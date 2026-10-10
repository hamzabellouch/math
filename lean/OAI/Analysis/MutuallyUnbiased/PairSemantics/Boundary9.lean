import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical230
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical274
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical302
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical312
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical313

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal246 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def boundaryMatrix246 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def boundaryRow246 : Integer.Sparse (Fin 909) := [(0, 6), (1, -185), (2, -235), (3, -400), (4, -80), (5, 440), (6, -90), (8, -320), (9, 300), (11, -80), (13, -320), (26, -160), (35, -480), (52, -880), (56, 480), (58, -10), (69, -80), (71, -320), (82, -320), (128, -400), (201, 960), (228, 240), (278, -80), (310, -160), (492, 240), (495, -160), (796, 960), (818, 480)]

theorem boundarySound246 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow246 (momentVector H) = 0 := by
  have hshape : boundaryMatrix246 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix246 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix246 (0 : Fin 6)) =
      Sparse.eval value2650 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix246 (0 : Fin 6) = raw6826 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6826 hH).trans (sound2650 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix246 (1 : Fin 6)) =
      Sparse.eval value2650 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix246 (1 : Fin 6) = raw8534 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8534 hH).trans (sound2650 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix246 (2 : Fin 6)) =
      Sparse.eval value2673 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix246 (2 : Fin 6) = raw8598 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8598 hH).trans (sound2673 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix246 (3 : Fin 6)) =
      Sparse.eval value1150 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix246 (3 : Fin 6) = raw8650 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8650 hH).trans (sound1150 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix246 (4 : Fin 6)) =
      Sparse.eval value1879 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix246 (4 : Fin 6) = raw8655 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8655 hH).trans (sound1879 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix246 (5 : Fin 6)) =
      Sparse.eval value2382 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix246 (5 : Fin 6) = raw8658 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8658 hH).trans (sound2382 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix246 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix246 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix246 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix246 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix246 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix246 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow246, value1150, value1879, value2382, value2650, value2673, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal247 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def boundaryMatrix247 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def boundaryRow247 : Integer.Sparse (Fin 909) := [(0, -1), (1, -15), (2, -190), (3, -640), (4, -160), (5, 320), (6, -35), (7, -480), (8, -320), (9, 100), (26, -160), (27, -60), (35, -320), (51, 480), (52, -480), (58, -5), (68, -60), (69, -320), (71, -160), (124, 240), (126, 480), (308, 480), (310, -160), (493, 480), (495, -160)]

theorem boundarySound247 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow247 (momentVector H) = 0 := by
  have hshape : boundaryMatrix247 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix247 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix247 (0 : Fin 6)) =
      Sparse.eval value1870 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix247 (0 : Fin 6) = raw8198 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8198 hH).trans (sound1870 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix247 (1 : Fin 6)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix247 (1 : Fin 6) = raw8676 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8676 hH).trans (sound559 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix247 (2 : Fin 6)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix247 (2 : Fin 6) = raw8700 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8700 hH).trans (sound559 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix247 (3 : Fin 6)) =
      Sparse.eval value1882 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix247 (3 : Fin 6) = raw8716 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8716 hH).trans (sound1882 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix247 (4 : Fin 6)) =
      Sparse.eval value1537 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix247 (4 : Fin 6) = raw8721 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8721 hH).trans (sound1537 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix247 (5 : Fin 6)) =
      Sparse.eval value1883 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix247 (5 : Fin 6) = raw8722 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8722 hH).trans (sound1883 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix247 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix247 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix247 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix247 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix247 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix247 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow247, value1537, value1870, value1882, value1883, value559, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal248 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def boundaryMatrix248 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def boundaryRow248 : Integer.Sparse (Fin 909) := [(0, 1), (1, 60), (2, -15), (3, -1120), (4, -320), (5, 420), (6, -25), (9, 60), (11, -320), (26, -800), (27, -120), (35, -1120), (52, -320), (55, 240), (58, -5), (68, -120), (238, 960), (278, -80), (493, 480), (495, -160), (727, 240)]

theorem boundarySound248 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow248 (momentVector H) = 0 := by
  have hshape : boundaryMatrix248 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix248 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix248 (0 : Fin 6)) =
      Sparse.eval value2473 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix248 (0 : Fin 6) = raw8214 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8214 hH).trans (sound2473 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix248 (1 : Fin 6)) =
      Sparse.eval value876 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix248 (1 : Fin 6) = raw8691 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8691 hH).trans (sound876 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix248 (2 : Fin 6)) =
      Sparse.eval value2474 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix248 (2 : Fin 6) = raw8756 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8756 hH).trans (sound2474 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix248 (3 : Fin 6)) =
      Sparse.eval value2474 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix248 (3 : Fin 6) = raw8772 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8772 hH).trans (sound2474 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix248 (4 : Fin 6)) =
      Sparse.eval value2383 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix248 (4 : Fin 6) = raw8775 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8775 hH).trans (sound2383 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix248 (5 : Fin 6)) =
      Sparse.eval value2471 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix248 (5 : Fin 6) = raw8776 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8776 hH).trans (sound2471 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix248 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix248 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix248 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix248 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix248 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix248 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow248, value2383, value2471, value2473, value2474, value876, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal249 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def boundaryMatrix249 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def boundaryRow249 : Integer.Sparse (Fin 909) := [(0, 7), (1, -55), (2, -175), (3, -1040), (5, 460), (6, -60), (7, -400), (8, -160), (9, 80), (12, -320), (13, -1360), (35, -720), (51, 480), (52, -960), (54, 240), (58, -5), (68, -60), (69, -160), (70, -160), (71, -80), (82, -320), (125, 480), (126, 240), (128, -400), (278, -80), (309, 480), (310, -160), (492, 240), (494, 480), (495, -160)]

theorem boundarySound249 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow249 (momentVector H) = 0 := by
  have hshape : boundaryMatrix249 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix249 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix249 (0 : Fin 6)) =
      Sparse.eval value1872 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix249 (0 : Fin 6) = raw8207 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8207 hH).trans (sound1872 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix249 (1 : Fin 6)) =
      Sparse.eval value563 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix249 (1 : Fin 6) = raw8684 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8684 hH).trans (sound563 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix249 (2 : Fin 6)) =
      Sparse.eval value1886 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix249 (2 : Fin 6) = raw8737 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8737 hH).trans (sound1886 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix249 (3 : Fin 6)) =
      Sparse.eval value1887 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix249 (3 : Fin 6) = raw8747 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8747 hH).trans (sound1887 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix249 (4 : Fin 6)) =
      Sparse.eval value1540 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix249 (4 : Fin 6) = raw8754 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8754 hH).trans (sound1540 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix249 (5 : Fin 6)) =
      Sparse.eval value1885 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix249 (5 : Fin 6) = raw8755 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8755 hH).trans (sound1885 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix249 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix249 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix249 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix249 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix249 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix249 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow249, value1540, value1872, value1885, value1886, value1887, value563, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal250 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def boundaryMatrix250 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def boundaryRow250 : Integer.Sparse (Fin 909) := [(0, 1), (1, 64), (2, -38), (3, -640), (4, -192), (5, 24), (6, -3), (12, -192), (13, -256), (26, -192), (27, -36), (35, -192), (51, 576), (52, -192), (55, 576), (127, 144), (128, -48), (493, 576), (494, 384), (495, -64)]

theorem boundarySound250 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow250 (momentVector H) = 0 := by
  have hshape : boundaryMatrix250 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix250 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix250 (0 : Fin 6)) =
      Sparse.eval value1889 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix250 (0 : Fin 6) = raw6797 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6797 hH).trans (sound1889 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix250 (1 : Fin 6)) =
      Sparse.eval value1889 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix250 (1 : Fin 6) = raw8520 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8520 hH).trans (sound1889 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix250 (2 : Fin 6)) =
      Sparse.eval value1889 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix250 (2 : Fin 6) = raw8567 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8567 hH).trans (sound1889 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix250 (3 : Fin 6)) =
      Sparse.eval value1889 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix250 (3 : Fin 6) = raw8581 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8581 hH).trans (sound1889 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix250 (4 : Fin 6)) =
      Sparse.eval value1888 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix250 (4 : Fin 6) = raw8583 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8583 hH).trans (sound1888 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix250 (5 : Fin 6)) =
      Sparse.eval value2480 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix250 (5 : Fin 6) = raw8584 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8584 hH).trans (sound2480 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix250 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix250 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix250 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix250 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix250 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix250 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow250, value1888, value1889, value2480, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal251 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def boundaryMatrix251 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def boundaryRow251 : Integer.Sparse (Fin 909) := [(0, 3), (1, -45), (2, -200), (3, -400), (5, 700), (6, -60), (7, -80), (8, -480), (9, 160), (27, -180), (52, -480), (58, -10), (68, -180), (69, -80), (71, -400), (126, 240), (236, 480), (237, 480), (308, 240), (310, -80)]

theorem boundarySound251 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow251 (momentVector H) = 0 := by
  have hshape : boundaryMatrix251 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix251 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix251 (0 : Fin 6)) =
      Sparse.eval value2456 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix251 (0 : Fin 6) = raw6847 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6847 hH).trans (sound2456 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix251 (1 : Fin 6)) =
      Sparse.eval value2465 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix251 (1 : Fin 6) = raw8539 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8539 hH).trans (sound2465 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix251 (2 : Fin 6)) =
      Sparse.eval value2465 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix251 (2 : Fin 6) = raw8694 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8694 hH).trans (sound2465 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix251 (3 : Fin 6)) =
      Sparse.eval value2476 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix251 (3 : Fin 6) = raw8713 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8713 hH).trans (sound2476 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix251 (4 : Fin 6)) =
      Sparse.eval value1537 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix251 (4 : Fin 6) = raw8721 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8721 hH).trans (sound1537 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix251 (5 : Fin 6)) =
      Sparse.eval value2479 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix251 (5 : Fin 6) = raw8723 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8723 hH).trans (sound2479 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix251 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix251 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix251 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix251 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix251 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix251 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow251, value1537, value2456, value2465, value2476, value2479, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal252 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def boundaryMatrix252 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def boundaryRow252 : Integer.Sparse (Fin 909) := [(0, 8), (1, -40), (2, -40), (3, -560), (5, 420), (6, -25), (9, 60), (11, -160), (12, -80), (13, -720), (26, -320), (35, -880), (52, -560), (55, 240), (58, -5), (68, -120), (82, -160), (128, -160), (237, 480), (278, -80), (494, 480), (495, -160), (728, 240)]

theorem boundarySound252 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow252 (momentVector H) = 0 := by
  have hshape : boundaryMatrix252 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix252 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix252 (0 : Fin 6)) =
      Sparse.eval value2670 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix252 (0 : Fin 6) = raw6860 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6860 hH).trans (sound2670 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix252 (1 : Fin 6)) =
      Sparse.eval value2464 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix252 (1 : Fin 6) = raw8544 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8544 hH).trans (sound2464 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix252 (2 : Fin 6)) =
      Sparse.eval value883 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix252 (2 : Fin 6) = raw8704 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8704 hH).trans (sound883 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix252 (3 : Fin 6)) =
      Sparse.eval value883 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix252 (3 : Fin 6) = raw8771 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8771 hH).trans (sound883 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix252 (4 : Fin 6)) =
      Sparse.eval value1887 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix252 (4 : Fin 6) = raw8774 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8774 hH).trans (sound1887 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix252 (5 : Fin 6)) =
      Sparse.eval value2383 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix252 (5 : Fin 6) = raw8777 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8777 hH).trans (sound2383 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix252 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix252 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix252 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix252 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix252 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix252 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow252, value1887, value2383, value2464, value2670, value883, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal253 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def boundaryMatrix253 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def boundaryRow253 : Integer.Sparse (Fin 909) := [(0, 6), (1, -5), (2, -15), (3, -480), (4, -80), (5, 480), (6, -30), (7, -160), (8, -160), (9, 140), (11, -160), (13, -320), (26, -480), (35, -960), (52, -160), (56, 240), (58, -10), (68, -180), (70, -160), (71, -240), (82, -160), (197, 480), (236, 240), (238, 240), (278, -80), (309, 240), (310, -80), (796, 240)]

theorem boundarySound253 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow253 (momentVector H) = 0 := by
  have hshape : boundaryMatrix253 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix253 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix253 (0 : Fin 6)) =
      Sparse.eval value2457 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix253 (0 : Fin 6) = raw6857 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6857 hH).trans (sound2457 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix253 (1 : Fin 6)) =
      Sparse.eval value2468 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix253 (1 : Fin 6) = raw8541 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8541 hH).trans (sound2468 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix253 (2 : Fin 6)) =
      Sparse.eval value2477 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix253 (2 : Fin 6) = raw8696 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8696 hH).trans (sound2477 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix253 (3 : Fin 6)) =
      Sparse.eval value883 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix253 (3 : Fin 6) = raw8744 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8744 hH).trans (sound883 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix253 (4 : Fin 6)) =
      Sparse.eval value1540 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix253 (4 : Fin 6) = raw8754 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8754 hH).trans (sound1540 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix253 (5 : Fin 6)) =
      Sparse.eval value2474 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix253 (5 : Fin 6) = raw8756 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8756 hH).trans (sound2474 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix253 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix253 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix253 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix253 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix253 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix253 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow253, value1540, value2457, value2468, value2474, value2477, value883, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal261 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def boundaryMatrix261 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def boundaryRow261 : Integer.Sparse (Fin 909) := [(0, 1), (1, -33), (2, -51), (3, -48), (5, 148), (6, -15), (7, -144), (8, -192), (9, 36), (35, -80), (52, -96), (69, -288), (70, -112), (71, -432), (256, 144), (257, -32), (495, -48)]

theorem boundarySound261 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow261 (momentVector H) = 0 := by
  have hshape : boundaryMatrix261 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix261 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix261 (0 : Fin 6)) =
      Sparse.eval value1382 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix261 (0 : Fin 6) = raw3916 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3916 hH).trans (sound1382 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix261 (1 : Fin 6)) =
      Sparse.eval value1382 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix261 (1 : Fin 6) = raw7359 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7359 hH).trans (sound1382 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix261 (2 : Fin 6)) =
      Sparse.eval value1381 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix261 (2 : Fin 6) = raw7378 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7378 hH).trans (sound1381 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix261 (3 : Fin 6)) =
      Sparse.eval value1381 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix261 (3 : Fin 6) = raw7380 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7380 hH).trans (sound1381 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix261 (4 : Fin 6)) =
      Sparse.eval value1438 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix261 (4 : Fin 6) = raw7381 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7381 hH).trans (sound1438 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix261 (5 : Fin 6)) =
      Sparse.eval value2380 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix261 (5 : Fin 6) = raw7382 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7382 hH).trans (sound2380 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix261 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix261 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix261 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix261 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix261 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix261 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow261, value1381, value1382, value1438, value2380, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal262 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def boundaryMatrix262 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def boundaryRow262 : Integer.Sparse (Fin 909) := [(0, 2), (1, -15), (2, -10), (3, -280), (5, 170), (6, -25), (7, -360), (9, 50), (13, -120), (26, -120), (35, -560), (52, -240), (54, 360), (60, -80), (69, -360), (70, -320), (71, -240), (257, -80), (259, 360), (260, 240), (495, -40)]

theorem boundarySound262 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow262 (momentVector H) = 0 := by
  have hshape : boundaryMatrix262 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix262 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix262 (0 : Fin 6)) =
      Sparse.eval value739 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix262 (0 : Fin 6) = raw9694 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9694 hH).trans (sound739 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix262 (1 : Fin 6)) =
      Sparse.eval value739 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix262 (1 : Fin 6) = raw10004 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10004 hH).trans (sound739 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix262 (2 : Fin 6)) =
      Sparse.eval value739 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix262 (2 : Fin 6) = raw10012 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10012 hH).trans (sound739 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix262 (3 : Fin 6)) =
      Sparse.eval value1386 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix262 (3 : Fin 6) = raw10019 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10019 hH).trans (sound1386 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix262 (4 : Fin 6)) =
      Sparse.eval value1387 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix262 (4 : Fin 6) = raw10025 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10025 hH).trans (sound1387 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix262 (5 : Fin 6)) =
      Sparse.eval value1379 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix262 (5 : Fin 6) = raw10026 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10026 hH).trans (sound1379 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix262 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix262 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix262 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix262 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix262 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix262 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow262, value1379, value1386, value1387, value739, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal263 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def boundaryMatrix263 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def boundaryRow263 : Integer.Sparse (Fin 909) := [(0, 9), (1, -225), (2, -300), (3, -480), (4, -80), (5, 840), (6, -100), (7, -320), (8, -960), (9, 80), (13, -320), (26, -80), (35, -400), (51, 240), (52, -880), (56, 480), (59, 480), (69, -560), (70, -80), (71, -1200), (128, -160), (256, 240), (259, 240), (262, 960), (495, -160)]

theorem boundarySound263 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow263 (momentVector H) = 0 := by
  have hshape : boundaryMatrix263 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix263 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix263 (0 : Fin 6)) =
      Sparse.eval value737 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix263 (0 : Fin 6) = raw9697 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9697 hH).trans (sound737 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix263 (1 : Fin 6)) =
      Sparse.eval value737 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix263 (1 : Fin 6) = raw10007 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10007 hH).trans (sound737 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix263 (2 : Fin 6)) =
      Sparse.eval value1389 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix263 (2 : Fin 6) = raw10031 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10031 hH).trans (sound1389 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix263 (3 : Fin 6)) =
      Sparse.eval value1390 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix263 (3 : Fin 6) = raw10032 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10032 hH).trans (sound1390 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix263 (4 : Fin 6)) =
      Sparse.eval value2380 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix263 (4 : Fin 6) = raw10033 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10033 hH).trans (sound2380 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix263 (5 : Fin 6)) =
      Sparse.eval value1381 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix263 (5 : Fin 6) = raw10034 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10034 hH).trans (sound1381 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix263 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix263 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix263 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix263 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix263 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix263 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow263, value1381, value1389, value1390, value2380, value737, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal264 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def boundaryMatrix264 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def boundaryRow264 : Integer.Sparse (Fin 909) := [(0, 3), (1, -30), (2, -80), (3, -560), (4, -80), (5, 260), (6, -25), (7, -640), (8, -320), (9, 40), (26, -240), (35, -720), (52, -240), (67, -160), (69, -400), (70, -240), (71, -320), (81, 240), (256, 240), (257, -80), (495, -80)]

theorem boundarySound264 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow264 (momentVector H) = 0 := by
  have hshape : boundaryMatrix264 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix264 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix264 (0 : Fin 6)) =
      Sparse.eval value1528 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix264 (0 : Fin 6) = raw6809 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6809 hH).trans (sound1528 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix264 (1 : Fin 6)) =
      Sparse.eval value1528 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix264 (1 : Fin 6) = raw8528 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8528 hH).trans (sound1528 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix264 (2 : Fin 6)) =
      Sparse.eval value1529 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix264 (2 : Fin 6) = raw8575 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8575 hH).trans (sound1529 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix264 (3 : Fin 6)) =
      Sparse.eval value1536 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix264 (3 : Fin 6) = raw8615 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8615 hH).trans (sound1536 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix264 (4 : Fin 6)) =
      Sparse.eval value1399 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix264 (4 : Fin 6) = raw8630 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8630 hH).trans (sound1399 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix264 (5 : Fin 6)) =
      Sparse.eval value2128 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix264 (5 : Fin 6) = raw8633 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8633 hH).trans (sound2128 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix264 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix264 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix264 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix264 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix264 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix264 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow264, value1399, value1528, value1529, value1536, value2128, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal265 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def boundaryMatrix265 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def boundaryRow265 : Integer.Sparse (Fin 909) := [(1, -1), (2, 12), (6, 1), (9, 4), (13, -160), (32, -32), (35, -96), (60, -64), (63, 144), (70, -64), (196, 144), (257, -32), (264, 96)]

theorem boundarySound265 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow265 (momentVector H) = 0 := by
  have hshape : boundaryMatrix265 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix265 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix265 (0 : Fin 6)) =
      Sparse.eval value1398 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix265 (0 : Fin 6) = raw8175 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8175 hH).trans (sound1398 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix265 (1 : Fin 6)) =
      Sparse.eval value1398 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix265 (1 : Fin 6) = raw8551 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8551 hH).trans (sound1398 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix265 (2 : Fin 6)) =
      Sparse.eval value1287 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix265 (2 : Fin 6) = raw8603 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8603 hH).trans (sound1287 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix265 (3 : Fin 6)) =
      Sparse.eval value1287 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix265 (3 : Fin 6) = raw8617 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8617 hH).trans (sound1287 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix265 (4 : Fin 6)) =
      Sparse.eval value2787 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix265 (4 : Fin 6) = raw8621 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8621 hH).trans (sound2787 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix265 (5 : Fin 6)) =
      Sparse.eval value1421 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix265 (5 : Fin 6) = raw8622 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8622 hH).trans (sound1421 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix265 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix265 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix265 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix265 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix265 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix265 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow265, value1287, value1398, value1421, value2787, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal266 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def boundaryMatrix266 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def boundaryRow266 : Integer.Sparse (Fin 909) := [(0, 7), (1, 60), (2, 40), (3, -1280), (5, 140), (6, -35), (7, -480), (9, 20), (12, -240), (13, -640), (26, -800), (34, -480), (35, -1360), (55, 720), (60, -160), (67, -480), (70, -240), (71, -80), (197, 720), (257, -160), (268, 480)]

theorem boundarySound266 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow266 (momentVector H) = 0 := by
  have hshape : boundaryMatrix266 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix266 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix266 (0 : Fin 6)) =
      Sparse.eval value1414 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix266 (0 : Fin 6) = raw8179 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8179 hH).trans (sound1414 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix266 (1 : Fin 6)) =
      Sparse.eval value1414 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix266 (1 : Fin 6) = raw8556 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8556 hH).trans (sound1414 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix266 (2 : Fin 6)) =
      Sparse.eval value876 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix266 (2 : Fin 6) = raw8608 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8608 hH).trans (sound876 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix266 (3 : Fin 6)) =
      Sparse.eval value1422 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix266 (3 : Fin 6) = raw8631 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8631 hH).trans (sound1422 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix266 (4 : Fin 6)) =
      Sparse.eval value2461 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix266 (4 : Fin 6) = raw8637 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8637 hH).trans (sound2461 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix266 (5 : Fin 6)) =
      Sparse.eval value2793 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix266 (5 : Fin 6) = raw8638 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8638 hH).trans (sound2793 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix266 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix266 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix266 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix266 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix266 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix266 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow266, value1414, value1422, value2461, value2793, value876, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal267 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def boundaryMatrix267 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def boundaryRow267 : Integer.Sparse (Fin 909) := [(0, -2), (1, 315), (2, -60), (3, -4080), (4, -960), (5, 220), (6, -45), (7, -960), (9, 20), (13, -1200), (26, -2880), (34, -1280), (35, -2000), (52, -480), (55, 720), (64, 1440), (67, -960), (69, -80), (70, -240), (125, 720), (257, -160), (266, 480)]

theorem boundarySound267 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow267 (momentVector H) = 0 := by
  have hshape : boundaryMatrix267 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix267 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix267 (0 : Fin 6)) =
      Sparse.eval value1416 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix267 (0 : Fin 6) = raw8186 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8186 hH).trans (sound1416 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix267 (1 : Fin 6)) =
      Sparse.eval value1416 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix267 (1 : Fin 6) = raw8563 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8563 hH).trans (sound1416 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix267 (2 : Fin 6)) =
      Sparse.eval value1425 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix267 (2 : Fin 6) = raw8654 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8654 hH).trans (sound1425 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix267 (3 : Fin 6)) =
      Sparse.eval value1425 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix267 (3 : Fin 6) = raw8662 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8662 hH).trans (sound1425 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix267 (4 : Fin 6)) =
      Sparse.eval value1878 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix267 (4 : Fin 6) = raw8666 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8666 hH).trans (sound1878 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix267 (5 : Fin 6)) =
      Sparse.eval value2671 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix267 (5 : Fin 6) = raw8667 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8667 hH).trans (sound2671 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix267 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix267 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix267 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix267 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix267 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix267 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow267, value1416, value1425, value1878, value2671, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal268 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

def boundaryMatrix268 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

def boundaryRow268 : Integer.Sparse (Fin 909) := [(0, 3), (1, 20), (2, 35), (3, -480), (5, 200), (6, -40), (7, -480), (9, 80), (13, -160), (26, -480), (34, -160), (35, -960), (54, 480), (67, -320), (69, -160), (70, -320), (71, -160), (124, 240), (196, 240), (197, 480), (257, -160), (259, 480), (266, 480), (495, -160)]

theorem boundarySound268 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow268 (momentVector H) = 0 := by
  have hshape : boundaryMatrix268 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix268 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix268 (0 : Fin 6)) =
      Sparse.eval value1392 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix268 (0 : Fin 6) = raw8197 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8197 hH).trans (sound1392 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix268 (1 : Fin 6)) =
      Sparse.eval value864 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix268 (1 : Fin 6) = raw8675 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8675 hH).trans (sound864 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix268 (2 : Fin 6)) =
      Sparse.eval value864 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix268 (2 : Fin 6) = raw8699 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8699 hH).trans (sound864 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix268 (3 : Fin 6)) =
      Sparse.eval value1403 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix268 (3 : Fin 6) = raw8715 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8715 hH).trans (sound1403 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix268 (4 : Fin 6)) =
      Sparse.eval value1383 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix268 (4 : Fin 6) = raw8719 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8719 hH).trans (sound1383 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix268 (5 : Fin 6)) =
      Sparse.eval value2788 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix268 (5 : Fin 6) = raw8720 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8720 hH).trans (sound2788 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix268 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix268 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix268 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix268 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix268 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix268 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow268, value1383, value1392, value1403, value2788, value864, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
