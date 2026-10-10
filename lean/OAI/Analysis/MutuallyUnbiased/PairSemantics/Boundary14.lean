import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical253
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical254
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical264
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical266
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical275
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical276
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical287
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical288
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical289
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical291
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical292
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical293
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical298
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical299

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal390 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix390 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryRow390 : Integer.Sparse (Fin 909) := [(0, -29), (1, 550), (2, 855), (3, 4480), (5, -1500), (6, 190), (7, 1680), (8, 960), (10, -720), (12, 1120), (13, 5120), (32, 320), (35, 3680), (52, 4160), (59, -1920), (60, 640), (72, 720), (73, 1440), (75, 1440), (81, -960), (82, 880), (128, 1680), (199, -720), (201, -2400), (267, -480), (284, 1440), (306, -720), (399, 2880), (499, 720), (502, 2880), (760, 1440)]

theorem boundarySound390 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow390 (momentVector H) = 0 := by
  have hshape : boundaryMatrix390 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix390 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix390 (0 : Fin 6)) =
      Sparse.eval value3150 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix390 (0 : Fin 6) = raw8103 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8103 hH).trans (sound3150 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix390 (1 : Fin 6)) =
      Sparse.eval value3412 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix390 (1 : Fin 6) = raw8467 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8467 hH).trans (sound3412 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix390 (2 : Fin 6)) =
      Sparse.eval value3164 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix390 (2 : Fin 6) = raw8514 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8514 hH).trans (sound3164 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix390 (3 : Fin 6)) =
      Sparse.eval value3164 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix390 (3 : Fin 6) = raw8515 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8515 hH).trans (sound3164 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix390 (4 : Fin 6)) =
      Sparse.eval value2956 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix390 (4 : Fin 6) = raw8516 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8516 hH).trans (sound2956 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix390 (5 : Fin 6)) =
      Sparse.eval value3427 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix390 (5 : Fin 6) = raw8517 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8517 hH).trans (sound3427 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix390 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix390 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix390 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix390 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix390 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix390 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow390, value2956, value3150, value3164, value3412, value3427, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal393 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def boundaryMatrix393 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def boundaryRow393 : Integer.Sparse (Fin 909) := [(0, -38), (1, -325), (2, 555), (3, 5040), (5, -820), (6, 30), (7, 2880), (8, 1440), (9, -20), (10, -2160), (12, 2720), (13, 4000), (23, -1440), (27, 360), (35, 1760), (38, 2160), (51, -4320), (54, -4320), (55, -720), (59, -3600), (68, 60), (69, 240), (70, 160), (72, 4320), (74, 4320), (82, 240), (124, -720), (196, -480), (199, -2400), (259, -1440), (282, 2160), (308, -720), (321, 2160), (505, 1440), (723, -720), (727, -240)]

theorem boundarySound393 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow393 (momentVector H) = 0 := by
  have hshape : boundaryMatrix393 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix393 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix393 (0 : Fin 6)) =
      Sparse.eval value3117 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix393 (0 : Fin 6) = raw8127 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8127 hH).trans (sound3117 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix393 (1 : Fin 6)) =
      Sparse.eval value3119 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix393 (1 : Fin 6) = raw8823 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8823 hH).trans (sound3119 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix393 (2 : Fin 6)) =
      Sparse.eval value3119 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix393 (2 : Fin 6) = raw8832 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8832 hH).trans (sound3119 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix393 (3 : Fin 6)) =
      Sparse.eval value3119 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix393 (3 : Fin 6) = raw8837 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8837 hH).trans (sound3119 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix393 (4 : Fin 6)) =
      Sparse.eval value3459 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix393 (4 : Fin 6) = raw8839 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8839 hH).trans (sound3459 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix393 (5 : Fin 6)) =
      Sparse.eval value3240 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix393 (5 : Fin 6) = raw8840 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8840 hH).trans (sound3240 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix393 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix393 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix393 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix393 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix393 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix393 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow393, value3117, value3119, value3240, value3459, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal394 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def boundaryMatrix394 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def boundaryRow394 : Integer.Sparse (Fin 909) := [(0, -14), (1, -100), (2, 255), (3, 3440), (4, 400), (5, -660), (6, 45), (7, 3040), (8, 640), (10, -240), (12, 640), (13, 960), (24, -240), (26, 960), (27, 60), (34, 160), (35, 3840), (37, 1440), (51, -480), (52, 1520), (55, -480), (59, -480), (60, 320), (67, 160), (73, 720), (81, -480), (83, 1440), (84, 3600), (228, -1200), (273, -480), (311, 1440), (317, 1440)]

theorem boundarySound394 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow394 (momentVector H) = 0 := by
  have hshape : boundaryMatrix394 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix394 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix394 (0 : Fin 6)) =
      Sparse.eval value2903 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix394 (0 : Fin 6) = raw8128 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8128 hH).trans (sound2903 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix394 (1 : Fin 6)) =
      Sparse.eval value2909 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix394 (1 : Fin 6) = raw8824 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8824 hH).trans (sound2909 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix394 (2 : Fin 6)) =
      Sparse.eval value2909 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix394 (2 : Fin 6) = raw8833 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8833 hH).trans (sound2909 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix394 (3 : Fin 6)) =
      Sparse.eval value3333 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix394 (3 : Fin 6) = raw8838 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8838 hH).trans (sound3333 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix394 (4 : Fin 6)) =
      Sparse.eval value2900 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix394 (4 : Fin 6) = raw8841 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8841 hH).trans (sound2900 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix394 (5 : Fin 6)) =
      Sparse.eval value3431 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix394 (5 : Fin 6) = raw8843 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8843 hH).trans (sound3431 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix394 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix394 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix394 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix394 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix394 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix394 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow394, value2900, value2903, value2909, value3333, value3431, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal395 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def boundaryMatrix395 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def boundaryRow395 : Integer.Sparse (Fin 909) := [(0, -3), (1, -31), (2, 91), (3, 656), (4, 48), (5, -164), (6, 9), (7, 592), (8, 256), (9, -8), (10, -192), (12, 80), (13, 64), (24, -192), (26, 96), (27, 48), (35, 512), (37, 288), (51, -288), (52, 144), (55, -96), (59, -240), (67, 32), (68, 12), (69, 128), (70, 96), (73, 576), (81, -96), (84, 144), (124, -48), (126, -96), (197, -96), (228, -48), (259, -96), (308, -96), (321, 144), (322, 288), (501, 288), (503, 288), (727, -48)]

theorem boundarySound395 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow395 (momentVector H) = 0 := by
  have hshape : boundaryMatrix395 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix395 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix395 (0 : Fin 6)) =
      Sparse.eval value3109 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix395 (0 : Fin 6) = raw8129 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8129 hH).trans (sound3109 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix395 (1 : Fin 6)) =
      Sparse.eval value3110 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix395 (1 : Fin 6) = raw8825 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8825 hH).trans (sound3110 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix395 (2 : Fin 6)) =
      Sparse.eval value3110 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix395 (2 : Fin 6) = raw8834 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8834 hH).trans (sound3110 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix395 (3 : Fin 6)) =
      Sparse.eval value3459 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix395 (3 : Fin 6) = raw8839 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8839 hH).trans (sound3459 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix395 (4 : Fin 6)) =
      Sparse.eval value3454 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix395 (4 : Fin 6) = raw8842 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8842 hH).trans (sound3454 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix395 (5 : Fin 6)) =
      Sparse.eval value3229 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix395 (5 : Fin 6) = raw8844 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8844 hH).trans (sound3229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix395 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix395 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix395 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix395 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix395 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix395 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow395, value3109, value3110, value3229, value3454, value3459, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal396 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def boundaryMatrix396 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def boundaryRow396 : Integer.Sparse (Fin 909) := [(0, -12), (1, -195), (2, 775), (3, 6320), (4, 1840), (5, -1040), (6, 70), (7, 2800), (8, 1280), (10, -240), (11, 240), (12, 80), (13, 80), (24, -240), (26, 2880), (27, 60), (31, -240), (33, -960), (34, 160), (35, 3280), (37, 1440), (51, -480), (52, 1760), (55, -480), (59, -480), (67, 160), (73, 720), (81, -3840), (83, 2880), (84, 2880), (85, 4320), (228, -4080), (273, -480), (311, 720), (314, 1440), (317, 1440), (490, -720)]

theorem boundarySound396 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow396 (momentVector H) = 0 := by
  have hshape : boundaryMatrix396 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix396 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix396 (0 : Fin 6)) =
      Sparse.eval value2903 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix396 (0 : Fin 6) = raw8131 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8131 hH).trans (sound2903 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix396 (1 : Fin 6)) =
      Sparse.eval value2917 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix396 (1 : Fin 6) = raw8826 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8826 hH).trans (sound2917 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix396 (2 : Fin 6)) =
      Sparse.eval value2917 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix396 (2 : Fin 6) = raw8835 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8835 hH).trans (sound2917 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix396 (3 : Fin 6)) =
      Sparse.eval value2933 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix396 (3 : Fin 6) = raw8845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8845 hH).trans (sound2933 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix396 (4 : Fin 6)) =
      Sparse.eval value2905 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix396 (4 : Fin 6) = raw8847 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8847 hH).trans (sound2905 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix396 (5 : Fin 6)) =
      Sparse.eval value3372 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix396 (5 : Fin 6) = raw8849 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8849 hH).trans (sound3372 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix396 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix396 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix396 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix396 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix396 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix396 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow396, value2903, value2905, value2917, value2933, value3372, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal397 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def boundaryMatrix397 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def boundaryRow397 : Integer.Sparse (Fin 909) := [(0, -1), (1, -310), (2, 730), (3, 6400), (4, 2080), (5, -1120), (6, 105), (7, 3040), (8, 960), (11, 560), (26, 3520), (35, 4160), (52, 2240), (53, 1440), (67, 160), (81, -2880), (83, 1440), (84, 3600), (85, 4320), (228, -4800), (702, 1440), (709, 1440)]

theorem boundarySound397 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow397 (momentVector H) = 0 := by
  have hshape : boundaryMatrix397 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix397 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix397 (0 : Fin 6)) =
      Sparse.eval value3213 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix397 (0 : Fin 6) = raw8132 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8132 hH).trans (sound3213 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix397 (1 : Fin 6)) =
      Sparse.eval value3271 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix397 (1 : Fin 6) = raw8827 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8827 hH).trans (sound3271 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix397 (2 : Fin 6)) =
      Sparse.eval value3271 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix397 (2 : Fin 6) = raw8836 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8836 hH).trans (sound3271 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix397 (3 : Fin 6)) =
      Sparse.eval value3277 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix397 (3 : Fin 6) = raw8846 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8846 hH).trans (sound3277 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix397 (4 : Fin 6)) =
      Sparse.eval value3349 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix397 (4 : Fin 6) = raw8848 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8848 hH).trans (sound3349 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix397 (5 : Fin 6)) =
      Sparse.eval value3452 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix397 (5 : Fin 6) = raw8850 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8850 hH).trans (sound3452 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix397 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix397 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix397 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix397 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix397 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix397 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow397, value3213, value3271, value3277, value3349, value3452, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal398 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def boundaryMatrix398 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def boundaryRow398 : Integer.Sparse (Fin 909) := [(0, -14), (1, -15), (2, 45), (3, 2320), (5, -440), (6, 70), (7, 1680), (8, 640), (9, -60), (10, -480), (23, -480), (25, -240), (26, 640), (27, 120), (35, 2480), (36, 720), (52, 480), (54, -1200), (55, -240), (64, -480), (67, 400), (68, 60), (69, 800), (70, 400), (72, 1440), (83, 1440), (125, -720), (126, -480), (199, -480), (228, -960), (260, -480), (271, -480), (287, 720), (308, -240), (316, 1440), (425, 720), (492, -240), (498, 720), (501, 1440), (727, -240)]

theorem boundarySound398 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow398 (momentVector H) = 0 := by
  have hshape : boundaryMatrix398 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix398 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix398 (0 : Fin 6)) =
      Sparse.eval value3101 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix398 (0 : Fin 6) = raw8135 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8135 hH).trans (sound3101 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix398 (1 : Fin 6)) =
      Sparse.eval value3104 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix398 (1 : Fin 6) = raw8828 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8828 hH).trans (sound3104 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix398 (2 : Fin 6)) =
      Sparse.eval value3454 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix398 (2 : Fin 6) = raw8842 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8842 hH).trans (sound3454 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix398 (3 : Fin 6)) =
      Sparse.eval value3454 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix398 (3 : Fin 6) = raw8851 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8851 hH).trans (sound3454 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix398 (4 : Fin 6)) =
      Sparse.eval value2960 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix398 (4 : Fin 6) = raw8852 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8852 hH).trans (sound2960 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix398 (5 : Fin 6)) =
      Sparse.eval value3171 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix398 (5 : Fin 6) = raw8853 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8853 hH).trans (sound3171 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix398 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix398 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix398 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix398 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix398 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix398 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow398, value2960, value3101, value3104, value3171, value3454, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal399 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def boundaryMatrix399 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def boundaryRow399 : Integer.Sparse (Fin 909) := [(0, -3), (1, 15), (2, 108), (3, 768), (4, 144), (5, -196), (6, 20), (7, 480), (8, 176), (11, 16), (12, 32), (13, 112), (26, 272), (34, 32), (35, 768), (37, 144), (52, 480), (56, -48), (59, -48), (60, 32), (67, 64), (73, 288), (81, -384), (83, 144), (84, 432), (128, 16), (201, -96), (228, -288), (275, -96), (317, 288), (428, 144), (460, 144), (517, 144), (709, 144)]

theorem boundarySound399 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow399 (momentVector H) = 0 := by
  have hshape : boundaryMatrix399 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix399 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix399 (0 : Fin 6)) =
      Sparse.eval value3151 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix399 (0 : Fin 6) = raw8138 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8138 hH).trans (sound3151 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix399 (1 : Fin 6)) =
      Sparse.eval value3158 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix399 (1 : Fin 6) = raw8829 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8829 hH).trans (sound3158 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix399 (2 : Fin 6)) =
      Sparse.eval value3349 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix399 (2 : Fin 6) = raw8848 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8848 hH).trans (sound3349 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix399 (3 : Fin 6)) =
      Sparse.eval value3172 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix399 (3 : Fin 6) = raw8854 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8854 hH).trans (sound3172 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix399 (4 : Fin 6)) =
      Sparse.eval value2961 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix399 (4 : Fin 6) = raw8855 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8855 hH).trans (sound2961 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix399 (5 : Fin 6)) =
      Sparse.eval value3438 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix399 (5 : Fin 6) = raw8856 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8856 hH).trans (sound3438 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix399 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix399 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix399 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix399 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix399 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix399 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow399, value2961, value3151, value3158, value3172, value3349, value3438, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal400 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def boundaryMatrix400 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def boundaryRow400 : Integer.Sparse (Fin 909) := [(0, -33), (1, 235), (2, 950), (3, 4480), (4, 160), (5, -1600), (6, 100), (7, 3680), (8, 2240), (10, -2400), (12, 1360), (13, 2560), (26, 160), (33, -480), (34, 160), (35, 3440), (38, 720), (52, 2240), (54, -240), (59, -3840), (60, 160), (72, 1440), (73, 2880), (74, 1440), (75, 2880), (81, -1440), (82, 320), (84, 1440), (128, 400), (199, -720), (201, -960), (228, -480), (271, -480), (307, -720), (318, 1440), (426, 720), (428, 1440), (499, 720)]

theorem boundarySound400 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow400 (momentVector H) = 0 := by
  have hshape : boundaryMatrix400 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix400 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix400 (0 : Fin 6)) =
      Sparse.eval value3102 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix400 (0 : Fin 6) = raw8140 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8140 hH).trans (sound3102 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix400 (1 : Fin 6)) =
      Sparse.eval value3108 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix400 (1 : Fin 6) = raw8830 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8830 hH).trans (sound3108 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix400 (2 : Fin 6)) =
      Sparse.eval value3115 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix400 (2 : Fin 6) = raw8858 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8858 hH).trans (sound3115 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix400 (3 : Fin 6)) =
      Sparse.eval value3115 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix400 (3 : Fin 6) = raw8859 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8859 hH).trans (sound3115 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix400 (4 : Fin 6)) =
      Sparse.eval value2963 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix400 (4 : Fin 6) = raw8860 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8860 hH).trans (sound2963 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix400 (5 : Fin 6)) =
      Sparse.eval value3416 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix400 (5 : Fin 6) = raw8861 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8861 hH).trans (sound3416 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix400 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix400 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix400 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix400 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix400 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix400 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow400, value2963, value3102, value3108, value3115, value3416, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal401 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def boundaryMatrix401 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def boundaryRow401 : Integer.Sparse (Fin 909) := [(0, -29), (1, -45), (2, 1290), (3, 6720), (4, 960), (5, -1080), (6, 60), (7, 1680), (8, 1440), (10, -720), (12, 2160), (13, 4400), (31, -720), (33, -1440), (35, 1680), (42, 4320), (51, -2880), (52, 3120), (59, -2880), (60, 480), (81, -1440), (82, 240), (86, 4320), (128, 960), (311, 2160), (326, 4320), (328, 4320), (490, -720)]

theorem boundarySound401 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow401 (momentVector H) = 0 := by
  have hshape : boundaryMatrix401 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix401 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix401 (0 : Fin 6)) =
      Sparse.eval value2930 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix401 (0 : Fin 6) = raw7193 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7193 hH).trans (sound2930 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix401 (1 : Fin 6)) =
      Sparse.eval value2930 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix401 (1 : Fin 6) = raw9178 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9178 hH).trans (sound2930 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix401 (2 : Fin 6)) =
      Sparse.eval value2930 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix401 (2 : Fin 6) = raw9242 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9242 hH).trans (sound2930 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix401 (3 : Fin 6)) =
      Sparse.eval value3331 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix401 (3 : Fin 6) = raw9263 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9263 hH).trans (sound3331 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix401 (4 : Fin 6)) =
      Sparse.eval value2924 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix401 (4 : Fin 6) = raw9271 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9271 hH).trans (sound2924 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix401 (5 : Fin 6)) =
      Sparse.eval value3396 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix401 (5 : Fin 6) = raw9277 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9277 hH).trans (sound3396 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix401 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix401 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix401 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix401 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix401 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix401 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow401, value2924, value2930, value3331, value3396, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal402 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def boundaryMatrix402 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def boundaryRow402 : Integer.Sparse (Fin 909) := [(0, 3), (1, -230), (2, 1095), (3, 6480), (4, 1520), (5, -1720), (6, 150), (7, 3040), (8, 1760), (11, 240), (26, 2560), (35, 4000), (52, 2640), (57, 1440), (67, 800), (81, -3360), (86, 2880), (228, -720), (460, 1440), (855, 4320)]

theorem boundarySound402 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow402 (momentVector H) = 0 := by
  have hshape : boundaryMatrix402 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix402 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix402 (0 : Fin 6)) =
      Sparse.eval value3342 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix402 (0 : Fin 6) = raw7197 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7197 hH).trans (sound3342 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix402 (1 : Fin 6)) =
      Sparse.eval value3342 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix402 (1 : Fin 6) = raw9181 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9181 hH).trans (sound3342 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix402 (2 : Fin 6)) =
      Sparse.eval value3345 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix402 (2 : Fin 6) = raw9247 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9247 hH).trans (sound3345 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix402 (3 : Fin 6)) =
      Sparse.eval value3347 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix402 (3 : Fin 6) = raw9313 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9313 hH).trans (sound3347 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix402 (4 : Fin 6)) =
      Sparse.eval value3052 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix402 (4 : Fin 6) = raw9320 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9320 hH).trans (sound3052 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix402 (5 : Fin 6)) =
      Sparse.eval value3407 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix402 (5 : Fin 6) = raw9325 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9325 hH).trans (sound3407 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix402 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix402 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix402 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix402 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix402 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix402 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow402, value3052, value3342, value3345, value3347, value3407, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal403 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix403 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def boundaryRow403 : Integer.Sparse (Fin 909) := [(0, -16), (1, 140), (2, 1155), (3, 4000), (4, 880), (5, -1820), (6, 95), (7, 3760), (8, 3040), (12, 80), (13, 160), (26, 1120), (31, -960), (33, -960), (35, 2480), (42, 1440), (51, -960), (52, 1120), (56, -240), (59, -960), (67, 480), (76, 1440), (81, -2400), (86, 1440), (97, 720), (107, 1440), (201, -240), (238, -720), (307, -720), (326, 2880), (425, 720), (428, 1440), (506, 1440)]

theorem boundarySound403 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow403 (momentVector H) = 0 := by
  have hshape : boundaryMatrix403 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix403 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix403 (0 : Fin 6)) =
      Sparse.eval value3112 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix403 (0 : Fin 6) = raw7204 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7204 hH).trans (sound3112 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix403 (1 : Fin 6)) =
      Sparse.eval value3112 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix403 (1 : Fin 6) = raw9185 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9185 hH).trans (sound3112 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix403 (2 : Fin 6)) =
      Sparse.eval value3401 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix403 (2 : Fin 6) = raw9256 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9256 hH).trans (sound3401 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix403 (3 : Fin 6)) =
      Sparse.eval value3406 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix403 (3 : Fin 6) = raw9359 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9359 hH).trans (sound3406 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix403 (4 : Fin 6)) =
      Sparse.eval value3054 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix403 (4 : Fin 6) = raw9378 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9378 hH).trans (sound3054 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix403 (5 : Fin 6)) =
      Sparse.eval value3230 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix403 (5 : Fin 6) = raw9382 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9382 hH).trans (sound3230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix403 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix403 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix403 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix403 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix403 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix403 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow403, value3054, value3112, value3230, value3401, value3406, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal404 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def boundaryMatrix404 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def boundaryRow404 : Integer.Sparse (Fin 909) := [(0, -1), (1, 64), (2, 143), (3, 304), (4, 32), (5, -412), (6, 60), (7, 48), (8, 256), (9, -4), (11, 32), (12, 16), (25, -96), (26, 64), (31, -192), (33, -192), (35, 288), (39, 288), (52, 608), (54, -96), (69, 16), (71, 64), (87, 144), (123, -192), (226, -48), (228, -96), (237, -144), (239, 288), (306, -144), (315, 576), (498, 144), (507, 288), (721, -192), (723, -48), (760, 288), (764, 288)]

theorem boundarySound404 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow404 (momentVector H) = 0 := by
  have hshape : boundaryMatrix404 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix404 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix404 (0 : Fin 6)) =
      Sparse.eval value3411 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix404 (0 : Fin 6) = raw7203 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7203 hH).trans (sound3411 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix404 (1 : Fin 6)) =
      Sparse.eval value3411 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix404 (1 : Fin 6) = raw9184 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9184 hH).trans (sound3411 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix404 (2 : Fin 6)) =
      Sparse.eval value3464 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix404 (2 : Fin 6) = raw9255 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9255 hH).trans (sound3464 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix404 (3 : Fin 6)) =
      Sparse.eval value3464 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix404 (3 : Fin 6) = raw9358 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9358 hH).trans (sound3464 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix404 (4 : Fin 6)) =
      Sparse.eval value3256 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix404 (4 : Fin 6) = raw9369 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9369 hH).trans (sound3256 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix404 (5 : Fin 6)) =
      Sparse.eval value3461 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix404 (5 : Fin 6) = raw9373 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9373 hH).trans (sound3461 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix404 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix404 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix404 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix404 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix404 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix404 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow404, value3256, value3411, value3461, value3464, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal405 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def boundaryMatrix405 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def boundaryRow405 : Integer.Sparse (Fin 909) := [(0, -27), (1, 505), (2, 1080), (3, 3840), (5, -2140), (6, 250), (7, 2160), (8, 1920), (9, -20), (12, 560), (13, 2640), (35, 3680), (51, -480), (52, 4080), (54, -240), (59, -1200), (60, 720), (69, 160), (71, 560), (82, 400), (86, 1440), (128, 800), (199, -240), (201, -960), (260, -480), (262, -480), (289, 720), (309, -720), (327, 1440), (328, 1440), (392, 720), (492, -240)]

theorem boundarySound405 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow405 (momentVector H) = 0 := by
  have hshape : boundaryMatrix405 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix405 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix405 (0 : Fin 6)) =
      Sparse.eval value3376 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix405 (0 : Fin 6) = raw7234 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7234 hH).trans (sound3376 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix405 (1 : Fin 6)) =
      Sparse.eval value3378 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix405 (1 : Fin 6) = raw9197 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9197 hH).trans (sound3378 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix405 (2 : Fin 6)) =
      Sparse.eval value3378 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix405 (2 : Fin 6) = raw9562 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9562 hH).trans (sound3378 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix405 (3 : Fin 6)) =
      Sparse.eval value3387 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix405 (3 : Fin 6) = raw9567 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9567 hH).trans (sound3387 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix405 (4 : Fin 6)) =
      Sparse.eval value2988 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix405 (4 : Fin 6) = raw9569 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9569 hH).trans (sound2988 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix405 (5 : Fin 6)) =
      Sparse.eval value3395 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix405 (5 : Fin 6) = raw9571 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9571 hH).trans (sound3395 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix405 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix405 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix405 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix405 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix405 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix405 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow405, value2988, value3376, value3378, value3387, value3395, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal406 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix406 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def boundaryRow406 : Integer.Sparse (Fin 909) := [(0, -29), (1, 535), (2, 1010), (3, 3600), (4, 160), (5, -2000), (6, 240), (7, 1600), (8, 1600), (12, 560), (13, 2720), (26, 80), (35, 3120), (42, 720), (51, -480), (52, 4240), (56, -480), (59, -1920), (60, 800), (76, 720), (82, 240), (86, 720), (102, 720), (103, 720), (128, 880), (201, -960), (328, 1440), (392, 720), (399, 720), (506, 1440), (798, 720)]

theorem boundarySound406 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow406 (momentVector H) = 0 := by
  have hshape : boundaryMatrix406 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix406 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix406 (0 : Fin 6)) =
      Sparse.eval value3377 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix406 (0 : Fin 6) = raw7240 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7240 hH).trans (sound3377 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix406 (1 : Fin 6)) =
      Sparse.eval value3381 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix406 (1 : Fin 6) = raw9200 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9200 hH).trans (sound3381 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix406 (2 : Fin 6)) =
      Sparse.eval value3389 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix406 (2 : Fin 6) = raw9564 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9564 hH).trans (sound3389 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix406 (3 : Fin 6)) =
      Sparse.eval value3394 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix406 (3 : Fin 6) = raw9588 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9588 hH).trans (sound3394 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix406 (4 : Fin 6)) =
      Sparse.eval value2991 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix406 (4 : Fin 6) = raw9594 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9594 hH).trans (sound2991 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix406 (5 : Fin 6)) =
      Sparse.eval value3385 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix406 (5 : Fin 6) = raw9597 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9597 hH).trans (sound3385 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix406 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix406 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix406 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix406 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix406 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix406 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow406, value2991, value3377, value3381, value3385, value3389, value3394, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal407 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def boundaryMatrix407 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def boundaryRow407 : Integer.Sparse (Fin 909) := [(0, -21), (1, 275), (2, 450), (3, 1440), (4, 160), (5, -1240), (6, 200), (7, 640), (8, 1040), (9, -20), (11, 160), (12, 160), (13, 720), (25, -240), (26, 320), (35, 1360), (39, 720), (51, -480), (52, 2000), (54, -480), (56, -480), (59, -480), (69, 80), (71, 320), (74, 720), (82, 160), (89, 720), (123, -480), (128, 400), (199, -240), (201, -480), (226, -240), (228, -480), (315, 1440), (507, 2160), (540, 720), (721, -480), (723, -240), (764, 720)]

theorem boundarySound407 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow407 (momentVector H) = 0 := by
  have hshape : boundaryMatrix407 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix407 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix407 (0 : Fin 6)) =
      Sparse.eval value3410 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix407 (0 : Fin 6) = raw7239 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7239 hH).trans (sound3410 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix407 (1 : Fin 6)) =
      Sparse.eval value3411 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix407 (1 : Fin 6) = raw9199 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9199 hH).trans (sound3411 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix407 (2 : Fin 6)) =
      Sparse.eval value3420 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix407 (2 : Fin 6) = raw9563 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9563 hH).trans (sound3420 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix407 (3 : Fin 6)) =
      Sparse.eval value3420 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix407 (3 : Fin 6) = raw9587 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9587 hH).trans (sound3420 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix407 (4 : Fin 6)) =
      Sparse.eval value3133 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix407 (4 : Fin 6) = raw9590 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9590 hH).trans (sound3133 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix407 (5 : Fin 6)) =
      Sparse.eval value3418 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix407 (5 : Fin 6) = raw9593 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9593 hH).trans (sound3418 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix407 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix407 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix407 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix407 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix407 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix407 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow407, value3133, value3410, value3411, value3418, value3420, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
