import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical308
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical309
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical312
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical313
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical314
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical315

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal448 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def boundaryMatrix448 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def boundaryRow448 : Integer.Sparse (Fin 909) := [(0, -36), (1, 35), (2, 615), (3, 3440), (5, -860), (6, 100), (7, 560), (8, 800), (9, -20), (12, 1200), (13, 3360), (33, -960), (35, 640), (38, 720), (51, -1440), (52, 1840), (54, -1200), (59, -1440), (69, 80), (71, 160), (82, 160), (102, 1440), (126, -480), (128, 400), (199, -480), (237, -480), (259, -480), (539, 1440), (540, 720), (721, -480), (723, -240), (739, 1440)]

theorem boundarySound448 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow448 (momentVector H) = 0 := by
  have hshape : boundaryMatrix448 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix448 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix448 (0 : Fin 6)) =
      Sparse.eval value1644 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix448 (0 : Fin 6) = raw9723 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9723 hH).trans (sound1644 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix448 (1 : Fin 6)) =
      Sparse.eval value3140 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix448 (1 : Fin 6) = raw9870 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9870 hH).trans (sound3140 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix448 (2 : Fin 6)) =
      Sparse.eval value3147 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix448 (2 : Fin 6) = raw9895 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9895 hH).trans (sound3147 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix448 (3 : Fin 6)) =
      Sparse.eval value3147 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix448 (3 : Fin 6) = raw9898 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9898 hH).trans (sound3147 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix448 (4 : Fin 6)) =
      Sparse.eval value3123 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix448 (4 : Fin 6) = raw9899 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9899 hH).trans (sound3123 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix448 (5 : Fin 6)) =
      Sparse.eval value2974 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix448 (5 : Fin 6) = raw9900 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9900 hH).trans (sound2974 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix448 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix448 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix448 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix448 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix448 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix448 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow448, value1644, value2974, value3123, value3140, value3147, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal454 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -2, 3]]

def boundaryMatrix454 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -2, 3]]

def boundaryRow454 : Integer.Sparse (Fin 909) := [(0, -18), (1, -455), (2, 160), (3, 7200), (4, 1520), (5, -260), (6, 45), (11, 80), (12, 1280), (13, 3680), (26, 3120), (34, 2400), (35, 1920), (41, 720), (52, 880), (55, -480), (56, -720), (60, 720), (82, 80), (128, 160), (139, 1440), (190, 1440), (204, 1440), (238, -480), (324, 720), (398, 1440)]

theorem boundarySound454 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow454 (momentVector H) = 0 := by
  have hshape : boundaryMatrix454 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix454 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix454 (0 : Fin 6)) =
      Sparse.eval value3364 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix454 (0 : Fin 6) = raw10055 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10055 hH).trans (sound3364 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix454 (1 : Fin 6)) =
      Sparse.eval value3364 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix454 (1 : Fin 6) = raw10063 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10063 hH).trans (sound3364 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix454 (2 : Fin 6)) =
      Sparse.eval value3409 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix454 (2 : Fin 6) = raw10069 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10069 hH).trans (sound3409 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix454 (3 : Fin 6)) =
      Sparse.eval value3362 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix454 (3 : Fin 6) = raw10073 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10073 hH).trans (sound3362 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix454 (4 : Fin 6)) =
      Sparse.eval value2997 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix454 (4 : Fin 6) = raw10080 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10080 hH).trans (sound2997 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix454 (5 : Fin 6)) =
      Sparse.eval value3408 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix454 (5 : Fin 6) = raw10081 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10081 hH).trans (sound3408 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix454 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix454 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix454 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix454 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix454 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix454 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow454, value2997, value3362, value3364, value3408, value3409, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal455 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3]]

def boundaryMatrix455 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3]]

def boundaryRow455 : Integer.Sparse (Fin 909) := [(0, -38), (1, -205), (2, 240), (3, 5840), (4, 160), (5, -560), (6, 75), (7, 640), (8, 160), (9, -20), (12, 1360), (13, 4160), (23, -240), (26, 2240), (27, 180), (34, 1920), (35, 2320), (38, 720), (51, -1440), (52, 1280), (54, -480), (55, -1200), (60, 560), (64, -1440), (68, 120), (70, 80), (71, 80), (82, 320), (125, -480), (128, 400), (138, 1440), (139, 1440), (146, 720), (197, -720), (236, -240), (238, -960), (260, -480), (309, -480), (323, 720), (400, 1440), (728, -240), (810, 1440)]

theorem boundarySound455 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow455 (momentVector H) = 0 := by
  have hshape : boundaryMatrix455 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix455 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix455 (0 : Fin 6)) =
      Sparse.eval value3130 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix455 (0 : Fin 6) = raw10052 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10052 hH).trans (sound3130 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix455 (1 : Fin 6)) =
      Sparse.eval value3130 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix455 (1 : Fin 6) = raw10062 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10062 hH).trans (sound3130 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix455 (2 : Fin 6)) =
      Sparse.eval value3219 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix455 (2 : Fin 6) = raw10068 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10068 hH).trans (sound3219 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix455 (3 : Fin 6)) =
      Sparse.eval value3128 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix455 (3 : Fin 6) = raw10072 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10072 hH).trans (sound3128 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix455 (4 : Fin 6)) =
      Sparse.eval value2966 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix455 (4 : Fin 6) = raw10078 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10078 hH).trans (sound2966 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix455 (5 : Fin 6)) =
      Sparse.eval value3218 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix455 (5 : Fin 6) = raw10079 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10079 hH).trans (sound3218 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix455 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix455 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix455 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix455 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix455 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix455 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow455, value2966, value3128, value3130, value3218, value3219, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal460 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def boundaryMatrix460 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def boundaryRow460 : Integer.Sparse (Fin 909) := [(0, -3), (1, -280), (2, 45), (3, 3440), (4, 1000), (5, -210), (6, 30), (7, 280), (8, 120), (11, 160), (12, 80), (13, 800), (26, 2200), (34, 960), (35, 1240), (51, -120), (52, 200), (53, 360), (55, -360), (56, -480), (64, -720), (67, 360), (107, 360), (139, 720), (190, 720), (228, -120), (238, -480), (453, 720), (546, 360), (702, 360), (870, 360)]

theorem boundarySound460 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow460 (momentVector H) = 0 := by
  have hshape : boundaryMatrix460 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix460 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix460 (0 : Fin 6)) =
      Sparse.eval value3361 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix460 (0 : Fin 6) = raw9997 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9997 hH).trans (sound3361 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix460 (1 : Fin 6)) =
      Sparse.eval value3362 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix460 (1 : Fin 6) = raw10041 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10041 hH).trans (sound3362 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix460 (2 : Fin 6)) =
      Sparse.eval value3363 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix460 (2 : Fin 6) = raw10044 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10044 hH).trans (sound3363 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix460 (3 : Fin 6)) =
      Sparse.eval value3364 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix460 (3 : Fin 6) = raw10047 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10047 hH).trans (sound3364 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix460 (4 : Fin 6)) =
      Sparse.eval value3344 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix460 (4 : Fin 6) = raw10053 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10053 hH).trans (sound3344 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix460 (5 : Fin 6)) =
      Sparse.eval value3203 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix460 (5 : Fin 6) = raw10054 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10054 hH).trans (sound3203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix460 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix460 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix460 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix460 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix460 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix460 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow460, value3203, value3344, value3361, value3362, value3363, value3364, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal461 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

def boundaryMatrix461 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

def boundaryRow461 : Integer.Sparse (Fin 909) := [(0, -22), (1, -190), (2, 355), (3, 5680), (4, 800), (5, -620), (6, 95), (7, 1280), (8, 240), (9, -40), (11, 80), (12, 480), (13, 2400), (24, -240), (26, 3040), (27, 120), (31, -240), (33, -480), (34, 1520), (35, 2400), (37, 720), (51, -1440), (52, 1120), (55, -960), (64, -2400), (67, 560), (68, 120), (69, 160), (70, 240), (125, -1200), (126, -240), (138, 1440), (139, 1440), (146, 720), (197, -480), (204, 720), (237, -240), (238, -1200), (307, -480), (309, -240), (472, 1440), (503, 720), (543, 720), (546, 720), (727, -240), (736, 720)]

theorem boundarySound461 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow461 (momentVector H) = 0 := by
  have hshape : boundaryMatrix461 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix461 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix461 (0 : Fin 6)) =
      Sparse.eval value3127 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix461 (0 : Fin 6) = raw9996 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9996 hH).trans (sound3127 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix461 (1 : Fin 6)) =
      Sparse.eval value3128 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix461 (1 : Fin 6) = raw10040 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10040 hH).trans (sound3128 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix461 (2 : Fin 6)) =
      Sparse.eval value3129 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix461 (2 : Fin 6) = raw10043 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10043 hH).trans (sound3129 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix461 (3 : Fin 6)) =
      Sparse.eval value3130 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix461 (3 : Fin 6) = raw10046 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10046 hH).trans (sound3130 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix461 (4 : Fin 6)) =
      Sparse.eval value3116 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix461 (4 : Fin 6) = raw10050 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10050 hH).trans (sound3116 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix461 (5 : Fin 6)) =
      Sparse.eval value2969 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix461 (5 : Fin 6) = raw10051 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10051 hH).trans (sound2969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix461 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix461 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix461 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix461 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix461 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix461 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow461, value2969, value3116, value3127, value3128, value3129, value3130, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
