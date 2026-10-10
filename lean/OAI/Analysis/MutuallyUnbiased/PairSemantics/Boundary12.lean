import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical287
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical289
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical291
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical293
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical294
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical295
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical297
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical298
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical299
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical300
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical301
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical302
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical304
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical305
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical306
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical309
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical310

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal343 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def boundaryMatrix343 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def boundaryRow343 : Integer.Sparse (Fin 909) := [(0, -12), (1, -405), (2, 300), (3, 3440), (4, 640), (5, -260), (6, 5), (7, 1200), (8, 80), (9, -20), (10, -480), (12, 1040), (13, 320), (23, -3600), (24, -3120), (26, 160), (27, 780), (35, 320), (47, 1440), (51, -480), (52, 160), (55, -3360), (68, 180), (69, 240), (70, 160), (79, 1440), (113, 720), (124, -240), (125, -2160), (126, -1440), (197, -480), (291, 720), (308, -240), (538, 1440), (640, 1440), (727, -240), (751, 720)]

theorem boundarySound343 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow343 (momentVector H) = 0 := by
  have hshape : boundaryMatrix343 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix343 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix343 (0 : Fin 6)) =
      Sparse.eval value3175 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix343 (0 : Fin 6) = raw9120 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9120 hH).trans (sound3175 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix343 (1 : Fin 6)) =
      Sparse.eval value1518 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix343 (1 : Fin 6) = raw9389 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9389 hH).trans (sound1518 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix343 (2 : Fin 6)) =
      Sparse.eval value3180 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix343 (2 : Fin 6) = raw9446 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9446 hH).trans (sound3180 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix343 (3 : Fin 6)) =
      Sparse.eval value3181 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix343 (3 : Fin 6) = raw9452 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9452 hH).trans (sound3181 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix343 (4 : Fin 6)) =
      Sparse.eval value3131 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix343 (4 : Fin 6) = raw9456 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9456 hH).trans (sound3131 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix343 (5 : Fin 6)) =
      Sparse.eval value3090 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix343 (5 : Fin 6) = raw9457 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9457 hH).trans (sound3090 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix343 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix343 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix343 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix343 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix343 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix343 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow343, value1518, value3090, value3131, value3175, value3180, value3181, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal345 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def boundaryMatrix345 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def boundaryRow345 : Integer.Sparse (Fin 909) := [(0, 29), (1, -515), (2, 480), (3, 1280), (4, 800), (5, -420), (6, 30), (7, 240), (8, 800), (9, -20), (12, 320), (23, -480), (24, -2880), (27, 1140), (30, -1680), (31, -960), (33, -960), (49, 1440), (51, -720), (52, 80), (55, -1920), (68, 180), (69, 80), (71, 320), (105, 720), (106, 1440), (124, -240), (126, -1680), (197, -960), (236, -1440), (237, -720), (290, 720), (299, 1440), (306, -480), (308, -240), (728, -240), (751, 720), (811, 1440), (812, 1440)]

theorem boundarySound345 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow345 (momentVector H) = 0 := by
  have hshape : boundaryMatrix345 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix345 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix345 (0 : Fin 6)) =
      Sparse.eval value3309 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix345 (0 : Fin 6) = raw9146 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9146 hH).trans (sound3309 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix345 (1 : Fin 6)) =
      Sparse.eval value1520 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix345 (1 : Fin 6) = raw9414 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9414 hH).trans (sound1520 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix345 (2 : Fin 6)) =
      Sparse.eval value3308 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix345 (2 : Fin 6) = raw9521 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9521 hH).trans (sound3308 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix345 (3 : Fin 6)) =
      Sparse.eval value3311 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix345 (3 : Fin 6) = raw9539 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9539 hH).trans (sound3311 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix345 (4 : Fin 6)) =
      Sparse.eval value3307 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix345 (4 : Fin 6) = raw9544 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9544 hH).trans (sound3307 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix345 (5 : Fin 6)) =
      Sparse.eval value3093 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix345 (5 : Fin 6) = raw9545 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9545 hH).trans (sound3093 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix345 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix345 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix345 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix345 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix345 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix345 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow345, value1520, value3093, value3307, value3308, value3309, value3311, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal346 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def boundaryMatrix346 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def boundaryRow346 : Integer.Sparse (Fin 909) := [(0, -1), (1, -80), (2, 555), (3, 2800), (4, 960), (5, -660), (6, 40), (7, 1040), (8, 1440), (9, -20), (26, 640), (31, -960), (35, 480), (46, 1440), (51, -3360), (52, 480), (56, -1680), (69, 240), (70, 160), (71, 320), (77, 1440), (97, 720), (107, 1440), (228, -480), (238, -720), (262, -960), (286, 720), (309, -720), (327, 1440), (735, 1440), (736, 1440), (796, -240)]

theorem boundarySound346 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow346 (momentVector H) = 0 := by
  have hshape : boundaryMatrix346 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix346 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix346 (0 : Fin 6)) =
      Sparse.eval value3228 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix346 (0 : Fin 6) = raw9142 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9142 hH).trans (sound3228 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix346 (1 : Fin 6)) =
      Sparse.eval value1513 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix346 (1 : Fin 6) = raw9410 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9410 hH).trans (sound1513 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix346 (2 : Fin 6)) =
      Sparse.eval value3227 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix346 (2 : Fin 6) = raw9517 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9517 hH).trans (sound3227 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix346 (3 : Fin 6)) =
      Sparse.eval value3231 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix346 (3 : Fin 6) = raw9530 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9530 hH).trans (sound3231 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix346 (4 : Fin 6)) =
      Sparse.eval value3226 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix346 (4 : Fin 6) = raw9536 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9536 hH).trans (sound3226 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix346 (5 : Fin 6)) =
      Sparse.eval value3035 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix346 (5 : Fin 6) = raw9537 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9537 hH).trans (sound3035 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix346 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix346 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix346 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix346 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix346 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix346 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow346, value1513, value3035, value3226, value3227, value3228, value3231, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal347 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def boundaryMatrix347 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def boundaryRow347 : Integer.Sparse (Fin 909) := [(0, 9), (1, -110), (2, 515), (3, 1040), (4, 320), (5, -740), (6, 80), (7, 400), (8, 1600), (9, -20), (12, 400), (23, -240), (27, 300), (30, -480), (33, -960), (45, 2880), (51, -2880), (52, 160), (54, -1440), (69, 80), (71, 640), (259, -960), (282, 720), (293, 1440), (308, -720), (325, 1440), (721, -480), (723, -240), (738, 2880), (739, 2880)]

theorem boundarySound347 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow347 (momentVector H) = 0 := by
  have hshape : boundaryMatrix347 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix347 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix347 (0 : Fin 6)) =
      Sparse.eval value3238 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix347 (0 : Fin 6) = raw9140 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9140 hH).trans (sound3238 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix347 (1 : Fin 6)) =
      Sparse.eval value1512 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix347 (1 : Fin 6) = raw9408 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9408 hH).trans (sound1512 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix347 (2 : Fin 6)) =
      Sparse.eval value3236 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix347 (2 : Fin 6) = raw9515 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9515 hH).trans (sound3236 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix347 (3 : Fin 6)) =
      Sparse.eval value3236 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix347 (3 : Fin 6) = raw9524 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9524 hH).trans (sound3236 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix347 (4 : Fin 6)) =
      Sparse.eval value3237 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix347 (4 : Fin 6) = raw9527 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9527 hH).trans (sound3237 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix347 (5 : Fin 6)) =
      Sparse.eval value3037 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix347 (5 : Fin 6) = raw9528 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9528 hH).trans (sound3037 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix347 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix347 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix347 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix347 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix347 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix347 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow347, value1512, value3037, value3236, value3237, value3238, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal349 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def boundaryMatrix349 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def boundaryRow349 : Integer.Sparse (Fin 909) := [(0, -13), (1, -630), (2, 660), (3, 4800), (4, 960), (5, -660), (6, 35), (7, 1840), (8, 720), (9, -20), (12, 1440), (13, 720), (23, -2160), (24, -1200), (25, -2400), (26, 320), (27, 480), (31, -1920), (33, -960), (35, 1040), (48, 1440), (51, -4080), (52, 640), (54, -3120), (55, -960), (56, -1200), (64, -2400), (68, 180), (69, 240), (70, 160), (97, 720), (100, 4320), (104, 1440), (124, -240), (125, -2160), (126, -1440), (197, -480), (238, -1680), (291, 720), (300, 1440), (307, -480), (309, -240), (538, 720), (543, 1440), (643, 1440), (727, -240)]

theorem boundarySound349 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow349 (momentVector H) = 0 := by
  have hshape : boundaryMatrix349 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix349 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix349 (0 : Fin 6)) =
      Sparse.eval value3176 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix349 (0 : Fin 6) = raw9174 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9174 hH).trans (sound3176 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix349 (1 : Fin 6)) =
      Sparse.eval value3189 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix349 (1 : Fin 6) = raw9606 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9606 hH).trans (sound3189 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix349 (2 : Fin 6)) =
      Sparse.eval value3183 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix349 (2 : Fin 6) = raw9678 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9678 hH).trans (sound3183 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix349 (3 : Fin 6)) =
      Sparse.eval value3187 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix349 (3 : Fin 6) = raw9682 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9682 hH).trans (sound3187 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix349 (4 : Fin 6)) =
      Sparse.eval value3132 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix349 (4 : Fin 6) = raw9688 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9688 hH).trans (sound3132 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix349 (5 : Fin 6)) =
      Sparse.eval value3095 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix349 (5 : Fin 6) = raw9689 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9689 hH).trans (sound3095 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix349 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix349 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix349 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix349 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix349 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix349 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow349, value3095, value3132, value3176, value3183, value3187, value3189, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal350 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def boundaryMatrix350 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def boundaryRow350 : Integer.Sparse (Fin 909) := [(0, 18), (1, -520), (2, 425), (3, 2760), (4, 720), (5, -510), (6, 35), (7, 1040), (8, 960), (9, -10), (10, -240), (12, 520), (13, 480), (24, -960), (26, 560), (27, 270), (30, -480), (31, -480), (35, 680), (49, 720), (51, -1080), (52, 80), (55, -840), (68, 90), (69, 40), (71, 160), (82, 80), (95, 720), (107, 1440), (124, -120), (126, -840), (197, -480), (236, -720), (238, -480), (290, 360), (309, -120), (538, 360), (728, -120), (810, 720), (811, 720)]

theorem boundarySound350 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow350 (momentVector H) = 0 := by
  have hshape : boundaryMatrix350 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix350 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix350 (0 : Fin 6)) =
      Sparse.eval value3304 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix350 (0 : Fin 6) = raw9171 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9171 hH).trans (sound3304 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix350 (1 : Fin 6)) =
      Sparse.eval value3234 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix350 (1 : Fin 6) = raw9603 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9603 hH).trans (sound3234 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix350 (2 : Fin 6)) =
      Sparse.eval value3305 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix350 (2 : Fin 6) = raw9655 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9655 hH).trans (sound3305 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix350 (3 : Fin 6)) =
      Sparse.eval value3232 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix350 (3 : Fin 6) = raw9669 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9669 hH).trans (sound3232 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix350 (4 : Fin 6)) =
      Sparse.eval value3303 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix350 (4 : Fin 6) = raw9674 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9674 hH).trans (sound3303 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix350 (5 : Fin 6)) =
      Sparse.eval value3091 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix350 (5 : Fin 6) = raw9675 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9675 hH).trans (sound3091 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix350 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix350 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix350 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix350 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix350 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix350 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow350, value3091, value3232, value3234, value3303, value3304, value3305, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal351 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def boundaryMatrix351 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def boundaryRow351 : Integer.Sparse (Fin 909) := [(0, -2), (1, -195), (2, 360), (3, 2960), (4, 520), (5, -550), (6, 65), (7, 440), (8, 480), (9, -10), (11, 80), (12, 720), (13, 1680), (26, 480), (35, 1200), (45, 720), (51, -960), (52, 1360), (54, -480), (56, -480), (69, 120), (70, 80), (71, 160), (102, 1440), (103, 720), (228, -240), (262, -480), (286, 360), (309, -360), (327, 720), (739, 720), (796, -120), (870, 720)]

theorem boundarySound351 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow351 (momentVector H) = 0 := by
  have hshape : boundaryMatrix351 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix351 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix351 (0 : Fin 6)) =
      Sparse.eval value3382 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix351 (0 : Fin 6) = raw9168 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9168 hH).trans (sound3382 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix351 (1 : Fin 6)) =
      Sparse.eval value3385 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix351 (1 : Fin 6) = raw9597 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9597 hH).trans (sound3385 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix351 (2 : Fin 6)) =
      Sparse.eval value3379 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix351 (2 : Fin 6) = raw9652 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9652 hH).trans (sound3379 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix351 (3 : Fin 6)) =
      Sparse.eval value3384 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix351 (3 : Fin 6) = raw9663 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9663 hH).trans (sound3384 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix351 (4 : Fin 6)) =
      Sparse.eval value3366 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix351 (4 : Fin 6) = raw9667 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9667 hH).trans (sound3366 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix351 (5 : Fin 6)) =
      Sparse.eval value3036 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix351 (5 : Fin 6) = raw9668 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9668 hH).trans (sound3036 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix351 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix351 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix351 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix351 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix351 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix351 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow351, value3036, value3366, value3379, value3382, value3384, value3385, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal353 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def boundaryMatrix353 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def boundaryRow353 : Integer.Sparse (Fin 909) := [(0, -8), (1, -345), (2, 605), (3, 5600), (4, 1280), (5, -1000), (6, 130), (7, 480), (8, 640), (11, 240), (12, 1280), (13, 2880), (26, 1440), (35, 2160), (43, 1440), (45, 1440), (51, -1200), (52, 2480), (54, -960), (55, -240), (56, -960), (77, 720), (102, 2880), (103, 2880), (228, -960), (546, 1440), (737, 1440), (739, 1440), (870, 1440)]

theorem boundarySound353 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow353 (momentVector H) = 0 := by
  have hshape : boundaryMatrix353 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix353 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix353 (0 : Fin 6)) =
      Sparse.eval value3383 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix353 (0 : Fin 6) = raw9153 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9153 hH).trans (sound3383 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix353 (1 : Fin 6)) =
      Sparse.eval value3386 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix353 (1 : Fin 6) = raw9561 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9561 hH).trans (sound3386 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix353 (2 : Fin 6)) =
      Sparse.eval value3380 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix353 (2 : Fin 6) = raw9586 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9586 hH).trans (sound3380 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix353 (3 : Fin 6)) =
      Sparse.eval value3385 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix353 (3 : Fin 6) = raw9597 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9597 hH).trans (sound3385 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix353 (4 : Fin 6)) =
      Sparse.eval value3367 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix353 (4 : Fin 6) = raw9601 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9601 hH).trans (sound3367 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix353 (5 : Fin 6)) =
      Sparse.eval value3077 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix353 (5 : Fin 6) = raw9602 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9602 hH).trans (sound3077 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix353 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix353 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix353 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix353 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix353 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix353 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow353, value3077, value3367, value3380, value3383, value3385, value3386, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal354 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix354 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryRow354 : Integer.Sparse (Fin 909) := [(0, -29), (1, 370), (2, 835), (3, 4080), (5, -1460), (6, 210), (7, 1200), (8, 640), (9, -20), (10, -720), (12, 1280), (13, 3840), (33, -960), (35, 2560), (38, 1440), (52, 3040), (54, -960), (59, -960), (69, 240), (70, 160), (72, 720), (75, 1440), (82, 800), (128, 800), (199, -720), (201, -1920), (306, -720), (313, 2880), (498, 720), (505, 1440), (540, 1440), (721, -960), (723, -240), (760, 1440)]

theorem boundarySound354 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow354 (momentVector H) = 0 := by
  have hshape : boundaryMatrix354 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix354 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix354 (0 : Fin 6)) =
      Sparse.eval value3177 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix354 (0 : Fin 6) = raw9151 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9151 hH).trans (sound3177 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix354 (1 : Fin 6)) =
      Sparse.eval value3184 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix354 (1 : Fin 6) = raw9559 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9559 hH).trans (sound3184 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix354 (2 : Fin 6)) =
      Sparse.eval value3192 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix354 (2 : Fin 6) = raw9584 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9584 hH).trans (sound3192 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix354 (3 : Fin 6)) =
      Sparse.eval value3192 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix354 (3 : Fin 6) = raw9589 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9589 hH).trans (sound3192 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix354 (4 : Fin 6)) =
      Sparse.eval value3133 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix354 (4 : Fin 6) = raw9590 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9590 hH).trans (sound3133 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix354 (5 : Fin 6)) =
      Sparse.eval value3017 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix354 (5 : Fin 6) = raw9591 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9591 hH).trans (sound3017 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix354 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix354 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix354 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix354 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix354 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix354 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow354, value3017, value3133, value3177, value3184, value3192, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal355 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def boundaryMatrix355 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def boundaryRow355 : Integer.Sparse (Fin 909) := [(0, -1), (1, -370), (2, 105), (3, 2400), (4, 720), (5, -40), (7, 480), (12, 1200), (13, 640), (23, -2160), (24, -2160), (25, -1440), (27, 300), (33, -1440), (35, 320), (55, -2880), (63, -960), (68, 60), (124, -720), (126, -720), (196, -480), (197, -1440), (290, 2160), (299, 2160), (306, -720), (728, -720)]

theorem boundarySound355 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow355 (momentVector H) = 0 := by
  have hshape : boundaryMatrix355 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix355 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix355 (0 : Fin 6)) =
      Sparse.eval value1523 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix355 (0 : Fin 6) = raw9700 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9700 hH).trans (sound1523 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix355 (1 : Fin 6)) =
      Sparse.eval value1523 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix355 (1 : Fin 6) = raw9764 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9764 hH).trans (sound1523 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix355 (2 : Fin 6)) =
      Sparse.eval value1523 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix355 (2 : Fin 6) = raw9788 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9788 hH).trans (sound1523 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix355 (3 : Fin 6)) =
      Sparse.eval value3293 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix355 (3 : Fin 6) = raw9790 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9790 hH).trans (sound3293 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix355 (4 : Fin 6)) =
      Sparse.eval value3265 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix355 (4 : Fin 6) = raw9792 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9792 hH).trans (sound3265 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix355 (5 : Fin 6)) =
      Sparse.eval value3294 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix355 (5 : Fin 6) = raw9793 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9793 hH).trans (sound3294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix355 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix355 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix355 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix355 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix355 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix355 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow355, value1523, value3265, value3293, value3294, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal356 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def boundaryMatrix356 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def boundaryRow356 : Integer.Sparse (Fin 909) := [(0, -2), (1, -69), (2, 24), (3, 432), (4, 48), (5, -36), (6, 3), (7, 192), (9, -4), (12, 240), (13, 64), (23, -432), (25, -144), (27, 84), (33, -288), (35, 96), (51, -432), (54, -576), (63, -96), (68, 24), (69, 48), (70, 32), (124, -288), (196, -192), (259, -288), (282, 432), (293, 432), (308, -144), (721, -144), (723, -144)]

theorem boundarySound356 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow356 (momentVector H) = 0 := by
  have hshape : boundaryMatrix356 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix356 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix356 (0 : Fin 6)) =
      Sparse.eval value1507 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix356 (0 : Fin 6) = raw9701 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9701 hH).trans (sound1507 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix356 (1 : Fin 6)) =
      Sparse.eval value1507 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix356 (1 : Fin 6) = raw9765 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9765 hH).trans (sound1507 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix356 (2 : Fin 6)) =
      Sparse.eval value1507 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix356 (2 : Fin 6) = raw9789 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9789 hH).trans (sound1507 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix356 (3 : Fin 6)) =
      Sparse.eval value3240 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix356 (3 : Fin 6) = raw9791 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9791 hH).trans (sound3240 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix356 (4 : Fin 6)) =
      Sparse.eval value3241 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix356 (4 : Fin 6) = raw9794 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9794 hH).trans (sound3241 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix356 (5 : Fin 6)) =
      Sparse.eval value3223 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix356 (5 : Fin 6) = raw9795 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9795 hH).trans (sound3223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix356 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix356 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix356 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix356 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix356 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix356 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow356, value1507, value3223, value3240, value3241, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal362 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def boundaryMatrix362 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def boundaryRow362 : Integer.Sparse (Fin 909) := [(1, -93), (2, 175), (3, 784), (4, 192), (5, -216), (6, 16), (7, 416), (8, 336), (9, -8), (12, 32), (13, 32), (24, -336), (26, 112), (27, 96), (30, -96), (31, -192), (35, 176), (46, 144), (51, -528), (52, 144), (55, -96), (56, -96), (68, 24), (69, 96), (70, 48), (71, 80), (95, 288), (106, 144), (107, 288), (126, -288), (197, -96), (236, -96), (237, -48), (238, -96), (262, -96), (308, -48), (309, -48), (322, 144), (327, 144), (735, 288), (736, 144), (738, 144)]

theorem boundarySound362 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow362 (momentVector H) = 0 := by
  have hshape : boundaryMatrix362 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix362 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix362 (0 : Fin 6)) =
      Sparse.eval value1504 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix362 (0 : Fin 6) = raw9732 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9732 hH).trans (sound1504 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix362 (1 : Fin 6)) =
      Sparse.eval value3232 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix362 (1 : Fin 6) = raw9908 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9908 hH).trans (sound3232 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix362 (2 : Fin 6)) =
      Sparse.eval value3233 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix362 (2 : Fin 6) = raw9933 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9933 hH).trans (sound3233 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix362 (3 : Fin 6)) =
      Sparse.eval value3234 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix362 (3 : Fin 6) = raw9935 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9935 hH).trans (sound3234 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix362 (4 : Fin 6)) =
      Sparse.eval value2889 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix362 (4 : Fin 6) = raw9938 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9938 hH).trans (sound2889 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix362 (5 : Fin 6)) =
      Sparse.eval value3222 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix362 (5 : Fin 6) = raw9939 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9939 hH).trans (sound3222 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix362 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix362 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix362 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix362 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix362 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix362 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow362, value1504, value2889, value3222, value3232, value3233, value3234, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal363 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def boundaryMatrix363 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def boundaryRow363 : Integer.Sparse (Fin 909) := [(0, -7), (1, -580), (2, 570), (3, 6160), (4, 1440), (5, -460), (6, 25), (7, 1440), (8, 480), (10, -720), (12, 2000), (13, 2880), (25, -1440), (26, 1440), (31, -720), (33, -1440), (35, 2080), (38, 2160), (39, 4320), (51, -720), (52, 1520), (54, -2160), (55, -720), (59, -1440), (60, 320), (81, -1440), (82, 240), (84, 2160), (85, 4320), (128, 480), (228, -2160), (311, 2160), (321, 4320), (323, 1440), (329, 4320), (330, 4320), (490, -720), (492, -960)]

theorem boundarySound363 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow363 (momentVector H) = 0 := by
  have hshape : boundaryMatrix363 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix363 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix363 (0 : Fin 6)) =
      Sparse.eval value2931 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix363 (0 : Fin 6) = raw8318 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8318 hH).trans (sound2931 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix363 (1 : Fin 6)) =
      Sparse.eval value2931 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix363 (1 : Fin 6) = raw9205 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9205 hH).trans (sound2931 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix363 (2 : Fin 6)) =
      Sparse.eval value2931 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix363 (2 : Fin 6) = raw9252 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9252 hH).trans (sound2931 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix363 (3 : Fin 6)) =
      Sparse.eval value2923 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix363 (3 : Fin 6) = raw9268 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9268 hH).trans (sound2923 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix363 (4 : Fin 6)) =
      Sparse.eval value2924 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix363 (4 : Fin 6) = raw9271 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9271 hH).trans (sound2924 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix363 (5 : Fin 6)) =
      Sparse.eval value3375 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix363 (5 : Fin 6) = raw9273 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9273 hH).trans (sound3375 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix363 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix363 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix363 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix363 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix363 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix363 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow363, value2923, value2924, value2931, value3375, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal364 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def boundaryMatrix364 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def boundaryRow364 : Integer.Sparse (Fin 909) := [(0, 21), (1, -705), (2, 350), (3, 6240), (4, 2720), (5, -580), (6, 30), (7, 1920), (8, 960), (10, -720), (11, 240), (12, 480), (13, 640), (26, 3120), (35, 2000), (37, 2160), (40, 4320), (52, 240), (55, -720), (56, -2160), (81, -1440), (82, 240), (83, 2160), (85, 4320), (228, -3120), (501, 4320), (508, 4320), (784, 1440), (794, 4320), (796, -960)]

theorem boundarySound364 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow364 (momentVector H) = 0 := by
  have hshape : boundaryMatrix364 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix364 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix364 (0 : Fin 6)) =
      Sparse.eval value3300 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (0 : Fin 6) = raw8319 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8319 hH).trans (sound3300 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix364 (1 : Fin 6)) =
      Sparse.eval value3300 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (1 : Fin 6) = raw9206 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9206 hH).trans (sound3300 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix364 (2 : Fin 6)) =
      Sparse.eval value3300 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (2 : Fin 6) = raw9253 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9253 hH).trans (sound3300 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix364 (3 : Fin 6)) =
      Sparse.eval value3287 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (3 : Fin 6) = raw9269 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9269 hH).trans (sound3287 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix364 (4 : Fin 6)) =
      Sparse.eval value3351 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (4 : Fin 6) = raw9272 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9272 hH).trans (sound3351 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix364 (5 : Fin 6)) =
      Sparse.eval value3467 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (5 : Fin 6) = raw9275 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9275 hH).trans (sound3467 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix364 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix364 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix364 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix364 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix364 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix364 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow364, value3287, value3300, value3351, value3467, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal365 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def boundaryMatrix365 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def boundaryRow365 : Integer.Sparse (Fin 909) := [(1, -78), (2, 19), (3, 432), (4, 96), (5, -64), (6, 9), (7, 144), (9, -4), (11, 48), (12, 144), (23, -144), (25, -288), (26, 96), (27, 36), (31, -288), (33, -576), (35, 224), (36, 432), (39, 864), (51, -288), (52, 144), (54, -720), (55, -144), (68, 12), (69, 48), (70, 32), (87, 432), (123, -288), (124, -144), (196, -96), (226, -144), (228, -144), (237, -144), (259, -288), (282, 432), (306, -288), (308, -144), (312, 432), (315, 864), (498, 864), (507, 864), (721, -432), (723, -336), (728, -48), (764, 864), (783, 288)]

theorem boundarySound365 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow365 (momentVector H) = 0 := by
  have hshape : boundaryMatrix365 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix365 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix365 (0 : Fin 6)) =
      Sparse.eval value3324 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (0 : Fin 6) = raw8320 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8320 hH).trans (sound3324 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix365 (1 : Fin 6)) =
      Sparse.eval value3324 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (1 : Fin 6) = raw9207 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9207 hH).trans (sound3324 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix365 (2 : Fin 6)) =
      Sparse.eval value3324 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (2 : Fin 6) = raw9254 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9254 hH).trans (sound3324 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix365 (3 : Fin 6)) =
      Sparse.eval value3286 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (3 : Fin 6) = raw9270 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9270 hH).trans (sound3286 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix365 (4 : Fin 6)) =
      Sparse.eval value3468 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (4 : Fin 6) = raw9274 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9274 hH).trans (sound3468 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix365 (5 : Fin 6)) =
      Sparse.eval value3328 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (5 : Fin 6) = raw9276 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9276 hH).trans (sound3328 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix365 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix365 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix365 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix365 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix365 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix365 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow365, value3286, value3324, value3328, value3468, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal368 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def boundaryMatrix368 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def boundaryRow368 : Integer.Sparse (Fin 909) := [(0, 1), (1, -98), (2, 113), (3, 1488), (4, 512), (5, -160), (6, 14), (7, 560), (8, 128), (11, 128), (26, 896), (35, 896), (52, 368), (53, 288), (67, 128), (81, -672), (83, 144), (84, 432), (85, 576), (228, -816), (460, 288), (702, 288), (709, 576)]

theorem boundarySound368 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow368 (momentVector H) = 0 := by
  have hshape : boundaryMatrix368 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix368 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix368 (0 : Fin 6)) =
      Sparse.eval value3195 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (0 : Fin 6) = raw8324 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8324 hH).trans (sound3195 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix368 (1 : Fin 6)) =
      Sparse.eval value3195 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (1 : Fin 6) = raw9211 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9211 hH).trans (sound3195 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix368 (2 : Fin 6)) =
      Sparse.eval value3351 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (2 : Fin 6) = raw9272 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9272 hH).trans (sound3351 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix368 (3 : Fin 6)) =
      Sparse.eval value3213 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (3 : Fin 6) = raw9317 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9317 hH).trans (sound3213 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix368 (4 : Fin 6)) =
      Sparse.eval value3052 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (4 : Fin 6) = raw9320 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9320 hH).trans (sound3052 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix368 (5 : Fin 6)) =
      Sparse.eval value3447 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (5 : Fin 6) = raw9322 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9322 hH).trans (sound3447 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix368 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix368 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix368 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix368 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix368 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix368 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow368, value3052, value3195, value3213, value3351, value3447, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
