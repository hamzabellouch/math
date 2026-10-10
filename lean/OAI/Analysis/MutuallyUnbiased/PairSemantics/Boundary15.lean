import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound27
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical201
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical261
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical262
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical263
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical264
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical293
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical294
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical295
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical296
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical297
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical299
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical300
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical301
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical305
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical306
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical307
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical308
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical309

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal408 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def boundaryMatrix408 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def boundaryRow408 : Integer.Sparse (Fin 909) := [(0, -23), (1, -105), (2, 1130), (3, 5680), (4, 1200), (5, -1300), (6, 90), (7, 1760), (8, 2000), (10, -240), (12, 1600), (13, 2800), (24, -240), (26, 480), (27, 60), (31, -720), (33, -1920), (34, 320), (35, 1040), (39, 1440), (42, 1440), (51, -3120), (52, 1920), (55, -480), (56, -960), (59, -2400), (60, 320), (74, 720), (76, 1440), (81, -960), (85, 1440), (86, 1440), (128, 480), (201, -720), (228, -480), (273, -480), (311, 2160), (314, 1440), (315, 2880), (319, 1440), (326, 2880), (328, 1440), (490, -720)]

theorem boundarySound408 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow408 (momentVector H) = 0 := by
  have hshape : boundaryMatrix408 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix408 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix408 (0 : Fin 6)) =
      Sparse.eval value2907 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix408 (0 : Fin 6) = raw6442 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6442 hH).trans (sound2907 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix408 (1 : Fin 6)) =
      Sparse.eval value2915 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix408 (1 : Fin 6) = raw8353 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8353 hH).trans (sound2915 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix408 (2 : Fin 6)) =
      Sparse.eval value2915 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix408 (2 : Fin 6) = raw8418 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8418 hH).trans (sound2915 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix408 (3 : Fin 6)) =
      Sparse.eval value2929 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix408 (3 : Fin 6) = raw8428 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8428 hH).trans (sound2929 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix408 (4 : Fin 6)) =
      Sparse.eval value2901 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix408 (4 : Fin 6) = raw8431 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8431 hH).trans (sound2901 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix408 (5 : Fin 6)) =
      Sparse.eval value3370 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix408 (5 : Fin 6) = raw8434 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8434 hH).trans (sound3370 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix408 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix408 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix408 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix408 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix408 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix408 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow408, value2901, value2907, value2915, value2929, value3370, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal409 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def boundaryMatrix409 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def boundaryRow409 : Integer.Sparse (Fin 909) := [(0, -14), (1, 15), (2, 500), (3, 3840), (4, 960), (5, -1260), (6, 175), (7, 480), (8, 960), (9, -20), (12, 960), (13, 2880), (24, -480), (26, 800), (27, 120), (31, -480), (33, -960), (35, 2080), (39, 1440), (42, 1440), (51, -960), (52, 2080), (54, -960), (55, -480), (56, -2400), (68, 60), (69, 80), (71, 320), (82, 640), (99, 1440), (123, -480), (124, -240), (126, -480), (128, 640), (197, -480), (199, -480), (201, -960), (237, -480), (259, -480), (262, -960), (286, 720), (288, 1440), (306, -960), (308, -480), (309, -240), (312, 720), (315, 1440), (328, 1440), (329, 1440), (500, 2880), (506, 1440), (721, -720), (728, -240), (764, 1440), (796, -720), (798, 2880)]

theorem boundarySound409 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow409 (momentVector H) = 0 := by
  have hshape : boundaryMatrix409 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix409 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix409 (0 : Fin 6)) =
      Sparse.eval value3297 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix409 (0 : Fin 6) = raw6448 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6448 hH).trans (sound3297 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix409 (1 : Fin 6)) =
      Sparse.eval value3298 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix409 (1 : Fin 6) = raw8354 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8354 hH).trans (sound3298 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix409 (2 : Fin 6)) =
      Sparse.eval value3298 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix409 (2 : Fin 6) = raw8419 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8419 hH).trans (sound3298 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix409 (3 : Fin 6)) =
      Sparse.eval value3414 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix409 (3 : Fin 6) = raw8429 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8429 hH).trans (sound3414 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix409 (4 : Fin 6)) =
      Sparse.eval value3314 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix409 (4 : Fin 6) = raw8438 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8438 hH).trans (sound3314 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix409 (5 : Fin 6)) =
      Sparse.eval value3465 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix409 (5 : Fin 6) = raw8439 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8439 hH).trans (sound3465 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix409 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix409 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix409 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix409 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix409 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix409 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow409, value3297, value3298, value3314, value3414, value3465, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal410 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def boundaryMatrix410 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def boundaryRow410 : Integer.Sparse (Fin 909) := [(0, -2), (1, 11), (2, 115), (3, 424), (4, 64), (5, -170), (6, 8), (7, 384), (8, 296), (12, 32), (13, 40), (25, -24), (26, 104), (31, -48), (33, -72), (34, 16), (35, 232), (39, 72), (51, -48), (52, 80), (54, -48), (59, -48), (64, -48), (67, 40), (74, 72), (81, -240), (85, 144), (86, 144), (100, 72), (107, 144), (199, -24), (228, -48), (238, -72), (271, -48), (307, -72), (319, 144), (326, 144), (425, 72), (426, 72), (428, 144), (500, 144)]

theorem boundarySound410 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow410 (momentVector H) = 0 := by
  have hshape : boundaryMatrix410 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix410 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix410 (0 : Fin 6)) =
      Sparse.eval value3103 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix410 (0 : Fin 6) = raw6457 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6457 hH).trans (sound3103 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix410 (1 : Fin 6)) =
      Sparse.eval value3106 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix410 (1 : Fin 6) = raw8356 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8356 hH).trans (sound3106 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix410 (2 : Fin 6)) =
      Sparse.eval value3111 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix410 (2 : Fin 6) = raw8421 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8421 hH).trans (sound3111 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix410 (3 : Fin 6)) =
      Sparse.eval value3111 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix410 (3 : Fin 6) = raw8448 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8448 hH).trans (sound3111 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix410 (4 : Fin 6)) =
      Sparse.eval value3019 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix410 (4 : Fin 6) = raw8450 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8450 hH).trans (sound3019 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix410 (5 : Fin 6)) =
      Sparse.eval value3402 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix410 (5 : Fin 6) = raw8452 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8452 hH).trans (sound3402 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix410 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix410 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix410 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix410 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix410 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix410 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow410, value3019, value3103, value3106, value3111, value3402, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal412 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def boundaryMatrix412 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def boundaryRow412 : Integer.Sparse (Fin 909) := [(0, -6), (1, 72), (2, 193), (3, 624), (4, 80), (5, -340), (6, 31), (7, 448), (8, 384), (11, 32), (12, 16), (13, 64), (26, 176), (33, -96), (35, 384), (52, 368), (59, -48), (67, 32), (75, 144), (81, -288), (85, 432), (86, 288), (128, 16), (201, -48), (228, -288), (428, 288), (517, 144), (760, 144), (855, 144)]

theorem boundarySound412 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow412 (momentVector H) = 0 := by
  have hshape : boundaryMatrix412 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix412 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix412 (0 : Fin 6)) =
      Sparse.eval value3340 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix412 (0 : Fin 6) = raw6405 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6405 hH).trans (sound3340 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix412 (1 : Fin 6)) =
      Sparse.eval value3341 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix412 (1 : Fin 6) = raw8348 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8348 hH).trans (sound3341 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix412 (2 : Fin 6)) =
      Sparse.eval value3343 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix412 (2 : Fin 6) = raw8400 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8400 hH).trans (sound3343 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix412 (3 : Fin 6)) =
      Sparse.eval value3350 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix412 (3 : Fin 6) = raw8406 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8406 hH).trans (sound3350 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix412 (4 : Fin 6)) =
      Sparse.eval value3124 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix412 (4 : Fin 6) = raw8408 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8408 hH).trans (sound3124 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix412 (5 : Fin 6)) =
      Sparse.eval value3419 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix412 (5 : Fin 6) = raw8409 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8409 hH).trans (sound3419 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix412 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix412 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix412 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix412 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix412 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix412 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow412, value3124, value3340, value3341, value3343, value3350, value3419, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal419 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def boundaryMatrix419 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def boundaryRow419 : Integer.Sparse (Fin 909) := [(0, 27), (1, -905), (2, 610), (3, 2960), (4, 2000), (5, -400), (6, 20), (7, 240), (8, 560), (9, -20), (12, 560), (23, -240), (24, -1680), (26, 160), (27, 900), (31, -2400), (47, 720), (51, -5040), (52, 400), (56, -960), (68, 180), (69, 80), (71, 80), (124, -240), (126, -1440), (205, 720), (207, 1440), (209, 1440), (238, -960), (262, -480), (308, -240), (309, -240), (538, 720), (751, 720), (753, 1440)]

theorem boundarySound419 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow419 (momentVector H) = 0 := by
  have hshape : boundaryMatrix419 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix419 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix419 (0 : Fin 6)) =
      Sparse.eval value3253 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix419 (0 : Fin 6) = raw9137 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9137 hH).trans (sound3253 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix419 (1 : Fin 6)) =
      Sparse.eval value1738 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix419 (1 : Fin 6) = raw9405 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9405 hH).trans (sound1738 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix419 (2 : Fin 6)) =
      Sparse.eval value3259 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix419 (2 : Fin 6) = raw9475 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9475 hH).trans (sound3259 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix419 (3 : Fin 6)) =
      Sparse.eval value3260 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix419 (3 : Fin 6) = raw9506 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9506 hH).trans (sound3260 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix419 (4 : Fin 6)) =
      Sparse.eval value3235 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix419 (4 : Fin 6) = raw9508 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9508 hH).trans (sound3235 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix419 (5 : Fin 6)) =
      Sparse.eval value3032 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix419 (5 : Fin 6) = raw9509 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9509 hH).trans (sound3032 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix419 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix419 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix419 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix419 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix419 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix419 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow419, value1738, value3032, value3235, value3253, value3259, value3260, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal422 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def boundaryMatrix422 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def boundaryRow422 : Integer.Sparse (Fin 909) := [(0, 33), (1, -685), (2, 305), (3, 6480), (4, 2720), (5, -380), (6, 45), (7, 1120), (8, 80), (12, 400), (13, 400), (24, -240), (26, 3360), (31, -720), (33, -480), (34, 640), (35, 2000), (44, 1440), (52, 1040), (67, 640), (81, -960), (95, 720), (99, 1440), (119, 1440), (453, 1440), (460, 1440)]

theorem boundarySound422 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow422 (momentVector H) = 0 := by
  have hshape : boundaryMatrix422 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix422 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix422 (0 : Fin 6)) =
      Sparse.eval value3047 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix422 (0 : Fin 6) = raw9123 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9123 hH).trans (sound3047 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix422 (1 : Fin 6)) =
      Sparse.eval value1768 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix422 (1 : Fin 6) = raw9392 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9392 hH).trans (sound1768 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix422 (2 : Fin 6)) =
      Sparse.eval value3055 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix422 (2 : Fin 6) = raw9449 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9449 hH).trans (sound3055 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix422 (3 : Fin 6)) =
      Sparse.eval value3059 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix422 (3 : Fin 6) = raw9465 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9465 hH).trans (sound3059 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix422 (4 : Fin 6)) =
      Sparse.eval value2987 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix422 (4 : Fin 6) = raw9467 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9467 hH).trans (sound2987 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix422 (5 : Fin 6)) =
      Sparse.eval value3060 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix422 (5 : Fin 6) = raw9468 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9468 hH).trans (sound3060 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix422 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix422 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix422 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix422 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix422 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix422 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow422, value1768, value2987, value3047, value3055, value3059, value3060, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal423 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def boundaryMatrix423 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def boundaryRow423 : Integer.Sparse (Fin 909) := [(0, -3), (1, -39), (2, 91), (3, 768), (4, 192), (5, -68), (6, 5), (7, 144), (8, 64), (12, 176), (13, 176), (25, -192), (26, 256), (31, -144), (33, -672), (34, 64), (35, 224), (43, 288), (51, -48), (52, 160), (59, -192), (64, -144), (67, 64), (81, -192), (95, 144), (103, 288), (104, 288), (110, 144), (112, 288), (201, -48), (307, -144), (425, 144), (428, 288), (472, 288)]

theorem boundarySound423 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow423 (momentVector H) = 0 := by
  have hshape : boundaryMatrix423 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix423 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix423 (0 : Fin 6)) =
      Sparse.eval value3050 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix423 (0 : Fin 6) = raw9141 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9141 hH).trans (sound3050 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix423 (1 : Fin 6)) =
      Sparse.eval value1718 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix423 (1 : Fin 6) = raw9409 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9409 hH).trans (sound1718 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix423 (2 : Fin 6)) =
      Sparse.eval value3070 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix423 (2 : Fin 6) = raw9516 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9516 hH).trans (sound3070 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix423 (3 : Fin 6)) =
      Sparse.eval value3071 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix423 (3 : Fin 6) = raw9529 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9529 hH).trans (sound3071 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix423 (4 : Fin 6)) =
      Sparse.eval value2954 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix423 (4 : Fin 6) = raw9533 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9533 hH).trans (sound2954 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix423 (5 : Fin 6)) =
      Sparse.eval value3069 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix423 (5 : Fin 6) = raw9534 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9534 hH).trans (sound3069 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix423 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix423 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix423 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix423 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix423 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix423 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow423, value1718, value2954, value3050, value3069, value3070, value3071, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal425 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def boundaryMatrix425 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def boundaryRow425 : Integer.Sparse (Fin 909) := [(0, -11), (1, -790), (2, 850), (3, 5920), (4, 1280), (5, -520), (6, 35), (7, 640), (8, 320), (9, -20), (12, 2000), (13, 1440), (23, -1200), (25, -2880), (26, 480), (27, 720), (31, -3840), (33, -3840), (35, 400), (51, -5760), (52, 800), (54, -960), (55, -2160), (64, -2880), (68, 180), (69, 80), (70, 80), (124, -240), (125, -960), (126, -480), (140, 720), (142, 2880), (145, 1440), (238, -1920), (260, -480), (309, -480), (383, 1440), (538, 1440)]

theorem boundarySound425 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow425 (momentVector H) = 0 := by
  have hshape : boundaryMatrix425 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix425 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix425 (0 : Fin 6)) =
      Sparse.eval value3220 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix425 (0 : Fin 6) = raw9162 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9162 hH).trans (sound3220 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix425 (1 : Fin 6)) =
      Sparse.eval value3144 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix425 (1 : Fin 6) = raw9580 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9580 hH).trans (sound3144 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix425 (2 : Fin 6)) =
      Sparse.eval value3144 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix425 (2 : Fin 6) = raw9616 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9616 hH).trans (sound3144 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix425 (3 : Fin 6)) =
      Sparse.eval value3142 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix425 (3 : Fin 6) = raw9634 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9634 hH).trans (sound3142 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix425 (4 : Fin 6)) =
      Sparse.eval value3033 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix425 (4 : Fin 6) = raw9642 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9642 hH).trans (sound3033 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix425 (5 : Fin 6)) =
      Sparse.eval value3221 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix425 (5 : Fin 6) = raw9643 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9643 hH).trans (sound3221 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix425 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix425 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix425 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix425 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix425 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix425 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow425, value3033, value3142, value3144, value3220, value3221, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal430 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def boundaryMatrix430 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def boundaryRow430 : Integer.Sparse (Fin 909) := [(0, -21), (1, 80), (2, 365), (3, 4080), (5, -900), (6, 170), (7, 560), (9, -60), (12, 1200), (13, 4160), (23, -960), (25, -960), (27, 240), (31, -960), (33, -1920), (35, 1760), (52, 2240), (54, -1440), (63, -2640), (68, 180), (69, 240), (70, 160), (123, -960), (124, -240), (125, -480), (126, -480), (129, 720), (144, 1440), (196, -720), (231, 1440), (237, -1920), (306, -720), (498, 720), (721, -960), (723, -240), (760, 1440)]

theorem boundarySound430 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow430 (momentVector H) = 0 := by
  have hshape : boundaryMatrix430 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix430 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix430 (0 : Fin 6)) =
      Sparse.eval value3254 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix430 (0 : Fin 6) = raw9166 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9166 hH).trans (sound3254 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix430 (1 : Fin 6)) =
      Sparse.eval value3263 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix430 (1 : Fin 6) = raw9592 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9592 hH).trans (sound3263 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix430 (2 : Fin 6)) =
      Sparse.eval value3264 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix430 (2 : Fin 6) = raw9650 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9650 hH).trans (sound3264 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix430 (3 : Fin 6)) =
      Sparse.eval value3264 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix430 (3 : Fin 6) = raw9657 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9657 hH).trans (sound3264 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix430 (4 : Fin 6)) =
      Sparse.eval value3239 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix430 (4 : Fin 6) = raw9660 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9660 hH).trans (sound3239 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix430 (5 : Fin 6)) =
      Sparse.eval value3034 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix430 (5 : Fin 6) = raw9661 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9661 hH).trans (sound3034 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix430 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix430 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix430 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix430 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix430 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix430 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow430, value3034, value3239, value3254, value3263, value3264, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal433 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def boundaryMatrix433 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def boundaryRow433 : Integer.Sparse (Fin 909) := [(0, -26), (1, -335), (2, 380), (3, 3600), (4, 160), (5, -320), (6, 5), (7, 1040), (8, 480), (9, -20), (10, -960), (12, 1920), (13, 1920), (23, -1200), (24, -480), (27, 660), (35, 160), (38, 720), (47, 1440), (51, -3120), (52, 80), (54, -480), (55, -1680), (59, -1200), (68, 120), (69, 160), (124, -720), (125, -480), (126, -240), (140, 1440), (205, 720), (259, -480), (308, -480), (321, 720), (538, 1440), (539, 1440), (727, -240)]

theorem boundarySound433 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow433 (momentVector H) = 0 := by
  have hshape : boundaryMatrix433 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix433 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix433 (0 : Fin 6)) =
      Sparse.eval value1631 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix433 (0 : Fin 6) = raw9703 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9703 hH).trans (sound1631 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix433 (1 : Fin 6)) =
      Sparse.eval value1631 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix433 (1 : Fin 6) = raw9767 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9767 hH).trans (sound1631 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix433 (2 : Fin 6)) =
      Sparse.eval value3134 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix433 (2 : Fin 6) = raw9799 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9799 hH).trans (sound3134 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix433 (3 : Fin 6)) =
      Sparse.eval value3135 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix433 (3 : Fin 6) = raw9807 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9807 hH).trans (sound3135 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix433 (4 : Fin 6)) =
      Sparse.eval value3118 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix433 (4 : Fin 6) = raw9810 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9810 hH).trans (sound3118 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix433 (5 : Fin 6)) =
      Sparse.eval value2966 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix433 (5 : Fin 6) = raw9811 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9811 hH).trans (sound2966 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix433 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix433 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix433 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix433 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix433 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix433 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow433, value1631, value2966, value3118, value3134, value3135, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal434 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def boundaryMatrix434 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def boundaryRow434 : Integer.Sparse (Fin 909) := [(0, -9), (1, -10), (2, -35), (3, 3040), (4, 800), (5, -320), (6, 40), (7, 2240), (8, 320), (9, -20), (12, 320), (13, 80), (23, -480), (25, -2160), (26, 1440), (33, -480), (35, 960), (38, 720), (51, -480), (52, 160), (54, -2640), (64, -960), (69, 240), (97, 2880), (124, -480), (228, -960), (260, -480), (321, 720), (383, 1440), (492, -240)]

theorem boundarySound434 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow434 (momentVector H) = 0 := by
  have hshape : boundaryMatrix434 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix434 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix434 (0 : Fin 6)) =
      Sparse.eval value1680 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix434 (0 : Fin 6) = raw9702 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9702 hH).trans (sound1680 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix434 (1 : Fin 6)) =
      Sparse.eval value1680 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix434 (1 : Fin 6) = raw9766 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9766 hH).trans (sound1680 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix434 (2 : Fin 6)) =
      Sparse.eval value2993 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix434 (2 : Fin 6) = raw9798 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9798 hH).trans (sound2993 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix434 (3 : Fin 6)) =
      Sparse.eval value2993 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix434 (3 : Fin 6) = raw9804 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9804 hH).trans (sound2993 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix434 (4 : Fin 6)) =
      Sparse.eval value2925 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix434 (4 : Fin 6) = raw9805 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9805 hH).trans (sound2925 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix434 (5 : Fin 6)) =
      Sparse.eval value2996 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix434 (5 : Fin 6) = raw9806 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9806 hH).trans (sound2996 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix434 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix434 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix434 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix434 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix434 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix434 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow434, value1680, value2925, value2993, value2996, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal436 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def boundaryMatrix436 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def boundaryRow436 : Integer.Sparse (Fin 909) := [(0, 6), (1, -240), (2, 565), (3, 4160), (4, 1680), (5, -480), (6, 35), (7, 800), (8, 880), (9, -20), (24, -240), (26, 1520), (27, 60), (31, -480), (35, 320), (37, 720), (46, 1440), (51, -1440), (52, 800), (56, -1680), (69, 160), (71, 80), (81, -1200), (107, 1440), (124, -240), (126, -240), (228, -960), (262, -480), (501, 720), (735, 1440), (745, 1440), (753, 1440), (796, -240)]

theorem boundarySound436 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow436 (momentVector H) = 0 := by
  have hshape : boundaryMatrix436 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix436 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix436 (0 : Fin 6)) =
      Sparse.eval value1739 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix436 (0 : Fin 6) = raw9714 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9714 hH).trans (sound1739 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix436 (1 : Fin 6)) =
      Sparse.eval value1739 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix436 (1 : Fin 6) = raw9778 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9778 hH).trans (sound1739 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix436 (2 : Fin 6)) =
      Sparse.eval value3246 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix436 (2 : Fin 6) = raw9849 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9849 hH).trans (sound3246 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix436 (3 : Fin 6)) =
      Sparse.eval value3249 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix436 (3 : Fin 6) = raw9854 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9854 hH).trans (sound3249 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix436 (4 : Fin 6)) =
      Sparse.eval value3245 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix436 (4 : Fin 6) = raw9856 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9856 hH).trans (sound3245 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix436 (5 : Fin 6)) =
      Sparse.eval value3197 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix436 (5 : Fin 6) = raw9857 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9857 hH).trans (sound3197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix436 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix436 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix436 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix436 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix436 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix436 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow436, value1739, value3197, value3245, value3246, value3249, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal444 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def boundaryMatrix444 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def boundaryRow444 : Integer.Sparse (Fin 909) := [(0, 1), (1, -490), (2, 640), (3, 3520), (4, 720), (5, -740), (6, 65), (7, 880), (8, 1120), (9, -40), (10, -480), (11, 80), (12, 800), (13, 720), (23, -480), (24, -240), (26, 480), (27, 420), (30, -240), (31, -720), (35, 560), (40, 720), (43, 720), (51, -2160), (52, 800), (55, -1200), (68, 120), (69, 160), (71, 240), (95, 1440), (125, -480), (126, -960), (146, 1440), (208, 720), (236, -480), (237, -240), (238, -240), (308, -240), (508, 720), (538, 720), (546, 720), (727, -240), (738, 720)]

theorem boundarySound444 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow444 (momentVector H) = 0 := by
  have hshape : boundaryMatrix444 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix444 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix444 (0 : Fin 6)) =
      Sparse.eval value1634 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix444 (0 : Fin 6) = raw9720 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9720 hH).trans (sound1634 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix444 (1 : Fin 6)) =
      Sparse.eval value3139 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix444 (1 : Fin 6) = raw9867 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9867 hH).trans (sound3139 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix444 (2 : Fin 6)) =
      Sparse.eval value3143 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix444 (2 : Fin 6) = raw9878 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9878 hH).trans (sound3143 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix444 (3 : Fin 6)) =
      Sparse.eval value3145 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix444 (3 : Fin 6) = raw9881 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9881 hH).trans (sound3145 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix444 (4 : Fin 6)) =
      Sparse.eval value3122 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix444 (4 : Fin 6) = raw9884 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9884 hH).trans (sound3122 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix444 (5 : Fin 6)) =
      Sparse.eval value2967 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix444 (5 : Fin 6) = raw9885 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9885 hH).trans (sound2967 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix444 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix444 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix444 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix444 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix444 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix444 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow444, value1634, value2967, value3122, value3139, value3143, value3145, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal445 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def boundaryMatrix445 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def boundaryRow445 : Integer.Sparse (Fin 909) := [(0, -14), (1, -145), (2, 360), (3, 4400), (4, 640), (5, -760), (6, 115), (7, 1120), (8, 240), (9, -20), (12, 560), (13, 2640), (25, -240), (26, 1360), (34, 560), (35, 2320), (39, 720), (52, 2480), (54, -1440), (60, 560), (64, -480), (69, 160), (71, 80), (82, 80), (99, 1440), (103, 1440), (116, 720), (126, -480), (128, 400), (228, -480), (260, -480), (329, 720), (392, 720), (400, 1440), (492, -240)]

theorem boundarySound445 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow445 (momentVector H) = 0 := by
  have hshape : boundaryMatrix445 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix445 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix445 (0 : Fin 6)) =
      Sparse.eval value1644 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix445 (0 : Fin 6) = raw9719 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9719 hH).trans (sound1644 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix445 (1 : Fin 6)) =
      Sparse.eval value3007 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix445 (1 : Fin 6) = raw9866 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9866 hH).trans (sound3007 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix445 (2 : Fin 6)) =
      Sparse.eval value3007 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix445 (2 : Fin 6) = raw9874 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9874 hH).trans (sound3007 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix445 (3 : Fin 6)) =
      Sparse.eval value3010 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix445 (3 : Fin 6) = raw9875 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9875 hH).trans (sound3010 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix445 (4 : Fin 6)) =
      Sparse.eval value2936 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix445 (4 : Fin 6) = raw9876 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9876 hH).trans (sound2936 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix445 (5 : Fin 6)) =
      Sparse.eval value3011 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix445 (5 : Fin 6) = raw9877 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9877 hH).trans (sound3011 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix445 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix445 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix445 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix445 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix445 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix445 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow445, value1644, value2936, value3007, value3010, value3011, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal446 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def boundaryMatrix446 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def boundaryRow446 : Integer.Sparse (Fin 909) := [(0, 3), (1, -80), (2, 51), (3, 608), (4, 232), (5, -60), (6, 6), (7, 80), (8, 72), (11, 24), (12, 64), (13, 64), (26, 240), (27, 6), (31, -72), (35, 144), (43, 72), (45, 72), (51, -120), (52, 64), (56, -96), (57, 72), (81, -48), (107, 216), (204, 144), (228, -48), (237, -24), (238, -72), (546, 72), (745, 144), (855, 72), (870, 72)]

theorem boundarySound446 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow446 (momentVector H) = 0 := by
  have hshape : boundaryMatrix446 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix446 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix446 (0 : Fin 6)) =
      Sparse.eval value1768 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix446 (0 : Fin 6) = raw9725 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9725 hH).trans (sound1768 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix446 (1 : Fin 6)) =
      Sparse.eval value3369 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix446 (1 : Fin 6) = raw9872 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9872 hH).trans (sound3369 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix446 (2 : Fin 6)) =
      Sparse.eval value3365 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix446 (2 : Fin 6) = raw9897 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9897 hH).trans (sound3365 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix446 (3 : Fin 6)) =
      Sparse.eval value3368 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix446 (3 : Fin 6) = raw9904 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9904 hH).trans (sound3368 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix446 (4 : Fin 6)) =
      Sparse.eval value3346 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix446 (4 : Fin 6) = raw9905 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9905 hH).trans (sound3346 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix446 (5 : Fin 6)) =
      Sparse.eval value3356 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix446 (5 : Fin 6) = raw9906 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9906 hH).trans (sound3356 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix446 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix446 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix446 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix446 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix446 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix446 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow446, value1768, value3346, value3356, value3365, value3368, value3369, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal447 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def boundaryMatrix447 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def boundaryRow447 : Integer.Sparse (Fin 909) := [(0, -29), (1, -5), (2, 660), (3, 5920), (4, 560), (5, -800), (6, 110), (7, 480), (8, 240), (12, 1840), (13, 5520), (26, 880), (33, -480), (34, 640), (35, 2320), (42, 720), (51, -240), (52, 3120), (59, -960), (60, 640), (82, 240), (98, 1440), (99, 720), (102, 1440), (103, 720), (116, 720), (120, 720), (128, 800), (201, -480), (237, -240), (328, 720), (392, 720), (398, 1440), (399, 720)]

theorem boundarySound447 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow447 (momentVector H) = 0 := by
  have hshape : boundaryMatrix447 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix447 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix447 (0 : Fin 6)) =
      Sparse.eval value1720 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix447 (0 : Fin 6) = raw9724 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9724 hH).trans (sound1720 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix447 (1 : Fin 6)) =
      Sparse.eval value3009 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix447 (1 : Fin 6) = raw9871 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9871 hH).trans (sound3009 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix447 (2 : Fin 6)) =
      Sparse.eval value3015 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix447 (2 : Fin 6) = raw9896 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9896 hH).trans (sound3015 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix447 (3 : Fin 6)) =
      Sparse.eval value3016 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix447 (3 : Fin 6) = raw9901 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9901 hH).trans (sound3016 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix447 (4 : Fin 6)) =
      Sparse.eval value2937 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix447 (4 : Fin 6) = raw9902 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9902 hH).trans (sound2937 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix447 (5 : Fin 6)) =
      Sparse.eval value3014 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix447 (5 : Fin 6) = raw9903 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9903 hH).trans (sound3014 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix447 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix447 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix447 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix447 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix447 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix447 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow447, value1720, value2937, value3009, value3014, value3015, value3016, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
