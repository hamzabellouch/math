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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical253
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical261
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical262
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical263
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical264
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical265
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical266
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

def boundaryOriginal369 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def boundaryMatrix369 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def boundaryRow369 : Integer.Sparse (Fin 909) := [(0, -9), (1, -25), (2, 600), (3, 4480), (4, 1120), (5, -1400), (6, 190), (7, 2400), (8, 480), (9, -40), (11, 640), (24, -480), (26, 1920), (27, 120), (31, -480), (33, -960), (35, 3520), (37, 1440), (51, -480), (52, 2560), (55, -480), (68, 60), (69, 640), (70, 480), (81, -960), (83, 720), (85, 1440), (99, 1440), (123, -480), (124, -240), (126, -480), (197, -480), (228, -3360), (237, -480), (259, -480), (306, -960), (308, -480), (312, 720), (315, 1440), (322, 1440), (517, 2880), (541, 1440), (721, -720), (728, -240), (784, 1440)]

theorem boundarySound369 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow369 (momentVector H) = 0 := by
  have hshape : boundaryMatrix369 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix369 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix369 (0 : Fin 6)) =
      Sparse.eval value3272 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (0 : Fin 6) = raw8325 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8325 hH).trans (sound3272 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix369 (1 : Fin 6)) =
      Sparse.eval value3272 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (1 : Fin 6) = raw9212 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9212 hH).trans (sound3272 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix369 (2 : Fin 6)) =
      Sparse.eval value3468 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (2 : Fin 6) = raw9274 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9274 hH).trans (sound3468 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix369 (3 : Fin 6)) =
      Sparse.eval value3290 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (3 : Fin 6) = raw9318 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9318 hH).trans (sound3290 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix369 (4 : Fin 6)) =
      Sparse.eval value3456 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (4 : Fin 6) = raw9321 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9321 hH).trans (sound3456 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix369 (5 : Fin 6)) =
      Sparse.eval value3291 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (5 : Fin 6) = raw9323 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9323 hH).trans (sound3291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix369 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix369 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix369 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix369 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix369 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix369 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow369, value3272, value3290, value3291, value3456, value3468, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal372 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix372 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryRow372 : Integer.Sparse (Fin 909) := [(0, -2), (1, -63), (2, 107), (3, 1024), (4, 288), (5, -152), (6, 8), (7, 480), (8, 224), (10, -288), (11, 48), (12, 208), (13, 176), (25, -48), (26, 384), (33, -192), (35, 544), (37, 288), (39, 288), (40, 288), (52, 160), (54, -48), (55, -288), (56, -96), (59, -288), (67, 64), (73, 288), (74, 288), (75, 288), (81, -288), (84, 144), (85, 288), (201, -48), (228, -288), (307, -144), (321, 288), (330, 576), (425, 144), (428, 288), (501, 576), (503, 288), (507, 288), (508, 864), (727, -192)]

theorem boundarySound372 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow372 (momentVector H) = 0 := by
  have hshape : boundaryMatrix372 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix372 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix372 (0 : Fin 6)) =
      Sparse.eval value3113 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix372 (0 : Fin 6) = raw8329 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8329 hH).trans (sound3113 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix372 (1 : Fin 6)) =
      Sparse.eval value3113 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix372 (1 : Fin 6) = raw9216 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9216 hH).trans (sound3113 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix372 (2 : Fin 6)) =
      Sparse.eval value3109 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix372 (2 : Fin 6) = raw9349 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9349 hH).trans (sound3109 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix372 (3 : Fin 6)) =
      Sparse.eval value3120 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix372 (3 : Fin 6) = raw9360 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9360 hH).trans (sound3120 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix372 (4 : Fin 6)) =
      Sparse.eval value3054 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix372 (4 : Fin 6) = raw9378 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9378 hH).trans (sound3054 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix372 (5 : Fin 6)) =
      Sparse.eval value3417 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix372 (5 : Fin 6) = raw9380 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9380 hH).trans (sound3417 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix372 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix372 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix372 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix372 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix372 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix372 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow372, value3054, value3109, value3113, value3120, value3417, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal373 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryMatrix373 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryRow373 : Integer.Sparse (Fin 909) := [(0, -11), (1, -15), (2, 415), (3, 4080), (4, 880), (5, -980), (6, 145), (7, 640), (8, 480), (11, 320), (12, 880), (13, 2320), (26, 1280), (33, -960), (35, 2320), (37, 1440), (39, 1440), (40, 1440), (52, 2080), (54, -720), (55, -1440), (56, -480), (81, -960), (82, 320), (83, 720), (85, 1440), (128, 320), (199, -240), (201, -480), (228, -1920), (306, -1440), (312, 1440), (329, 2880), (500, 1440), (517, 1440), (541, 2880), (721, -480), (728, -960), (760, 1440), (764, 1440), (784, 1440), (794, 4320)]

theorem boundarySound373 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow373 (momentVector H) = 0 := by
  have hshape : boundaryMatrix373 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix373 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix373 (0 : Fin 6)) =
      Sparse.eval value3273 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix373 (0 : Fin 6) = raw8330 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8330 hH).trans (sound3273 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix373 (1 : Fin 6)) =
      Sparse.eval value3273 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix373 (1 : Fin 6) = raw9217 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9217 hH).trans (sound3273 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix373 (2 : Fin 6)) =
      Sparse.eval value3290 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix373 (2 : Fin 6) = raw9350 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9350 hH).trans (sound3290 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix373 (3 : Fin 6)) =
      Sparse.eval value3292 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix373 (3 : Fin 6) = raw9362 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9362 hH).trans (sound3292 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix373 (4 : Fin 6)) =
      Sparse.eval value3413 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix373 (4 : Fin 6) = raw9379 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9379 hH).trans (sound3413 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix373 (5 : Fin 6)) =
      Sparse.eval value3465 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix373 (5 : Fin 6) = raw9381 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9381 hH).trans (sound3465 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix373 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix373 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix373 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix373 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix373 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix373 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow373, value3273, value3290, value3292, value3413, value3465, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal374 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def boundaryMatrix374 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def boundaryRow374 : Integer.Sparse (Fin 909) := [(0, 7), (1, -142), (2, 152), (3, 544), (4, 256), (5, -128), (6, 7), (7, 192), (8, 224), (9, -4), (12, 48), (23, -336), (24, -960), (26, 32), (27, 324), (30, -384), (31, -288), (35, 48), (47, 144), (51, -144), (52, 64), (55, -528), (68, 48), (69, 32), (70, 16), (71, 32), (106, 576), (125, -192), (126, -480), (197, -96), (236, -192), (237, -192), (308, -48), (538, 288), (640, 144), (812, 288)]

theorem boundarySound374 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow374 (momentVector H) = 0 := by
  have hshape : boundaryMatrix374 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix374 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix374 (0 : Fin 6)) =
      Sparse.eval value3306 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix374 (0 : Fin 6) = raw8336 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8336 hH).trans (sound3306 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix374 (1 : Fin 6)) =
      Sparse.eval value3310 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix374 (1 : Fin 6) = raw9223 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9223 hH).trans (sound3310 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix374 (2 : Fin 6)) =
      Sparse.eval value3311 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix374 (2 : Fin 6) = raw9546 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9546 hH).trans (sound3311 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix374 (3 : Fin 6)) =
      Sparse.eval value3311 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix374 (3 : Fin 6) = raw9549 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9549 hH).trans (sound3311 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix374 (4 : Fin 6)) =
      Sparse.eval value3181 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix374 (4 : Fin 6) = raw9550 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9550 hH).trans (sound3181 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix374 (5 : Fin 6)) =
      Sparse.eval value3460 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix374 (5 : Fin 6) = raw9551 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9551 hH).trans (sound3460 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix374 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix374 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix374 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix374 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix374 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix374 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow374, value3181, value3306, value3310, value3311, value3460, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal377 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def boundaryMatrix377 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def boundaryRow377 : Integer.Sparse (Fin 909) := [(0, -18), (1, 295), (2, 700), (3, 3040), (4, 160), (5, -1260), (6, 135), (7, 2240), (8, 720), (9, -60), (12, 320), (13, 1440), (23, -240), (26, 160), (27, 60), (35, 3200), (38, 720), (52, 2960), (54, -240), (55, -240), (59, -720), (60, 560), (68, 60), (69, 800), (70, 400), (81, -960), (82, 80), (84, 1440), (98, 720), (125, -720), (126, -480), (128, 400), (201, -240), (228, -480), (237, -240), (260, -480), (287, 720), (306, -480), (308, -240), (323, 1440), (392, 720), (492, -240), (499, 1440), (540, 720), (541, 1440), (728, -240)]

theorem boundarySound377 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow377 (momentVector H) = 0 := by
  have hshape : boundaryMatrix377 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix377 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix377 (0 : Fin 6)) =
      Sparse.eval value3159 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix377 (0 : Fin 6) = raw8339 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8339 hH).trans (sound3159 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix377 (1 : Fin 6)) =
      Sparse.eval value3456 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix377 (1 : Fin 6) = raw9321 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9321 hH).trans (sound3456 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix377 (2 : Fin 6)) =
      Sparse.eval value3456 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix377 (2 : Fin 6) = raw9565 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9565 hH).trans (sound3456 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix377 (3 : Fin 6)) =
      Sparse.eval value3185 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix377 (3 : Fin 6) = raw9568 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9568 hH).trans (sound3185 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix377 (4 : Fin 6)) =
      Sparse.eval value2988 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix377 (4 : Fin 6) = raw9569 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9569 hH).trans (sound2988 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix377 (5 : Fin 6)) =
      Sparse.eval value3188 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix377 (5 : Fin 6) = raw9570 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9570 hH).trans (sound3188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix377 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix377 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix377 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix377 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix377 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix377 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow377, value2988, value3159, value3185, value3188, value3456, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal378 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix378 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryRow378 : Integer.Sparse (Fin 909) := [(0, -24), (1, 360), (2, 715), (3, 4240), (4, 80), (5, -1360), (6, 175), (7, 1760), (8, 800), (10, -720), (11, 80), (12, 1280), (13, 4400), (26, 160), (33, -480), (35, 3920), (41, 720), (52, 3440), (54, -720), (59, -1920), (60, 640), (73, 720), (74, 720), (75, 720), (81, -480), (82, 960), (84, 720), (128, 1360), (199, -960), (201, -1680), (228, -480), (306, -720), (313, 1440), (324, 1440), (392, 720), (399, 720), (500, 720), (502, 1440), (517, 720), (545, 720), (721, -480), (760, 720)]

theorem boundarySound378 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow378 (momentVector H) = 0 := by
  have hshape : boundaryMatrix378 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix378 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix378 (0 : Fin 6)) =
      Sparse.eval value3160 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix378 (0 : Fin 6) = raw8341 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8341 hH).trans (sound3160 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix378 (1 : Fin 6)) =
      Sparse.eval value3413 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix378 (1 : Fin 6) = raw9379 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9379 hH).trans (sound3413 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix378 (2 : Fin 6)) =
      Sparse.eval value3191 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix378 (2 : Fin 6) = raw9583 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9583 hH).trans (sound3191 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix378 (3 : Fin 6)) =
      Sparse.eval value3192 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix378 (3 : Fin 6) = raw9589 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9589 hH).trans (sound3192 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix378 (4 : Fin 6)) =
      Sparse.eval value2991 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix378 (4 : Fin 6) = raw9594 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9594 hH).trans (sound2991 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix378 (5 : Fin 6)) =
      Sparse.eval value3443 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix378 (5 : Fin 6) = raw9595 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9595 hH).trans (sound3443 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix378 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix378 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix378 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix378 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix378 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix378 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow378, value2991, value3160, value3191, value3192, value3413, value3443, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal379 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def boundaryMatrix379 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def boundaryRow379 : Integer.Sparse (Fin 909) := [(0, -31), (1, -330), (2, 410), (3, 6720), (4, 160), (5, -400), (6, 15), (7, 2320), (8, 320), (10, -2640), (12, 3120), (13, 5760), (23, -240), (26, 320), (27, 60), (33, -960), (34, 320), (35, 3680), (38, 1440), (51, -960), (52, 1760), (54, -960), (55, -480), (59, -3360), (60, 640), (72, 720), (73, 720), (74, 1440), (75, 1440), (82, 640), (84, 1440), (128, 640), (199, -720), (201, -720), (228, -480), (273, -480), (311, 2880), (313, 2880), (318, 1440)]

theorem boundarySound379 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow379 (momentVector H) = 0 := by
  have hshape : boundaryMatrix379 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix379 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix379 (0 : Fin 6)) =
      Sparse.eval value2904 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix379 (0 : Fin 6) = raw8073 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8073 hH).trans (sound2904 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix379 (1 : Fin 6)) =
      Sparse.eval value2912 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix379 (1 : Fin 6) = raw8379 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8379 hH).trans (sound2912 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix379 (2 : Fin 6)) =
      Sparse.eval value2912 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix379 (2 : Fin 6) = raw8424 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8424 hH).trans (sound2912 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix379 (3 : Fin 6)) =
      Sparse.eval value3332 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix379 (3 : Fin 6) = raw8430 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8430 hH).trans (sound3332 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix379 (4 : Fin 6)) =
      Sparse.eval value2901 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix379 (4 : Fin 6) = raw8431 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8431 hH).trans (sound2901 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix379 (5 : Fin 6)) =
      Sparse.eval value3435 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix379 (5 : Fin 6) = raw8433 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8433 hH).trans (sound3435 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix379 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix379 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix379 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix379 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix379 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix379 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow379, value2901, value2904, value2912, value3332, value3435, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal381 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def boundaryMatrix381 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def boundaryRow381 : Integer.Sparse (Fin 909) := [(0, -6), (1, -205), (2, 175), (3, 2560), (4, 720), (5, -220), (6, 20), (7, 400), (8, 240), (10, -120), (12, 760), (13, 720), (23, -120), (25, -240), (26, 800), (27, 30), (31, -240), (33, -1440), (34, 160), (35, 560), (36, 720), (39, 1440), (51, -480), (52, 240), (54, -1200), (55, -960), (59, -480), (72, 360), (74, 720), (81, -960), (83, 720), (85, 1440), (199, -360), (228, -960), (273, -240), (311, 720), (312, 1440), (314, 1440), (316, 720), (321, 720), (329, 1440), (330, 2880), (490, -720), (492, -480)]

theorem boundarySound381 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow381 (momentVector H) = 0 := by
  have hshape : boundaryMatrix381 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix381 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix381 (0 : Fin 6)) =
      Sparse.eval value2902 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (0 : Fin 6) = raw8074 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8074 hH).trans (sound2902 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix381 (1 : Fin 6)) =
      Sparse.eval value2916 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (1 : Fin 6) = raw8380 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8380 hH).trans (sound2916 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix381 (2 : Fin 6)) =
      Sparse.eval value2916 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (2 : Fin 6) = raw8425 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8425 hH).trans (sound2916 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix381 (3 : Fin 6)) =
      Sparse.eval value2932 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (3 : Fin 6) = raw8435 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8435 hH).trans (sound2932 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix381 (4 : Fin 6)) =
      Sparse.eval value2906 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (4 : Fin 6) = raw8440 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8440 hH).trans (sound2906 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix381 (5 : Fin 6)) =
      Sparse.eval value3371 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (5 : Fin 6) = raw8442 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8442 hH).trans (sound3371 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix381 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix381 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix381 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix381 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix381 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix381 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow381, value2902, value2906, value2916, value2932, value3371, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal382 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def boundaryMatrix382 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def boundaryRow382 : Integer.Sparse (Fin 909) := [(0, 9), (1, -570), (2, 380), (3, 6240), (4, 2400), (5, -400), (6, 45), (7, 1360), (8, 160), (11, 480), (12, 480), (13, 640), (26, 3040), (35, 3040), (37, 1440), (40, 2880), (52, 1280), (55, -1440), (56, -1440), (67, 160), (73, 720), (75, 1440), (81, -1440), (84, 1440), (85, 2880), (201, -720), (228, -2880), (501, 1440), (503, 1440), (508, 5760), (541, 2880), (794, 2880), (796, -960)]

theorem boundarySound382 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow382 (momentVector H) = 0 := by
  have hshape : boundaryMatrix382 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix382 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix382 (0 : Fin 6)) =
      Sparse.eval value3179 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix382 (0 : Fin 6) = raw8075 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8075 hH).trans (sound3179 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix382 (1 : Fin 6)) =
      Sparse.eval value3299 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix382 (1 : Fin 6) = raw8381 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8381 hH).trans (sound3299 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix382 (2 : Fin 6)) =
      Sparse.eval value3299 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix382 (2 : Fin 6) = raw8426 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8426 hH).trans (sound3299 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix382 (3 : Fin 6)) =
      Sparse.eval value3302 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix382 (3 : Fin 6) = raw8436 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8436 hH).trans (sound3302 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix382 (4 : Fin 6)) =
      Sparse.eval value3348 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix382 (4 : Fin 6) = raw8441 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8441 hH).trans (sound3348 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix382 (5 : Fin 6)) =
      Sparse.eval value3448 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix382 (5 : Fin 6) = raw8444 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8444 hH).trans (sound3448 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix382 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix382 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix382 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix382 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix382 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix382 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow382, value3179, value3299, value3302, value3348, value3448, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal383 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def boundaryMatrix383 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def boundaryRow383 : Integer.Sparse (Fin 909) := [(0, -12), (1, -195), (2, 375), (3, 3920), (4, 800), (5, -900), (6, 130), (7, 880), (8, 480), (10, -240), (11, 480), (12, 1120), (13, 1680), (23, -240), (25, -1920), (26, 1280), (27, 60), (31, -960), (33, -960), (35, 2480), (38, 1440), (39, 2880), (51, -1440), (52, 1920), (54, -3120), (56, -480), (59, -960), (72, 720), (74, 1440), (82, 320), (87, 1440), (89, 2880), (123, -1920), (128, 320), (199, -960), (201, -480), (226, -1440), (228, -1440), (237, -480), (306, -480), (313, 1440), (315, 2880), (498, 1440), (505, 1440), (507, 5760), (540, 2880), (721, -1440), (723, -960), (764, 2880)]

theorem boundarySound383 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow383 (momentVector H) = 0 := by
  have hshape : boundaryMatrix383 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix383 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix383 (0 : Fin 6)) =
      Sparse.eval value3178 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix383 (0 : Fin 6) = raw8076 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8076 hH).trans (sound3178 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix383 (1 : Fin 6)) =
      Sparse.eval value3323 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix383 (1 : Fin 6) = raw8382 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8382 hH).trans (sound3323 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix383 (2 : Fin 6)) =
      Sparse.eval value3323 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix383 (2 : Fin 6) = raw8427 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8427 hH).trans (sound3323 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix383 (3 : Fin 6)) =
      Sparse.eval value3325 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix383 (3 : Fin 6) = raw8437 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8437 hH).trans (sound3325 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix383 (4 : Fin 6)) =
      Sparse.eval value3449 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix383 (4 : Fin 6) = raw8443 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8443 hH).trans (sound3449 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix383 (5 : Fin 6)) =
      Sparse.eval value3326 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix383 (5 : Fin 6) = raw8445 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8445 hH).trans (sound3326 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix383 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix383 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix383 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix383 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix383 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix383 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow383, value3178, value3323, value3325, value3326, value3449, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal384 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def boundaryMatrix384 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def boundaryRow384 : Integer.Sparse (Fin 909) := [(0, -13), (1, -150), (2, 375), (3, 3840), (4, 800), (5, -700), (6, 30), (7, 2960), (8, 960), (10, -240), (12, 160), (13, 80), (23, -240), (24, -480), (25, -480), (26, 1760), (27, 60), (35, 3680), (38, 720), (51, -480), (52, 1120), (54, -720), (55, -480), (59, -480), (64, -960), (67, 800), (72, 720), (73, 1440), (81, -1920), (84, 1440), (104, 1440), (199, -240), (228, -480), (271, -480), (318, 1440), (425, 1440), (499, 1440)]

theorem boundarySound384 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow384 (momentVector H) = 0 := by
  have hshape : boundaryMatrix384 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix384 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix384 (0 : Fin 6)) =
      Sparse.eval value3102 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix384 (0 : Fin 6) = raw8078 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8078 hH).trans (sound3102 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix384 (1 : Fin 6)) =
      Sparse.eval value3105 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix384 (1 : Fin 6) = raw8383 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8383 hH).trans (sound3105 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix384 (2 : Fin 6)) =
      Sparse.eval value3428 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix384 (2 : Fin 6) = raw8432 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8432 hH).trans (sound3428 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix384 (3 : Fin 6)) =
      Sparse.eval value3428 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix384 (3 : Fin 6) = raw8449 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8449 hH).trans (sound3428 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix384 (4 : Fin 6)) =
      Sparse.eval value3019 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix384 (4 : Fin 6) = raw8450 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8450 hH).trans (sound3019 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix384 (5 : Fin 6)) =
      Sparse.eval value3201 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix384 (5 : Fin 6) = raw8451 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8451 hH).trans (sound3201 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix384 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix384 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix384 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix384 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix384 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix384 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow384, value3019, value3102, value3105, value3201, value3428, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal385 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def boundaryMatrix385 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def boundaryRow385 : Integer.Sparse (Fin 909) := [(0, -9), (1, -280), (2, 565), (3, 7040), (4, 2160), (5, -860), (6, 70), (7, 3120), (8, 800), (11, 640), (12, 80), (13, 160), (26, 3920), (33, -480), (34, 320), (35, 4800), (37, 720), (52, 1920), (56, -240), (67, 640), (73, 720), (81, -2880), (83, 720), (84, 1440), (85, 2880), (201, -240), (228, -4320), (275, -480), (317, 1440), (428, 1440), (460, 1440), (517, 1440), (709, 1440)]

theorem boundarySound385 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow385 (momentVector H) = 0 := by
  have hshape : boundaryMatrix385 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix385 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix385 (0 : Fin 6)) =
      Sparse.eval value3151 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (0 : Fin 6) = raw8080 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8080 hH).trans (sound3151 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix385 (1 : Fin 6)) =
      Sparse.eval value3194 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (1 : Fin 6) = raw8384 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8384 hH).trans (sound3194 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix385 (2 : Fin 6)) =
      Sparse.eval value3348 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (2 : Fin 6) = raw8441 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8441 hH).trans (sound3348 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix385 (3 : Fin 6)) =
      Sparse.eval value3202 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (3 : Fin 6) = raw8453 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8453 hH).trans (sound3202 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix385 (4 : Fin 6)) =
      Sparse.eval value3021 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (4 : Fin 6) = raw8455 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8455 hH).trans (sound3021 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix385 (5 : Fin 6)) =
      Sparse.eval value3430 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (5 : Fin 6) = raw8457 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8457 hH).trans (sound3430 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix385 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix385 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix385 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix385 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix385 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix385 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow385, value3021, value3151, value3194, value3202, value3348, value3430, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal386 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def boundaryMatrix386 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def boundaryRow386 : Integer.Sparse (Fin 909) := [(0, -12), (1, -20), (2, 615), (3, 4880), (4, 1120), (5, -1320), (6, 175), (7, 1760), (8, 720), (10, -240), (11, 640), (12, 320), (13, 1040), (24, -240), (26, 1840), (27, 60), (31, -480), (33, -480), (35, 3840), (41, 720), (51, -960), (52, 3200), (56, -480), (59, -960), (60, 160), (73, 720), (81, -480), (82, 80), (84, 720), (85, 1440), (99, 1440), (103, 1440), (123, -960), (128, 240), (201, -240), (228, -3120), (237, -480), (306, -480), (313, 720), (315, 1440), (324, 1440), (502, 720), (517, 1440), (545, 1440), (721, -720)]

theorem boundarySound386 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow386 (momentVector H) = 0 := by
  have hshape : boundaryMatrix386 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix386 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix386 (0 : Fin 6)) =
      Sparse.eval value3191 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix386 (0 : Fin 6) = raw8081 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8081 hH).trans (sound3191 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix386 (1 : Fin 6)) =
      Sparse.eval value3269 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix386 (1 : Fin 6) = raw8385 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8385 hH).trans (sound3269 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix386 (2 : Fin 6)) =
      Sparse.eval value3449 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix386 (2 : Fin 6) = raw8443 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8443 hH).trans (sound3449 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix386 (3 : Fin 6)) =
      Sparse.eval value3274 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix386 (3 : Fin 6) = raw8454 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8454 hH).trans (sound3274 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix386 (4 : Fin 6)) =
      Sparse.eval value3424 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix386 (4 : Fin 6) = raw8456 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8456 hH).trans (sound3424 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix386 (5 : Fin 6)) =
      Sparse.eval value3275 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix386 (5 : Fin 6) = raw8458 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8458 hH).trans (sound3275 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix386 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix386 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix386 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix386 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix386 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix386 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow386, value3191, value3269, value3274, value3275, value3424, value3449, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal387 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix387 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryRow387 : Integer.Sparse (Fin 909) := [(0, -2), (1, -39), (2, 93), (3, 976), (4, 352), (5, -116), (6, 6), (7, 272), (8, 192), (10, -144), (12, 112), (13, 192), (26, 416), (33, -288), (34, 64), (35, 256), (36, 144), (40, 288), (52, 64), (54, -144), (55, -144), (56, -192), (59, -192), (72, 144), (75, 288), (81, -384), (83, 288), (85, 576), (199, -48), (228, -384), (271, -96), (307, -288), (316, 288), (330, 576), (426, 288), (428, 576), (498, 288), (501, 576), (508, 1152), (727, -192)]

theorem boundarySound387 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow387 (momentVector H) = 0 := by
  have hshape : boundaryMatrix387 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix387 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix387 (0 : Fin 6)) =
      Sparse.eval value3101 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix387 (0 : Fin 6) = raw8083 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8083 hH).trans (sound3101 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix387 (1 : Fin 6)) =
      Sparse.eval value3107 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix387 (1 : Fin 6) = raw8387 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8387 hH).trans (sound3107 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix387 (2 : Fin 6)) =
      Sparse.eval value3114 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix387 (2 : Fin 6) = raw8462 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8462 hH).trans (sound3114 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix387 (3 : Fin 6)) =
      Sparse.eval value3114 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix387 (3 : Fin 6) = raw8464 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8464 hH).trans (sound3114 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix387 (4 : Fin 6)) =
      Sparse.eval value3029 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix387 (4 : Fin 6) = raw8466 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8466 hH).trans (sound3029 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix387 (5 : Fin 6)) =
      Sparse.eval value3415 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix387 (5 : Fin 6) = raw8468 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8468 hH).trans (sound3415 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix387 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix387 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix387 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix387 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix387 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix387 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow387, value3029, value3101, value3107, value3114, value3415, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal388 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryMatrix388 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryRow388 : Integer.Sparse (Fin 909) := [(0, -13), (1, 80), (2, 605), (3, 4480), (4, 800), (5, -1220), (6, 170), (7, 1200), (8, 640), (12, 720), (13, 2880), (26, 960), (35, 3040), (38, 720), (40, 1440), (52, 2720), (54, -480), (55, -720), (56, -960), (59, -480), (60, 160), (81, -960), (82, 560), (84, 1440), (85, 2880), (128, 560), (199, -480), (201, -960), (228, -1440), (306, -720), (323, 1440), (329, 2880), (499, 720), (540, 1440), (541, 2880), (728, -960), (760, 1440), (794, 5760)]

theorem boundarySound388 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow388 (momentVector H) = 0 := by
  have hshape : boundaryMatrix388 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix388 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix388 (0 : Fin 6)) =
      Sparse.eval value3185 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix388 (0 : Fin 6) = raw8084 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8084 hH).trans (sound3185 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix388 (1 : Fin 6)) =
      Sparse.eval value3270 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix388 (1 : Fin 6) = raw8388 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8388 hH).trans (sound3270 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix388 (2 : Fin 6)) =
      Sparse.eval value3276 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix388 (2 : Fin 6) = raw8463 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8463 hH).trans (sound3276 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix388 (3 : Fin 6)) =
      Sparse.eval value3276 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix388 (3 : Fin 6) = raw8465 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8465 hH).trans (sound3276 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix388 (4 : Fin 6)) =
      Sparse.eval value3412 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix388 (4 : Fin 6) = raw8467 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8467 hH).trans (sound3412 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix388 (5 : Fin 6)) =
      Sparse.eval value3451 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix388 (5 : Fin 6) = raw8469 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8469 hH).trans (sound3451 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix388 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix388 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix388 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix388 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix388 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix388 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow388, value3185, value3270, value3276, value3412, value3451, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal389 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def boundaryMatrix389 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def boundaryRow389 : Integer.Sparse (Fin 909) := [(0, -5), (1, 76), (2, 127), (3, 656), (5, -216), (6, 24), (7, 384), (8, 128), (10, -48), (12, 112), (13, 512), (23, -48), (27, 12), (35, 720), (51, -96), (52, 544), (54, -192), (59, -240), (60, 160), (62, -192), (72, 144), (73, 288), (81, -192), (82, 32), (98, 288), (128, 112), (199, -96), (201, -96), (237, -96), (267, -96), (284, 288), (306, -96), (392, 288), (499, 288), (502, 288)]

theorem boundarySound389 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow389 (momentVector H) = 0 := by
  have hshape : boundaryMatrix389 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix389 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix389 (0 : Fin 6)) =
      Sparse.eval value3150 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix389 (0 : Fin 6) = raw8101 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8101 hH).trans (sound3150 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix389 (1 : Fin 6)) =
      Sparse.eval value3424 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix389 (1 : Fin 6) = raw8456 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8456 hH).trans (sound3424 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix389 (2 : Fin 6)) =
      Sparse.eval value3424 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix389 (2 : Fin 6) = raw8509 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8509 hH).trans (sound3424 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix389 (3 : Fin 6)) =
      Sparse.eval value3162 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix389 (3 : Fin 6) = raw8510 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8510 hH).trans (sound3162 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix389 (4 : Fin 6)) =
      Sparse.eval value2953 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix389 (4 : Fin 6) = raw8511 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8511 hH).trans (sound2953 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix389 (5 : Fin 6)) =
      Sparse.eval value3163 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix389 (5 : Fin 6) = raw8512 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8512 hH).trans (sound3163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix389 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix389 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix389 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix389 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix389 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix389 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow389, value2953, value3150, value3162, value3163, value3424, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
