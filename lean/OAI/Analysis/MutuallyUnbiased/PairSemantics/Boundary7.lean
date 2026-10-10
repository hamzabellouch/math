import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical284
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical288
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical291
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical292
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical293
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical294
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical295
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical296
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical297
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical298
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical299
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical300
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical301

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal140 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def boundaryMatrix140 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def boundaryRow140 : Integer.Sparse (Fin 909) := [(0, 149), (1, -2280), (2, 265), (3, 6960), (4, 5280), (5, -40), (7, 480), (12, 1200), (13, 320), (23, -1440), (24, -1440), (25, -3600), (26, 2400), (27, 240), (31, -3600), (35, 560), (44, 4320), (55, -2160), (63, -480), (108, 2160), (123, -720)]

theorem boundarySound140 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow140 (momentVector H) = 0 := by
  have hshape : boundaryMatrix140 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix140 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix140 (0 : Fin 6)) =
      Sparse.eval value3296 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (0 : Fin 6) = raw9102 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9102 hH).trans (sound3296 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix140 (1 : Fin 6)) =
      Sparse.eval value3296 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (1 : Fin 6) = raw9232 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9232 hH).trans (sound3296 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix140 (2 : Fin 6)) =
      Sparse.eval value3042 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (2 : Fin 6) = raw9324 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9324 hH).trans (sound3042 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix140 (3 : Fin 6)) =
      Sparse.eval value3295 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (3 : Fin 6) = raw9334 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9334 hH).trans (sound3295 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix140 (4 : Fin 6)) =
      Sparse.eval value3040 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (4 : Fin 6) = raw9336 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9336 hH).trans (sound3040 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix140 (5 : Fin 6)) =
      Sparse.eval value3208 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (5 : Fin 6) = raw9337 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9337 hH).trans (sound3208 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix140 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix140 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix140 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix140 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix140 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix140 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow140, value3040, value3042, value3208, value3295, value3296, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal144 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def boundaryMatrix144 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def boundaryRow144 : Integer.Sparse (Fin 909) := [(0, 32), (1, -25), (2, 95), (5, -60), (14, 1080), (17, 2160), (23, -1920), (25, -2880), (27, 480), (30, -720), (31, -2160), (63, -240), (108, 2160), (123, -720), (124, -480), (129, 720), (203, 4320), (230, 2160)]

theorem boundarySound144 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow144 (momentVector H) = 0 := by
  have hshape : boundaryMatrix144 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix144 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix144 (0 : Fin 6)) =
      Sparse.eval value3316 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix144 (0 : Fin 6) = raw9111 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9111 hH).trans (sound3316 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix144 (1 : Fin 6)) =
      Sparse.eval value3316 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix144 (1 : Fin 6) = raw9240 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9240 hH).trans (sound3316 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix144 (2 : Fin 6)) =
      Sparse.eval value3315 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix144 (2 : Fin 6) = raw9356 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9356 hH).trans (sound3315 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix144 (3 : Fin 6)) =
      Sparse.eval value3315 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix144 (3 : Fin 6) = raw9365 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9365 hH).trans (sound3315 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix144 (4 : Fin 6)) =
      Sparse.eval value3043 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix144 (4 : Fin 6) = raw9376 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9376 hH).trans (sound3043 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix144 (5 : Fin 6)) =
      Sparse.eval value3155 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix144 (5 : Fin 6) = raw9377 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9377 hH).trans (sound3155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix144 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix144 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix144 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix144 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix144 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix144 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow144, value3043, value3155, value3315, value3316, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal145 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def boundaryMatrix145 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def boundaryRow145 : Integer.Sparse (Fin 909) := [(0, 31), (1, -354), (2, 141), (3, 704), (4, 384), (5, -24), (12, 320), (13, 64), (15, 432), (20, 864), (23, -144), (24, -432), (27, 180), (30, -288), (51, -288), (52, 96), (126, -192), (144, 288), (205, 864), (208, 1728)]

theorem boundarySound145 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow145 (momentVector H) = 0 := by
  have hshape : boundaryMatrix145 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix145 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix145 (0 : Fin 6)) =
      Sparse.eval value3267 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix145 (0 : Fin 6) = raw9109 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9109 hH).trans (sound3267 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix145 (1 : Fin 6)) =
      Sparse.eval value3267 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix145 (1 : Fin 6) = raw9238 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9238 hH).trans (sound3267 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix145 (2 : Fin 6)) =
      Sparse.eval value3266 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix145 (2 : Fin 6) = raw9354 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9354 hH).trans (sound3266 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix145 (3 : Fin 6)) =
      Sparse.eval value3266 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix145 (3 : Fin 6) = raw9363 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9363 hH).trans (sound3266 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix145 (4 : Fin 6)) =
      Sparse.eval value3046 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix145 (4 : Fin 6) = raw9371 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9371 hH).trans (sound3046 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix145 (5 : Fin 6)) =
      Sparse.eval value3193 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix145 (5 : Fin 6) = raw9372 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9372 hH).trans (sound3193 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix145 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix145 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix145 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix145 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix145 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix145 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow145, value3046, value3193, value3266, value3267, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal146 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def boundaryMatrix146 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def boundaryRow146 : Integer.Sparse (Fin 909) := [(0, 23), (1, -885), (2, 210), (3, 3840), (4, 1200), (12, 1840), (13, 960), (16, 1080), (17, 2160), (23, -1080), (26, 480), (35, 240), (38, 1080), (40, 2160), (51, -720), (52, 240), (55, -1800), (125, -480), (140, 2160), (141, 720), (146, 4320)]

theorem boundarySound146 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow146 (momentVector H) = 0 := by
  have hshape : boundaryMatrix146 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix146 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix146 (0 : Fin 6)) =
      Sparse.eval value3138 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix146 (0 : Fin 6) = raw9107 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9107 hH).trans (sound3138 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix146 (1 : Fin 6)) =
      Sparse.eval value3138 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix146 (1 : Fin 6) = raw9236 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9236 hH).trans (sound3138 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix146 (2 : Fin 6)) =
      Sparse.eval value3136 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix146 (2 : Fin 6) = raw9352 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9352 hH).trans (sound3136 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix146 (3 : Fin 6)) =
      Sparse.eval value3136 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix146 (3 : Fin 6) = raw9361 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9361 hH).trans (sound3136 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix146 (4 : Fin 6)) =
      Sparse.eval value2979 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix146 (4 : Fin 6) = raw9367 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9367 hH).trans (sound2979 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix146 (5 : Fin 6)) =
      Sparse.eval value3157 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix146 (5 : Fin 6) = raw9368 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9368 hH).trans (sound3157 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix146 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix146 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix146 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix146 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix146 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix146 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow146, value2979, value3136, value3138, value3157, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal147 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def boundaryMatrix147 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def boundaryRow147 : Integer.Sparse (Fin 909) := [(0, -1), (1, -11), (2, 21), (5, -24), (6, 3), (17, 216), (23, -72), (25, -96), (27, 90), (28, 432), (30, -360), (31, -144), (203, 432), (216, 144), (236, -96), (253, 864)]

theorem boundarySound147 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow147 (momentVector H) = 0 := by
  have hshape : boundaryMatrix147 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix147 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix147 (0 : Fin 6)) =
      Sparse.eval value3463 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix147 (0 : Fin 6) = raw9110 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9110 hH).trans (sound3463 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix147 (1 : Fin 6)) =
      Sparse.eval value3463 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix147 (1 : Fin 6) = raw9239 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9239 hH).trans (sound3463 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix147 (2 : Fin 6)) =
      Sparse.eval value3462 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix147 (2 : Fin 6) = raw9355 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9355 hH).trans (sound3462 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix147 (3 : Fin 6)) =
      Sparse.eval value3462 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix147 (3 : Fin 6) = raw9364 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9364 hH).trans (sound3462 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix147 (4 : Fin 6)) =
      Sparse.eval value3043 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix147 (4 : Fin 6) = raw9374 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9374 hH).trans (sound3043 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix147 (5 : Fin 6)) =
      Sparse.eval value3398 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix147 (5 : Fin 6) = raw9375 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9375 hH).trans (sound3398 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix147 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix147 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix147 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix147 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix147 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix147 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow147, value3043, value3398, value3462, value3463, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal150 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def boundaryMatrix150 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def boundaryRow150 : Integer.Sparse (Fin 909) := [(0, 3), (1, -290), (2, 165), (3, 2080), (4, 640), (5, -60), (7, 320), (12, 1120), (15, 1440), (23, -1680), (24, -1440), (25, -1200), (27, 360), (33, -480), (48, 1440), (51, -480), (55, -960), (68, 60), (124, -480), (126, -480), (137, 1440), (197, -480), (205, 1440), (230, 720)]

theorem boundarySound150 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow150 (momentVector H) = 0 := by
  have hshape : boundaryMatrix150 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix150 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix150 (0 : Fin 6)) =
      Sparse.eval value3289 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix150 (0 : Fin 6) = raw9117 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9117 hH).trans (sound3289 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix150 (1 : Fin 6)) =
      Sparse.eval value1747 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix150 (1 : Fin 6) = raw9386 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9386 hH).trans (sound1747 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix150 (2 : Fin 6)) =
      Sparse.eval value1747 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix150 (2 : Fin 6) = raw9424 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9424 hH).trans (sound1747 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix150 (3 : Fin 6)) =
      Sparse.eval value3092 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix150 (3 : Fin 6) = raw9433 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9433 hH).trans (sound3092 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix150 (4 : Fin 6)) =
      Sparse.eval value3097 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix150 (4 : Fin 6) = raw9436 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9436 hH).trans (sound3097 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix150 (5 : Fin 6)) =
      Sparse.eval value3288 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix150 (5 : Fin 6) = raw9437 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9437 hH).trans (sound3288 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix150 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix150 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix150 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix150 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix150 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix150 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow150, value1747, value3092, value3097, value3288, value3289, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal151 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def boundaryMatrix151 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def boundaryRow151 : Integer.Sparse (Fin 909) := [(0, 17), (1, -725), (2, 260), (3, 4720), (4, 1120), (5, -120), (7, 640), (12, 2000), (13, 560), (16, 720), (23, -2880), (24, -1920), (27, 540), (47, 2880), (51, -960), (55, -1920), (68, 60), (124, -240), (125, -720), (126, -480), (140, 2160), (205, 1440)]

theorem boundarySound151 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow151 (momentVector H) = 0 := by
  have hshape : boundaryMatrix151 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix151 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix151 (0 : Fin 6)) =
      Sparse.eval value3182 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (0 : Fin 6) = raw9129 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9129 hH).trans (sound3182 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix151 (1 : Fin 6)) =
      Sparse.eval value1749 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (1 : Fin 6) = raw9397 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9397 hH).trans (sound1749 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix151 (2 : Fin 6)) =
      Sparse.eval value3090 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (2 : Fin 6) = raw9459 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9459 hH).trans (sound3090 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix151 (3 : Fin 6)) =
      Sparse.eval value3090 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (3 : Fin 6) = raw9480 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9480 hH).trans (sound3090 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix151 (4 : Fin 6)) =
      Sparse.eval value3096 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (4 : Fin 6) = raw9489 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9489 hH).trans (sound3096 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix151 (5 : Fin 6)) =
      Sparse.eval value3181 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (5 : Fin 6) = raw9490 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9490 hH).trans (sound3181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix151 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix151 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix151 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix151 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix151 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix151 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow151, value1749, value3090, value3096, value3181, value3182, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal152 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def boundaryMatrix152 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def boundaryRow152 : Integer.Sparse (Fin 909) := [(0, 9), (1, -160), (2, 40), (3, 1160), (4, 440), (5, -5), (7, 60), (12, 780), (13, 80), (23, -120), (25, -660), (26, 200), (33, -360), (38, 180), (43, 720), (50, 180), (54, -60), (64, -120), (110, 360)]

theorem boundarySound152 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow152 (momentVector H) = 0 := by
  have hshape : boundaryMatrix152 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix152 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix152 (0 : Fin 6)) =
      Sparse.eval value3072 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix152 (0 : Fin 6) = raw9130 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9130 hH).trans (sound3072 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix152 (1 : Fin 6)) =
      Sparse.eval value1785 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix152 (1 : Fin 6) = raw9398 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9398 hH).trans (sound1785 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix152 (2 : Fin 6)) =
      Sparse.eval value3057 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix152 (2 : Fin 6) = raw9460 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9460 hH).trans (sound3057 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix152 (3 : Fin 6)) =
      Sparse.eval value3057 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix152 (3 : Fin 6) = raw9481 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9481 hH).trans (sound3057 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix152 (4 : Fin 6)) =
      Sparse.eval value3056 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix152 (4 : Fin 6) = raw9491 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9491 hH).trans (sound3056 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix152 (5 : Fin 6)) =
      Sparse.eval value3061 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix152 (5 : Fin 6) = raw9492 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9492 hH).trans (sound3061 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix152 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix152 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix152 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix152 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix152 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix152 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow152, value1785, value3056, value3057, value3061, value3072, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal153 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def boundaryMatrix153 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def boundaryRow153 : Integer.Sparse (Fin 909) := [(0, 47), (1, -1150), (2, 350), (3, 4640), (4, 2480), (5, -120), (6, 5), (7, 240), (8, 160), (12, 1120), (21, 1440), (23, -480), (24, -960), (25, -240), (26, 720), (27, 360), (31, -1680), (33, -480), (35, 160), (43, 720), (47, 1440), (48, 720), (51, -2880), (52, 240), (54, -480), (56, -1200), (97, 720), (191, 1440), (209, 1440), (238, -240)]

theorem boundarySound153 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow153 (momentVector H) = 0 := by
  have hshape : boundaryMatrix153 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix153 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix153 (0 : Fin 6)) =
      Sparse.eval value3262 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix153 (0 : Fin 6) = raw9136 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9136 hH).trans (sound3262 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix153 (1 : Fin 6)) =
      Sparse.eval value1793 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix153 (1 : Fin 6) = raw9404 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9404 hH).trans (sound1793 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix153 (2 : Fin 6)) =
      Sparse.eval value3032 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix153 (2 : Fin 6) = raw9474 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9474 hH).trans (sound3032 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix153 (3 : Fin 6)) =
      Sparse.eval value3261 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix153 (3 : Fin 6) = raw9505 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9505 hH).trans (sound3261 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix153 (4 : Fin 6)) =
      Sparse.eval value3260 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix153 (4 : Fin 6) = raw9506 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9506 hH).trans (sound3260 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix153 (5 : Fin 6)) =
      Sparse.eval value3205 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix153 (5 : Fin 6) = raw9507 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9507 hH).trans (sound3205 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix153 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix153 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix153 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix153 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix153 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix153 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow153, value1793, value3032, value3205, value3260, value3261, value3262, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal156 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def boundaryMatrix156 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def boundaryRow156 : Integer.Sparse (Fin 909) := [(0, 9), (1, -206), (2, 31), (3, 1088), (4, 432), (5, -4), (7, 48), (12, 464), (13, 144), (18, 288), (23, -240), (24, -288), (25, -144), (26, 32), (27, 36), (33, -96), (35, 32), (47, 288), (48, 144), (50, 432), (51, -48), (55, -384), (113, 144), (177, 288)]

theorem boundarySound156 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow156 (momentVector H) = 0 := by
  have hshape : boundaryMatrix156 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix156 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix156 (0 : Fin 6)) =
      Sparse.eval value3211 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix156 (0 : Fin 6) = raw9121 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9121 hH).trans (sound3211 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix156 (1 : Fin 6)) =
      Sparse.eval value1786 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix156 (1 : Fin 6) = raw9390 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9390 hH).trans (sound1786 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix156 (2 : Fin 6)) =
      Sparse.eval value3214 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix156 (2 : Fin 6) = raw9447 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9447 hH).trans (sound3214 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix156 (3 : Fin 6)) =
      Sparse.eval value3096 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix156 (3 : Fin 6) = raw9453 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9453 hH).trans (sound3096 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix156 (4 : Fin 6)) =
      Sparse.eval value3090 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix156 (4 : Fin 6) = raw9457 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9457 hH).trans (sound3090 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix156 (5 : Fin 6)) =
      Sparse.eval value3173 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix156 (5 : Fin 6) = raw9458 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9458 hH).trans (sound3173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix156 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix156 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix156 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix156 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix156 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix156 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow156, value1786, value3090, value3096, value3173, value3211, value3214, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal157 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def boundaryMatrix157 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def boundaryRow157 : Integer.Sparse (Fin 909) := [(0, 32), (1, -825), (2, 235), (3, 4960), (4, 1760), (12, 3520), (13, 1440), (25, -1920), (26, 400), (33, -1440), (34, 160), (41, 720), (43, 2880), (50, 1440), (114, 720), (116, 1440)]

theorem boundarySound157 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow157 (momentVector H) = 0 := by
  have hshape : boundaryMatrix157 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix157 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix157 (0 : Fin 6)) =
      Sparse.eval value3073 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix157 (0 : Fin 6) = raw9122 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9122 hH).trans (sound3073 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix157 (1 : Fin 6)) =
      Sparse.eval value1786 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix157 (1 : Fin 6) = raw9391 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9391 hH).trans (sound1786 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix157 (2 : Fin 6)) =
      Sparse.eval value3058 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix157 (2 : Fin 6) = raw9448 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9448 hH).trans (sound3058 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix157 (3 : Fin 6)) =
      Sparse.eval value3061 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix157 (3 : Fin 6) = raw9454 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9454 hH).trans (sound3061 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix157 (4 : Fin 6)) =
      Sparse.eval value3057 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix157 (4 : Fin 6) = raw9460 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9460 hH).trans (sound3057 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix157 (5 : Fin 6)) =
      Sparse.eval value3057 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix157 (5 : Fin 6) = raw9461 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9461 hH).trans (sound3057 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix157 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix157 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix157 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix157 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix157 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix157 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow157, value1786, value3057, value3058, value3061, value3073, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal158 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def boundaryMatrix158 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def boundaryRow158 : Integer.Sparse (Fin 909) := [(0, 29), (1, -340), (2, 105), (3, 1560), (4, 760), (12, 440), (13, 440), (26, 320), (31, -540), (33, -360), (34, 160), (42, 360), (44, 360), (45, 360), (115, 180), (119, 360), (120, 360)]

theorem boundarySound158 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow158 (momentVector H) = 0 := by
  have hshape : boundaryMatrix158 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix158 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix158 (0 : Fin 6)) =
      Sparse.eval value3074 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix158 (0 : Fin 6) = raw9124 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9124 hH).trans (sound3074 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix158 (1 : Fin 6)) =
      Sparse.eval value1793 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix158 (1 : Fin 6) = raw9393 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9393 hH).trans (sound1793 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix158 (2 : Fin 6)) =
      Sparse.eval value3064 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix158 (2 : Fin 6) = raw9450 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9450 hH).trans (sound3064 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix158 (3 : Fin 6)) =
      Sparse.eval value3063 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix158 (3 : Fin 6) = raw9466 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9466 hH).trans (sound3063 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix158 (4 : Fin 6)) =
      Sparse.eval value3062 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix158 (4 : Fin 6) = raw9472 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9472 hH).trans (sound3062 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix158 (5 : Fin 6)) =
      Sparse.eval value3060 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix158 (5 : Fin 6) = raw9473 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9473 hH).trans (sound3060 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix158 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix158 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix158 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix158 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix158 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix158 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow158, value1793, value3060, value3062, value3063, value3064, value3074, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal161 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def boundaryMatrix161 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def boundaryRow161 : Integer.Sparse (Fin 909) := [(0, 116), (1, -1215), (2, 325), (3, 3200), (4, 2000), (5, -60), (7, 240), (8, 160), (12, 800), (13, 160), (22, 1440), (26, 480), (31, -2880), (35, 160), (43, 1440), (46, 1440), (47, 720), (49, 1440), (51, -1680), (56, -240), (97, 720), (107, 1440), (204, 1440), (238, -720)]

theorem boundarySound161 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow161 (momentVector H) = 0 := by
  have hshape : boundaryMatrix161 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix161 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix161 (0 : Fin 6)) =
      Sparse.eval value3248 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix161 (0 : Fin 6) = raw9143 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9143 hH).trans (sound3248 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix161 (1 : Fin 6)) =
      Sparse.eval value1825 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix161 (1 : Fin 6) = raw9411 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9411 hH).trans (sound1825 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix161 (2 : Fin 6)) =
      Sparse.eval value3247 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix161 (2 : Fin 6) = raw9518 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9518 hH).trans (sound3247 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix161 (3 : Fin 6)) =
      Sparse.eval value3250 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix161 (3 : Fin 6) = raw9531 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9531 hH).trans (sound3250 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix161 (4 : Fin 6)) =
      Sparse.eval value3035 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix161 (4 : Fin 6) = raw9537 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9537 hH).trans (sound3035 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix161 (5 : Fin 6)) =
      Sparse.eval value3209 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix161 (5 : Fin 6) = raw9538 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9538 hH).trans (sound3209 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix161 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix161 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix161 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix161 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix161 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix161 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow161, value1825, value3035, value3209, value3247, value3248, value3250, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal162 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def boundaryMatrix162 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def boundaryRow162 : Integer.Sparse (Fin 909) := [(0, 29), (1, -1090), (2, 335), (3, 4880), (4, 2000), (12, 2080), (13, 1200), (25, -2880), (26, 800), (31, -2160), (33, -2400), (34, 320), (38, 720), (39, 1440), (43, 1440), (46, 1440), (50, 1440), (54, -720), (64, -720), (110, 720), (112, 1440), (115, 720), (116, 1440)]

theorem boundarySound162 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow162 (momentVector H) = 0 := by
  have hshape : boundaryMatrix162 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix162 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix162 (0 : Fin 6)) =
      Sparse.eval value3075 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (0 : Fin 6) = raw9144 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9144 hH).trans (sound3075 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix162 (1 : Fin 6)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (1 : Fin 6) = raw9412 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9412 hH).trans (sound1800 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix162 (2 : Fin 6)) =
      Sparse.eval value3066 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (2 : Fin 6) = raw9519 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9519 hH).trans (sound3066 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix162 (3 : Fin 6)) =
      Sparse.eval value3065 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (3 : Fin 6) = raw9532 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9532 hH).trans (sound3065 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix162 (4 : Fin 6)) =
      Sparse.eval value3067 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (4 : Fin 6) = raw9540 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9540 hH).trans (sound3067 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix162 (5 : Fin 6)) =
      Sparse.eval value3069 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (5 : Fin 6) = raw9541 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9541 hH).trans (sound3069 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix162 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix162 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix162 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix162 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix162 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix162 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow162, value1800, value3065, value3066, value3067, value3069, value3075, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal165 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def boundaryMatrix165 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def boundaryRow165 : Integer.Sparse (Fin 909) := [(0, 21), (1, -1115), (2, 610), (3, 5520), (4, 2560), (5, -220), (7, 320), (8, 640), (12, 2160), (13, 1360), (15, 1440), (23, -720), (24, -1440), (25, -960), (27, 360), (31, -1920), (33, -2400), (39, 2880), (42, 2880), (51, -2880), (55, -960), (56, -2400), (64, -480), (68, 60), (97, 1440), (110, 1440), (124, -240), (125, -240), (126, -480), (140, 720), (144, 1440), (145, 1440), (197, -480), (238, -480)]

theorem boundarySound165 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow165 (momentVector H) = 0 := by
  have hshape : boundaryMatrix165 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix165 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix165 (0 : Fin 6)) =
      Sparse.eval value3148 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix165 (0 : Fin 6) = raw9159 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9159 hH).trans (sound3148 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix165 (1 : Fin 6)) =
      Sparse.eval value2968 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix165 (1 : Fin 6) = raw9577 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9577 hH).trans (sound2968 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix165 (2 : Fin 6)) =
      Sparse.eval value2968 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix165 (2 : Fin 6) = raw9613 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9613 hH).trans (sound2968 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix165 (3 : Fin 6)) =
      Sparse.eval value3141 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix165 (3 : Fin 6) = raw9631 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9631 hH).trans (sound3141 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix165 (4 : Fin 6)) =
      Sparse.eval value3142 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix165 (4 : Fin 6) = raw9635 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9635 hH).trans (sound3142 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix165 (5 : Fin 6)) =
      Sparse.eval value3170 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix165 (5 : Fin 6) = raw9636 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9636 hH).trans (sound3170 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix165 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix165 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix165 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix165 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix165 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix165 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow165, value2968, value3141, value3142, value3148, value3170, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal166 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def boundaryMatrix166 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

def boundaryRow166 : Integer.Sparse (Fin 909) := [(0, 37), (1, -406), (2, 139), (3, 1216), (4, 704), (12, 384), (13, 16), (25, -144), (26, 224), (31, -576), (33, -96), (34, 32), (43, 288), (45, 576), (46, 576), (50, 144), (115, 288), (116, 288)]

theorem boundarySound166 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow166 (momentVector H) = 0 := by
  have hshape : boundaryMatrix166 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix166 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix166 (0 : Fin 6)) =
      Sparse.eval value3087 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix166 (0 : Fin 6) = raw9160 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9160 hH).trans (sound3087 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix166 (1 : Fin 6)) =
      Sparse.eval value3082 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix166 (1 : Fin 6) = raw9578 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9578 hH).trans (sound3082 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix166 (2 : Fin 6)) =
      Sparse.eval value3082 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix166 (2 : Fin 6) = raw9614 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9614 hH).trans (sound3082 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix166 (3 : Fin 6)) =
      Sparse.eval value3080 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix166 (3 : Fin 6) = raw9632 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9632 hH).trans (sound3080 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix166 (4 : Fin 6)) =
      Sparse.eval value3081 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix166 (4 : Fin 6) = raw9637 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9637 hH).trans (sound3081 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix166 (5 : Fin 6)) =
      Sparse.eval value3078 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix166 (5 : Fin 6) = raw9638 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9638 hH).trans (sound3078 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix166 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix166 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix166 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix166 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix166 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix166 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow166, value3078, value3080, value3081, value3082, value3087, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
