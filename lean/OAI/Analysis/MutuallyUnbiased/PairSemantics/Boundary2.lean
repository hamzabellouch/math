import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical105
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical108
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical115
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical228
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical267
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical268
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical269
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical277
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical284
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical293
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical294
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical295
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical296
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical297
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical302
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical305
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical308
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical309
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical312
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical313

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal33 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def boundaryMatrix33 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def boundaryRow33 : Integer.Sparse (Fin 909) := [(0, 56), (1, -675), (2, 305), (3, 1760), (4, 1120), (5, -80), (7, 160), (8, 240), (12, 440), (24, -480), (26, 160), (27, 180), (30, -240), (31, -720), (45, 360), (46, 360), (51, -480), (56, -240)]

theorem boundarySound33 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow33 (momentVector H) = 0 := by
  have hshape : boundaryMatrix33 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix33 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix33 (0 : Fin 6)) =
      Sparse.eval value3044 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix33 (0 : Fin 6) = raw8878 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8878 hH).trans (sound3044 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix33 (1 : Fin 6)) =
      Sparse.eval value3339 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix33 (1 : Fin 6) = raw9763 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9763 hH).trans (sound3339 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix33 (2 : Fin 6)) =
      Sparse.eval value2449 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix33 (2 : Fin 6) = raw9873 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9873 hH).trans (sound2449 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix33 (3 : Fin 6)) =
      Sparse.eval value3082 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix33 (3 : Fin 6) = raw9883 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9883 hH).trans (sound3082 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix33 (4 : Fin 6)) =
      Sparse.eval value3083 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix33 (4 : Fin 6) = raw9892 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9892 hH).trans (sound3083 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix33 (5 : Fin 6)) =
      Sparse.eval value2889 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix33 (5 : Fin 6) = raw9893 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9893 hH).trans (sound2889 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix33 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix33 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix33 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix33 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix33 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix33 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow33, value2449, value2889, value3044, value3082, value3083, value3339, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal34 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def boundaryMatrix34 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def boundaryRow34 : Integer.Sparse (Fin 909) := [(0, 67), (1, -1010), (2, 185), (3, 3200), (4, 960), (5, -60), (7, 80), (8, 160), (12, 1040), (13, 1200), (25, -960), (26, 640), (31, -960), (33, -960), (38, 720), (39, 1440), (54, -720)]

theorem boundarySound34 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow34 (momentVector H) = 0 := by
  have hshape : boundaryMatrix34 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix34 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix34 (0 : Fin 6)) =
      Sparse.eval value3017 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (0 : Fin 6) = raw3470 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3470 hH).trans (sound3017 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix34 (1 : Fin 6)) =
      Sparse.eval value3011 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (1 : Fin 6) = raw7272 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7272 hH).trans (sound3011 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix34 (2 : Fin 6)) =
      Sparse.eval value3012 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (2 : Fin 6) = raw7335 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7335 hH).trans (sound3012 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix34 (3 : Fin 6)) =
      Sparse.eval value3441 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (3 : Fin 6) = raw7340 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7340 hH).trans (sound3441 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix34 (4 : Fin 6)) =
      Sparse.eval value3441 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (4 : Fin 6) = raw7341 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7341 hH).trans (sound3441 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix34 (5 : Fin 6)) =
      Sparse.eval value3081 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (5 : Fin 6) = raw7342 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7342 hH).trans (sound3081 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix34 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix34 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix34 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix34 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix34 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix34 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow34, value3011, value3012, value3017, value3081, value3441, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal35 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def boundaryMatrix35 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def boundaryRow35 : Integer.Sparse (Fin 909) := [(0, 8), (1, -151), (2, 109), (3, 624), (4, 192), (5, -44), (7, 48), (8, 160), (12, 96), (23, -48), (25, -96), (26, 128), (27, 36), (30, -96), (31, -192), (33, -384), (36, 144), (39, 288), (40, 288), (51, -192), (54, -240), (55, -144)]

theorem boundarySound35 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow35 (momentVector H) = 0 := by
  have hshape : boundaryMatrix35 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix35 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix35 (0 : Fin 6)) =
      Sparse.eval value2964 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix35 (0 : Fin 6) = raw3369 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3369 hH).trans (sound2964 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix35 (1 : Fin 6)) =
      Sparse.eval value2971 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix35 (1 : Fin 6) = raw7262 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7262 hH).trans (sound2971 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix35 (2 : Fin 6)) =
      Sparse.eval value3012 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix35 (2 : Fin 6) = raw7292 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7292 hH).trans (sound3012 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix35 (3 : Fin 6)) =
      Sparse.eval value2965 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix35 (3 : Fin 6) = raw7303 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7303 hH).trans (sound2965 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix35 (4 : Fin 6)) =
      Sparse.eval value2965 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix35 (4 : Fin 6) = raw7307 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7307 hH).trans (sound2965 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix35 (5 : Fin 6)) =
      Sparse.eval value3393 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix35 (5 : Fin 6) = raw7309 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7309 hH).trans (sound3393 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix35 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix35 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix35 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix35 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix35 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix35 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow35, value2964, value2965, value2971, value3012, value3393, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal36 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def boundaryMatrix36 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def boundaryRow36 : Integer.Sparse (Fin 909) := [(0, 19), (1, -288), (2, 91), (3, 928), (4, 512), (5, -12), (7, 16), (8, 32), (12, 48), (13, 32), (26, 368), (37, 144), (40, 288), (56, -144), (57, 288)]

theorem boundarySound36 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow36 (momentVector H) = 0 := by
  have hshape : boundaryMatrix36 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix36 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix36 (0 : Fin 6)) =
      Sparse.eval value3161 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix36 (0 : Fin 6) = raw3370 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3370 hH).trans (sound3161 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix36 (1 : Fin 6)) =
      Sparse.eval value3353 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix36 (1 : Fin 6) = raw7263 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7263 hH).trans (sound3353 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix36 (2 : Fin 6)) =
      Sparse.eval value3354 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix36 (2 : Fin 6) = raw7293 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7293 hH).trans (sound3354 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix36 (3 : Fin 6)) =
      Sparse.eval value3356 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix36 (3 : Fin 6) = raw7304 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7304 hH).trans (sound3356 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix36 (4 : Fin 6)) =
      Sparse.eval value3373 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix36 (4 : Fin 6) = raw7308 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7308 hH).trans (sound3373 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix36 (5 : Fin 6)) =
      Sparse.eval value3442 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix36 (5 : Fin 6) = raw7310 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7310 hH).trans (sound3442 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix36 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix36 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix36 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix36 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix36 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix36 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow36, value3161, value3353, value3354, value3356, value3373, value3442, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal37 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def boundaryMatrix37 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def boundaryRow37 : Integer.Sparse (Fin 909) := [(0, 37), (1, -580), (2, 255), (3, 1920), (4, 320), (5, -80), (7, 80), (8, 320), (12, 720), (13, 880), (23, -120), (26, 160), (27, 90), (30, -240), (38, 360), (40, 720), (51, -480), (54, -240), (55, -360)]

theorem boundarySound37 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow37 (momentVector H) = 0 := by
  have hshape : boundaryMatrix37 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix37 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix37 (0 : Fin 6)) =
      Sparse.eval value2970 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix37 (0 : Fin 6) = raw3374 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3374 hH).trans (sound2970 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix37 (1 : Fin 6)) =
      Sparse.eval value2974 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix37 (1 : Fin 6) = raw7267 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7267 hH).trans (sound2974 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix37 (2 : Fin 6)) =
      Sparse.eval value2967 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix37 (2 : Fin 6) = raw7297 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7297 hH).trans (sound2967 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix37 (3 : Fin 6)) =
      Sparse.eval value2967 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix37 (3 : Fin 6) = raw7320 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7320 hH).trans (sound2967 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix37 (4 : Fin 6)) =
      Sparse.eval value3337 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix37 (4 : Fin 6) = raw7322 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7322 hH).trans (sound3337 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix37 (5 : Fin 6)) =
      Sparse.eval value3437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix37 (5 : Fin 6) = raw7323 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7323 hH).trans (sound3437 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix37 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix37 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix37 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix37 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix37 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix37 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow37, value2967, value2970, value2974, value3337, value3437, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal38 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def boundaryMatrix38 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def boundaryRow38 : Integer.Sparse (Fin 909) := [(0, 16), (1, -255), (2, 93), (3, 896), (4, 304), (12, 384), (13, 448), (26, 112), (31, -192), (33, -192), (41, 144), (42, 288)]

theorem boundarySound38 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow38 (momentVector H) = 0 := by
  have hshape : boundaryMatrix38 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix38 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix38 (0 : Fin 6)) =
      Sparse.eval value3018 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix38 (0 : Fin 6) = raw3377 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3377 hH).trans (sound3018 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix38 (1 : Fin 6)) =
      Sparse.eval value3014 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix38 (1 : Fin 6) = raw7268 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7268 hH).trans (sound3014 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix38 (2 : Fin 6)) =
      Sparse.eval value3013 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix38 (2 : Fin 6) = raw7298 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7298 hH).trans (sound3013 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix38 (3 : Fin 6)) =
      Sparse.eval value3440 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix38 (3 : Fin 6) = raw7321 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7321 hH).trans (sound3440 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix38 (4 : Fin 6)) =
      Sparse.eval value3441 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix38 (4 : Fin 6) = raw7324 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7324 hH).trans (sound3441 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix38 (5 : Fin 6)) =
      Sparse.eval value3083 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix38 (5 : Fin 6) = raw7325 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7325 hH).trans (sound3083 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix38 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix38 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix38 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix38 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix38 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix38 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow38, value3013, value3014, value3018, value3083, value3440, value3441, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal39 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def boundaryMatrix39 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def boundaryRow39 : Integer.Sparse (Fin 909) := [(0, 17), (1, -309), (2, 76), (3, 1008), (4, 480), (26, 528), (53, 144), (57, 144)]

theorem boundarySound39 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow39 (momentVector H) = 0 := by
  have hshape : boundaryMatrix39 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix39 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix39 (0 : Fin 6)) =
      Sparse.eval value3203 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix39 (0 : Fin 6) = raw3699 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3699 hH).trans (sound3203 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix39 (1 : Fin 6)) =
      Sparse.eval value3355 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix39 (1 : Fin 6) = raw7474 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7474 hH).trans (sound3355 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix39 (2 : Fin 6)) =
      Sparse.eval value3355 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix39 (2 : Fin 6) = raw7489 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7489 hH).trans (sound3355 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix39 (3 : Fin 6)) =
      Sparse.eval value3356 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix39 (3 : Fin 6) = raw7491 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7491 hH).trans (sound3356 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix39 (4 : Fin 6)) =
      Sparse.eval value3374 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix39 (4 : Fin 6) = raw7493 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7493 hH).trans (sound3374 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix39 (5 : Fin 6)) =
      Sparse.eval value3434 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix39 (5 : Fin 6) = raw7494 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7494 hH).trans (sound3434 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix39 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix39 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix39 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix39 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix39 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix39 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow39, value3203, value3355, value3356, value3374, value3434, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal40 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def boundaryMatrix40 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def boundaryRow40 : Integer.Sparse (Fin 909) := [(0, 9), (1, -179), (2, 82), (3, 720), (4, 288), (5, -32), (7, 64), (8, 96), (12, 160), (13, 128), (24, -96), (26, 176), (27, 36), (30, -48), (31, -96), (33, -192), (37, 144), (39, 144), (40, 144), (42, 144), (51, -192), (55, -144), (56, -96)]

theorem boundarySound40 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow40 (momentVector H) = 0 := by
  have hshape : boundaryMatrix40 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix40 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix40 (0 : Fin 6)) =
      Sparse.eval value2977 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix40 (0 : Fin 6) = raw3700 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3700 hH).trans (sound2977 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix40 (1 : Fin 6)) =
      Sparse.eval value2972 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix40 (1 : Fin 6) = raw7475 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7475 hH).trans (sound2972 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix40 (2 : Fin 6)) =
      Sparse.eval value2973 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix40 (2 : Fin 6) = raw7490 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7490 hH).trans (sound2973 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix40 (3 : Fin 6)) =
      Sparse.eval value3455 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix40 (3 : Fin 6) = raw7492 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7492 hH).trans (sound3455 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix40 (4 : Fin 6)) =
      Sparse.eval value3457 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix40 (4 : Fin 6) = raw7495 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7495 hH).trans (sound3457 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix40 (5 : Fin 6)) =
      Sparse.eval value3044 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix40 (5 : Fin 6) = raw7496 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7496 hH).trans (sound3044 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix40 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix40 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix40 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix40 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix40 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix40 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow40, value2972, value2973, value2977, value3044, value3455, value3457, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal41 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def boundaryMatrix41 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def boundaryRow41 : Integer.Sparse (Fin 909) := [(0, 1), (1, -145), (2, 70), (3, 1200), (4, 400), (5, -10), (7, 80), (12, 720), (14, 360), (15, 1440), (23, -840), (24, -480), (25, -840), (27, 120), (33, -480), (36, 720), (48, 720), (51, -240), (54, -240), (55, -240)]

theorem boundarySound41 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow41 (momentVector H) = 0 := by
  have hshape : boundaryMatrix41 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix41 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix41 (0 : Fin 6)) =
      Sparse.eval value3154 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix41 (0 : Fin 6) = raw9116 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9116 hH).trans (sound3154 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix41 (1 : Fin 6)) =
      Sparse.eval value2743 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix41 (1 : Fin 6) = raw9385 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9385 hH).trans (sound2743 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix41 (2 : Fin 6)) =
      Sparse.eval value2743 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix41 (2 : Fin 6) = raw9423 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9423 hH).trans (sound2743 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix41 (3 : Fin 6)) =
      Sparse.eval value3166 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix41 (3 : Fin 6) = raw9432 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9432 hH).trans (sound3166 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix41 (4 : Fin 6)) =
      Sparse.eval value3030 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix41 (4 : Fin 6) = raw9435 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9435 hH).trans (sound3030 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix41 (5 : Fin 6)) =
      Sparse.eval value3097 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix41 (5 : Fin 6) = raw9436 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9436 hH).trans (sound3097 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix41 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix41 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix41 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix41 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix41 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix41 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow41, value2743, value3030, value3097, value3154, value3166, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal42 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 0, 0]]

def boundaryMatrix42 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 0, 0]]

def boundaryRow42 : Integer.Sparse (Fin 909) := [(0, 83), (1, -1010), (2, 145), (3, 5280), (4, 1920), (12, 1760), (13, 720), (15, 1440), (16, 720), (18, 2880), (23, -480), (24, -480), (25, -720), (27, 60), (38, 1440), (50, 720), (55, -480)]

theorem boundarySound42 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow42 (momentVector H) = 0 := by
  have hshape : boundaryMatrix42 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix42 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix42 (0 : Fin 6)) =
      Sparse.eval value3156 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix42 (0 : Fin 6) = raw9128 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9128 hH).trans (sound3156 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix42 (1 : Fin 6)) =
      Sparse.eval value2613 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix42 (1 : Fin 6) = raw9396 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9396 hH).trans (sound2613 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix42 (2 : Fin 6)) =
      Sparse.eval value3173 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix42 (2 : Fin 6) = raw9458 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9458 hH).trans (sound3173 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix42 (3 : Fin 6)) =
      Sparse.eval value3173 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix42 (3 : Fin 6) = raw9479 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9479 hH).trans (sound3173 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix42 (4 : Fin 6)) =
      Sparse.eval value3425 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix42 (4 : Fin 6) = raw9488 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9488 hH).trans (sound3425 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix42 (5 : Fin 6)) =
      Sparse.eval value3096 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix42 (5 : Fin 6) = raw9489 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9489 hH).trans (sound3096 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix42 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix42 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix42 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix42 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix42 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix42 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow42, value2613, value3096, value3156, value3173, value3425, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal43 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def boundaryMatrix43 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def boundaryRow43 : Integer.Sparse (Fin 909) := [(0, 88), (1, -1245), (2, 255), (3, 4080), (4, 1760), (5, -20), (7, 80), (8, 80), (12, 880), (15, 720), (18, 720), (19, 1440), (21, 1440), (23, -240), (24, -1440), (25, -240), (26, 480), (27, 180), (31, -960), (37, 1440), (47, 720), (48, 720), (51, -480), (56, -480)]

theorem boundarySound43 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow43 (momentVector H) = 0 := by
  have hshape : boundaryMatrix43 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix43 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix43 (0 : Fin 6)) =
      Sparse.eval value3153 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix43 (0 : Fin 6) = raw9138 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9138 hH).trans (sound3153 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix43 (1 : Fin 6)) =
      Sparse.eval value2584 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix43 (1 : Fin 6) = raw9406 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9406 hH).trans (sound2584 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix43 (2 : Fin 6)) =
      Sparse.eval value3198 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix43 (2 : Fin 6) = raw9476 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9476 hH).trans (sound3198 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix43 (3 : Fin 6)) =
      Sparse.eval value3205 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix43 (3 : Fin 6) = raw9507 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9507 hH).trans (sound3205 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix43 (4 : Fin 6)) =
      Sparse.eval value3032 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix43 (4 : Fin 6) = raw9509 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9509 hH).trans (sound3032 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix43 (5 : Fin 6)) =
      Sparse.eval value3432 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix43 (5 : Fin 6) = raw9510 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9510 hH).trans (sound3432 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix43 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix43 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix43 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix43 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix43 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix43 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow43, value2584, value3032, value3153, value3198, value3205, value3432, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal44 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def boundaryMatrix44 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def boundaryRow44 : Integer.Sparse (Fin 909) := [(0, 79), (1, -810), (2, 195), (3, 1040), (4, 1320), (5, -20), (7, 80), (8, 120), (12, 160), (17, 360), (20, 720), (23, -120), (24, -600), (25, -360), (26, 80), (27, 90), (30, -360), (31, -720), (44, 720), (45, 720), (48, 360), (51, -120)]

theorem boundarySound44 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow44 (momentVector H) = 0 := by
  have hshape : boundaryMatrix44 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix44 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix44 (0 : Fin 6)) =
      Sparse.eval value3152 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix44 (0 : Fin 6) = raw9134 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9134 hH).trans (sound3152 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix44 (1 : Fin 6)) =
      Sparse.eval value2630 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix44 (1 : Fin 6) = raw9402 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9402 hH).trans (sound2630 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix44 (2 : Fin 6)) =
      Sparse.eval value3199 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix44 (2 : Fin 6) = raw9469 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9469 hH).trans (sound3199 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix44 (3 : Fin 6)) =
      Sparse.eval value3204 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix44 (3 : Fin 6) = raw9498 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9498 hH).trans (sound3204 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix44 (4 : Fin 6)) =
      Sparse.eval value3031 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix44 (4 : Fin 6) = raw9500 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9500 hH).trans (sound3031 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix44 (5 : Fin 6)) =
      Sparse.eval value3433 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix44 (5 : Fin 6) = raw9501 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9501 hH).trans (sound3433 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix44 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix44 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix44 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix44 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix44 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix44 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow44, value2630, value3031, value3152, value3199, value3204, value3433, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal45 : Matrix (Fin 7) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]

def boundaryMatrix45 : Matrix (Fin 7) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]

def boundaryRow45 : Integer.Sparse (Fin 909) := [(0, 1), (1, -25), (2, -25), (9, -100), (58, 5)]

theorem boundarySound45 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow45 (momentVector H) = 0 := by
  have hshape : boundaryMatrix45 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix45 1 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix45 (0 : Fin 6)) =
      Sparse.eval value296 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix45 (0 : Fin 6) = raw5117 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5117 hH).trans (sound296 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix45 (1 : Fin 6)) =
      Sparse.eval value296 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix45 (1 : Fin 6) = raw7622 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7622 hH).trans (sound296 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix45 (2 : Fin 6)) =
      Sparse.eval value296 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix45 (2 : Fin 6) = raw7644 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7644 hH).trans (sound296 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix45 (3 : Fin 6)) =
      Sparse.eval value296 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix45 (3 : Fin 6) = raw7648 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7648 hH).trans (sound296 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix45 (4 : Fin 6)) =
      Sparse.eval value69 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix45 (4 : Fin 6) = raw7650 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7650 hH).trans (sound69 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix45 (5 : Fin 6)) =
      Sparse.eval value383 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix45 (5 : Fin 6) = raw7651 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7651 hH).trans (sound383 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix45 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix45 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix45 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix45 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix45 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix45 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow45, value296, value383, value69, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal46 : Matrix (Fin 7) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def boundaryMatrix46 : Matrix (Fin 7) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def boundaryRow46 : Integer.Sparse (Fin 909) := [(0, 1), (1, -24), (2, 36), (5, -120), (6, 15), (9, -16), (27, 180), (68, 240)]

theorem boundarySound46 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow46 (momentVector H) = 0 := by
  have hshape : boundaryMatrix46 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix46 1 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix46 (0 : Fin 6)) =
      Sparse.eval value380 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix46 (0 : Fin 6) = raw5118 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5118 hH).trans (sound380 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix46 (1 : Fin 6)) =
      Sparse.eval value380 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix46 (1 : Fin 6) = raw7623 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7623 hH).trans (sound380 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix46 (2 : Fin 6)) =
      Sparse.eval value380 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix46 (2 : Fin 6) = raw7645 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7645 hH).trans (sound380 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix46 (3 : Fin 6)) =
      Sparse.eval value380 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix46 (3 : Fin 6) = raw7649 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7649 hH).trans (sound380 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix46 (4 : Fin 6)) =
      Sparse.eval value383 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix46 (4 : Fin 6) = raw7651 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7651 hH).trans (sound383 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix46 (5 : Fin 6)) =
      Sparse.eval value716 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix46 (5 : Fin 6) = raw7652 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7652 hH).trans (sound716 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix46 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix46 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix46 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix46 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix46 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix46 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow46, value380, value383, value716, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal47 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def boundaryMatrix47 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def boundaryRow47 : Integer.Sparse (Fin 909) := [(0, 1), (1, -25), (2, -150), (3, -240), (5, 320), (6, -30), (7, -480), (8, -480), (9, 40), (35, -160), (69, -240), (70, -80), (71, -480)]

theorem boundarySound47 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow47 (momentVector H) = 0 := by
  have hshape : boundaryMatrix47 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix47 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix47 (0 : Fin 6)) =
      Sparse.eval value441 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix47 (0 : Fin 6) = raw9695 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9695 hH).trans (sound441 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix47 (1 : Fin 6)) =
      Sparse.eval value441 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix47 (1 : Fin 6) = raw10005 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10005 hH).trans (sound441 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix47 (2 : Fin 6)) =
      Sparse.eval value441 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix47 (2 : Fin 6) = raw10013 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10013 hH).trans (sound441 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix47 (3 : Fin 6)) =
      Sparse.eval value1542 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix47 (3 : Fin 6) = raw10022 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10022 hH).trans (sound1542 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix47 (4 : Fin 6)) =
      Sparse.eval value1542 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix47 (4 : Fin 6) = raw10027 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10027 hH).trans (sound1542 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix47 (5 : Fin 6)) =
      Sparse.eval value1438 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix47 (5 : Fin 6) = raw10028 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10028 hH).trans (sound1438 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix47 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix47 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix47 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix47 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix47 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix47 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow47, value1438, value1542, value441, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal48 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

def boundaryMatrix48 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

def boundaryRow48 : Integer.Sparse (Fin 909) := [(0, -1), (1, 55), (2, -10), (3, -480), (5, -20), (7, -480), (9, 20), (12, -320), (13, -160), (23, 720), (35, -320), (69, -320), (70, -160), (124, 720), (125, 480)]

theorem boundarySound48 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow48 (momentVector H) = 0 := by
  have hshape : boundaryMatrix48 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix48 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix48 (0 : Fin 6)) =
      Sparse.eval value1874 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix48 (0 : Fin 6) = raw8176 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8176 hH).trans (sound1874 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix48 (1 : Fin 6)) =
      Sparse.eval value1874 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix48 (1 : Fin 6) = raw8552 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8552 hH).trans (sound1874 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix48 (2 : Fin 6)) =
      Sparse.eval value555 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix48 (2 : Fin 6) = raw8604 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8604 hH).trans (sound555 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix48 (3 : Fin 6)) =
      Sparse.eval value555 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix48 (3 : Fin 6) = raw8618 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8618 hH).trans (sound555 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix48 (4 : Fin 6)) =
      Sparse.eval value1873 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix48 (4 : Fin 6) = raw8623 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8623 hH).trans (sound1873 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix48 (5 : Fin 6)) =
      Sparse.eval value2125 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix48 (5 : Fin 6) = raw8624 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8624 hH).trans (sound2125 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix48 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix48 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix48 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix48 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix48 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix48 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow48, value1873, value1874, value2125, value555, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
