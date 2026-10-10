import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical293
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical294
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical295
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical296
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical297
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical298
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical299
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical300
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical301
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical302
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical305
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical306
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical307
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical308

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal85 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def boundaryMatrix85 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def boundaryRow85 : Integer.Sparse (Fin 909) := [(0, 8), (1, -124), (2, 37), (3, 800), (4, 352), (5, -12), (6, 1), (7, 64), (12, 592), (13, 80), (23, -96), (25, -384), (26, 128), (33, -96), (35, 64), (43, 576), (50, 144), (52, 32), (55, -96), (104, 288), (113, 144)]

theorem boundarySound85 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow85 (momentVector H) = 0 := by
  have hshape : boundaryMatrix85 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix85 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix85 (0 : Fin 6)) =
      Sparse.eval value3048 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix85 (0 : Fin 6) = raw9131 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9131 hH).trans (sound3048 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix85 (1 : Fin 6)) =
      Sparse.eval value2778 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix85 (1 : Fin 6) = raw9399 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9399 hH).trans (sound2778 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix85 (2 : Fin 6)) =
      Sparse.eval value3057 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix85 (2 : Fin 6) = raw9461 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9461 hH).trans (sound3057 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix85 (3 : Fin 6)) =
      Sparse.eval value3057 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix85 (3 : Fin 6) = raw9482 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9482 hH).trans (sound3057 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix85 (4 : Fin 6)) =
      Sparse.eval value3061 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix85 (4 : Fin 6) = raw9492 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9492 hH).trans (sound3061 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix85 (5 : Fin 6)) =
      Sparse.eval value3422 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix85 (5 : Fin 6) = raw9493 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9493 hH).trans (sound3422 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix85 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix85 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix85 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix85 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix85 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix85 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow85, value2778, value3048, value3057, value3061, value3422, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal87 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def boundaryMatrix87 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def boundaryRow87 : Integer.Sparse (Fin 909) := [(0, 64), (1, -710), (2, 515), (3, 3760), (4, 1760), (5, -260), (6, 5), (7, 480), (8, 800), (12, 240), (23, -240), (24, -480), (26, 880), (27, 60), (31, -1680), (43, 720), (46, 1440), (51, -1440), (52, 80), (56, -960), (77, 720), (81, -480), (106, 1440), (107, 1440), (122, 1440), (228, -240)]

theorem boundarySound87 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow87 (momentVector H) = 0 := by
  have hshape : boundaryMatrix87 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix87 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix87 (0 : Fin 6)) =
      Sparse.eval value3028 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix87 (0 : Fin 6) = raw9145 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9145 hH).trans (sound3028 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix87 (1 : Fin 6)) =
      Sparse.eval value2443 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix87 (1 : Fin 6) = raw9413 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9413 hH).trans (sound2443 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix87 (2 : Fin 6)) =
      Sparse.eval value3025 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix87 (2 : Fin 6) = raw9520 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9520 hH).trans (sound3025 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix87 (3 : Fin 6)) =
      Sparse.eval value3035 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix87 (3 : Fin 6) = raw9537 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9537 hH).trans (sound3035 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix87 (4 : Fin 6)) =
      Sparse.eval value3024 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix87 (4 : Fin 6) = raw9542 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9542 hH).trans (sound3024 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix87 (5 : Fin 6)) =
      Sparse.eval value3429 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix87 (5 : Fin 6) = raw9543 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9543 hH).trans (sound3429 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix87 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix87 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix87 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix87 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix87 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix87 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow87, value2443, value3024, value3025, value3028, value3035, value3429, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal88 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def boundaryMatrix88 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def boundaryRow88 : Integer.Sparse (Fin 909) := [(0, 6), (1, -189), (2, 83), (3, 832), (4, 368), (5, -28), (6, 2), (7, 112), (8, 16), (12, 320), (13, 96), (23, -48), (24, -48), (25, -336), (26, 128), (31, -336), (33, -336), (35, 80), (43, 288), (46, 288), (50, 144), (51, -96), (52, 64), (55, -96), (81, -96), (95, 144), (104, 144), (113, 288), (122, 288)]

theorem boundarySound88 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow88 (momentVector H) = 0 := by
  have hshape : boundaryMatrix88 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix88 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix88 (0 : Fin 6)) =
      Sparse.eval value3049 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix88 (0 : Fin 6) = raw9147 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9147 hH).trans (sound3049 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix88 (1 : Fin 6)) =
      Sparse.eval value2769 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix88 (1 : Fin 6) = raw9415 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9415 hH).trans (sound2769 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix88 (2 : Fin 6)) =
      Sparse.eval value3068 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix88 (2 : Fin 6) = raw9522 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9522 hH).trans (sound3068 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix88 (3 : Fin 6)) =
      Sparse.eval value3069 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix88 (3 : Fin 6) = raw9541 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9541 hH).trans (sound3069 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix88 (4 : Fin 6)) =
      Sparse.eval value3067 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix88 (4 : Fin 6) = raw9547 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9547 hH).trans (sound3067 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix88 (5 : Fin 6)) =
      Sparse.eval value3423 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix88 (5 : Fin 6) = raw9548 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9548 hH).trans (sound3423 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix88 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix88 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix88 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix88 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix88 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix88 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow88, value2769, value3049, value3067, value3068, value3069, value3423, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal89 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def boundaryMatrix89 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def boundaryRow89 : Integer.Sparse (Fin 909) := [(0, -1), (1, -56), (2, 56), (3, 464), (4, 80), (5, -40), (6, 1), (7, 80), (8, 80), (10, -72), (12, 184), (13, 192), (24, -48), (26, 32), (35, 32), (38, 72), (40, 144), (51, -48), (52, 48), (55, -72), (59, -144), (72, 72), (75, 144), (94, 144), (95, 288), (102, 288), (199, -24)]

theorem boundarySound89 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow89 (momentVector H) = 0 := by
  have hshape : boundaryMatrix89 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix89 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix89 (0 : Fin 6)) =
      Sparse.eval value2952 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix89 (0 : Fin 6) = raw9139 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9139 hH).trans (sound2952 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix89 (1 : Fin 6)) =
      Sparse.eval value2427 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix89 (1 : Fin 6) = raw9407 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9407 hH).trans (sound2427 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix89 (2 : Fin 6)) =
      Sparse.eval value2951 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix89 (2 : Fin 6) = raw9514 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9514 hH).trans (sound2951 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix89 (3 : Fin 6)) =
      Sparse.eval value2951 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix89 (3 : Fin 6) = raw9523 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9523 hH).trans (sound2951 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix89 (4 : Fin 6)) =
      Sparse.eval value2957 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix89 (4 : Fin 6) = raw9525 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9525 hH).trans (sound2957 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix89 (5 : Fin 6)) =
      Sparse.eval value3426 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix89 (5 : Fin 6) = raw9526 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9526 hH).trans (sound3426 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix89 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix89 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix89 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix89 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix89 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix89 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow89, value2427, value2951, value2952, value2957, value3426, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal90 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def boundaryMatrix90 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def boundaryRow90 : Integer.Sparse (Fin 909) := [(0, 31), (1, -362), (2, 90), (3, 768), (4, 704), (5, -20), (6, 1), (7, 32), (8, 32), (12, 144), (24, -96), (25, -240), (26, 160), (31, -768), (35, 32), (43, 288), (44, 576), (52, 32), (55, -96), (95, 288), (113, 144)]

theorem boundarySound90 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow90 (momentVector H) = 0 := by
  have hshape : boundaryMatrix90 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix90 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix90 (0 : Fin 6)) =
      Sparse.eval value3051 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix90 (0 : Fin 6) = raw9163 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9163 hH).trans (sound3051 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix90 (1 : Fin 6)) =
      Sparse.eval value3076 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix90 (1 : Fin 6) = raw9581 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9581 hH).trans (sound3076 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix90 (2 : Fin 6)) =
      Sparse.eval value3076 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix90 (2 : Fin 6) = raw9617 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9617 hH).trans (sound3076 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix90 (3 : Fin 6)) =
      Sparse.eval value3078 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix90 (3 : Fin 6) = raw9638 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9638 hH).trans (sound3078 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix90 (4 : Fin 6)) =
      Sparse.eval value3446 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix90 (4 : Fin 6) = raw9644 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9644 hH).trans (sound3446 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix90 (5 : Fin 6)) =
      Sparse.eval value3400 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix90 (5 : Fin 6) = raw9645 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9645 hH).trans (sound3400 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix90 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix90 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix90 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix90 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix90 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix90 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow90, value3051, value3076, value3078, value3400, value3446, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal91 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def boundaryMatrix91 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def boundaryRow91 : Integer.Sparse (Fin 909) := [(0, 68), (1, -1405), (2, 540), (3, 5040), (4, 2240), (5, -180), (6, 5), (7, 880), (8, 160), (10, -240), (12, 2480), (13, 160), (23, -2160), (24, -1440), (25, -480), (26, 640), (27, 420), (31, -1440), (35, 240), (43, 2880), (52, 160), (55, -1200), (79, 720), (95, 1440), (113, 1440)]

theorem boundarySound91 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow91 (momentVector H) = 0 := by
  have hshape : boundaryMatrix91 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix91 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix91 (0 : Fin 6)) =
      Sparse.eval value3038 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix91 (0 : Fin 6) = raw9156 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9156 hH).trans (sound3038 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix91 (1 : Fin 6)) =
      Sparse.eval value3041 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix91 (1 : Fin 6) = raw9574 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9574 hH).trans (sound3041 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix91 (2 : Fin 6)) =
      Sparse.eval value3041 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix91 (2 : Fin 6) = raw9610 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9610 hH).trans (sound3041 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix91 (3 : Fin 6)) =
      Sparse.eval value3053 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix91 (3 : Fin 6) = raw9620 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9620 hH).trans (sound3053 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix91 (4 : Fin 6)) =
      Sparse.eval value2945 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix91 (4 : Fin 6) = raw9625 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9625 hH).trans (sound2945 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix91 (5 : Fin 6)) =
      Sparse.eval value3405 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix91 (5 : Fin 6) = raw9626 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9626 hH).trans (sound3405 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix91 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix91 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix91 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix91 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix91 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix91 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow91, value2945, value3038, value3041, value3053, value3405, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal92 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def boundaryMatrix92 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def boundaryRow92 : Integer.Sparse (Fin 909) := [(0, 54), (1, -935), (2, 310), (3, 3280), (4, 1480), (5, -140), (6, 5), (7, 360), (8, 360), (12, 1080), (23, -480), (24, -120), (26, 720), (27, 30), (31, -240), (35, 80), (43, 720), (45, 1440), (51, -600), (55, -240), (56, -480), (77, 360), (105, 720), (107, 720), (228, -120)]

theorem boundarySound92 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow92 (momentVector H) = 0 := by
  have hshape : boundaryMatrix92 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix92 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix92 (0 : Fin 6)) =
      Sparse.eval value3020 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix92 (0 : Fin 6) = raw9170 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9170 hH).trans (sound3020 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix92 (1 : Fin 6)) =
      Sparse.eval value3077 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix92 (1 : Fin 6) = raw9602 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9602 hH).trans (sound3077 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix92 (2 : Fin 6)) =
      Sparse.eval value3026 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix92 (2 : Fin 6) = raw9654 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9654 hH).trans (sound3026 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix92 (3 : Fin 6)) =
      Sparse.eval value3036 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix92 (3 : Fin 6) = raw9668 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9668 hH).trans (sound3036 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix92 (4 : Fin 6)) =
      Sparse.eval value3022 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix92 (4 : Fin 6) = raw9672 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9672 hH).trans (sound3022 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix92 (5 : Fin 6)) =
      Sparse.eval value3403 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix92 (5 : Fin 6) = raw9673 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9673 hH).trans (sound3403 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix92 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix92 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix92 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix92 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix92 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix92 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow92, value3020, value3022, value3026, value3036, value3077, value3403, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal93 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def boundaryMatrix93 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def boundaryRow93 : Integer.Sparse (Fin 909) := [(0, 4), (1, -875), (2, 605), (3, 5680), (4, 640), (5, -420), (6, 20), (7, 880), (8, 640), (10, -720), (12, 3120), (13, 3840), (23, -480), (26, 320), (33, -1920), (35, 800), (36, 720), (38, 1440), (40, 1440), (52, 640), (54, -1200), (55, -720), (59, -960), (72, 720), (75, 1440), (199, -240)]

theorem boundarySound93 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow93 (momentVector H) = 0 := by
  have hshape : boundaryMatrix93 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix93 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix93 (0 : Fin 6)) =
      Sparse.eval value2947 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix93 (0 : Fin 6) = raw9165 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9165 hH).trans (sound2947 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix93 (1 : Fin 6)) =
      Sparse.eval value3017 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix93 (1 : Fin 6) = raw9591 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9591 hH).trans (sound3017 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix93 (2 : Fin 6)) =
      Sparse.eval value2950 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix93 (2 : Fin 6) = raw9649 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9649 hH).trans (sound2950 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix93 (3 : Fin 6)) =
      Sparse.eval value2950 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix93 (3 : Fin 6) = raw9656 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9656 hH).trans (sound2950 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix93 (4 : Fin 6)) =
      Sparse.eval value2946 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix93 (4 : Fin 6) = raw9658 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9658 hH).trans (sound2946 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix93 (5 : Fin 6)) =
      Sparse.eval value3390 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix93 (5 : Fin 6) = raw9659 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9659 hH).trans (sound3390 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix93 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix93 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix93 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix93 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix93 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix93 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow93, value2946, value2947, value2950, value3017, value3390, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal94 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def boundaryMatrix94 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def boundaryRow94 : Integer.Sparse (Fin 909) := [(0, 8), (1, -1045), (2, 155), (3, 6480), (4, 1920), (10, -720), (12, 3200), (13, 2800), (23, -480), (24, -960), (25, -720), (27, 60), (33, -1920), (50, 1440), (55, -1920), (59, -720), (79, 720), (80, 1440), (94, 720), (101, 1440)]

theorem boundarySound94 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow94 (momentVector H) = 0 := by
  have hshape : boundaryMatrix94 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix94 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix94 (0 : Fin 6)) =
      Sparse.eval value2453 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix94 (0 : Fin 6) = raw9707 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9707 hH).trans (sound2453 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix94 (1 : Fin 6)) =
      Sparse.eval value2453 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix94 (1 : Fin 6) = raw9771 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9771 hH).trans (sound2453 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix94 (2 : Fin 6)) =
      Sparse.eval value3098 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix94 (2 : Fin 6) = raw9812 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9812 hH).trans (sound3098 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix94 (3 : Fin 6)) =
      Sparse.eval value3098 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix94 (3 : Fin 6) = raw9826 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9826 hH).trans (sound3098 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix94 (4 : Fin 6)) =
      Sparse.eval value3000 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix94 (4 : Fin 6) = raw9830 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9830 hH).trans (sound3000 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix94 (5 : Fin 6)) =
      Sparse.eval value2891 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix94 (5 : Fin 6) = raw9831 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9831 hH).trans (sound2891 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix94 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix94 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix94 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix94 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix94 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix94 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow94, value2453, value2891, value3000, value3098, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal95 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def boundaryMatrix95 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def boundaryRow95 : Integer.Sparse (Fin 909) := [(0, -7), (1, -515), (2, 435), (3, 4560), (4, 800), (5, -100), (6, 5), (7, 480), (12, 3200), (13, 3600), (25, -240), (26, 160), (33, -960), (35, 800), (41, 1440), (52, 640), (59, -720), (73, 720), (75, 1440), (94, 720), (101, 1440), (201, -720)]

theorem boundarySound95 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow95 (momentVector H) = 0 := by
  have hshape : boundaryMatrix95 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix95 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix95 (0 : Fin 6)) =
      Sparse.eval value2676 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix95 (0 : Fin 6) = raw9709 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9709 hH).trans (sound2676 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix95 (1 : Fin 6)) =
      Sparse.eval value2676 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix95 (1 : Fin 6) = raw9773 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9773 hH).trans (sound2676 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix95 (2 : Fin 6)) =
      Sparse.eval value2997 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix95 (2 : Fin 6) = raw9814 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9814 hH).trans (sound2997 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix95 (3 : Fin 6)) =
      Sparse.eval value2997 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix95 (3 : Fin 6) = raw9828 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9828 hH).trans (sound2997 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix95 (4 : Fin 6)) =
      Sparse.eval value3000 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix95 (4 : Fin 6) = raw9835 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9835 hH).trans (sound3000 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix95 (5 : Fin 6)) =
      Sparse.eval value2926 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix95 (5 : Fin 6) = raw9836 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9836 hH).trans (sound2926 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix95 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix95 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix95 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix95 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix95 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix95 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow95, value2676, value2926, value2997, value3000, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal96 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def boundaryMatrix96 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def boundaryRow96 : Integer.Sparse (Fin 909) := [(0, -22), (1, -465), (2, 365), (3, 4880), (4, 320), (5, -180), (7, 720), (8, 320), (10, -240), (12, 2800), (13, 3920), (23, -720), (25, -240), (27, 180), (33, -960), (35, 320), (38, 1440), (51, -1920), (54, -1920), (55, -480), (59, -1680), (72, 720), (74, 1440), (94, 720), (101, 1440), (199, -720)]

theorem boundarySound96 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow96 (momentVector H) = 0 := by
  have hshape : boundaryMatrix96 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix96 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix96 (0 : Fin 6)) =
      Sparse.eval value2421 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix96 (0 : Fin 6) = raw9708 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9708 hH).trans (sound2421 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix96 (1 : Fin 6)) =
      Sparse.eval value2421 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix96 (1 : Fin 6) = raw9772 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9772 hH).trans (sound2421 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix96 (2 : Fin 6)) =
      Sparse.eval value2966 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix96 (2 : Fin 6) = raw9813 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9813 hH).trans (sound2966 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix96 (3 : Fin 6)) =
      Sparse.eval value2966 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix96 (3 : Fin 6) = raw9827 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9827 hH).trans (sound2966 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix96 (4 : Fin 6)) =
      Sparse.eval value3000 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix96 (4 : Fin 6) = raw9833 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9833 hH).trans (sound3000 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix96 (5 : Fin 6)) =
      Sparse.eval value2876 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix96 (5 : Fin 6) = raw9834 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9834 hH).trans (sound2876 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix96 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix96 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix96 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix96 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix96 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix96 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow96, value2421, value2876, value2966, value3000, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal97 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def boundaryMatrix97 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def boundaryRow97 : Integer.Sparse (Fin 909) := [(0, 6), (1, -140), (2, 225), (3, 2560), (4, 800), (5, -260), (6, 15), (7, 1360), (8, 160), (12, 1600), (13, 1040), (23, -480), (25, -960), (26, 720), (35, 1200), (38, 1440), (41, 720), (43, 1440), (52, 560), (54, -720), (84, 720), (97, 1440), (98, 1440), (228, -240)]

theorem boundarySound97 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow97 (momentVector H) = 0 := by
  have hshape : boundaryMatrix97 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix97 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix97 (0 : Fin 6)) =
      Sparse.eval value2742 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix97 (0 : Fin 6) = raw9704 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9704 hH).trans (sound2742 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix97 (1 : Fin 6)) =
      Sparse.eval value2742 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix97 (1 : Fin 6) = raw9768 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9768 hH).trans (sound2742 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix97 (2 : Fin 6)) =
      Sparse.eval value2994 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix97 (2 : Fin 6) = raw9800 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9800 hH).trans (sound2994 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix97 (3 : Fin 6)) =
      Sparse.eval value2996 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix97 (3 : Fin 6) = raw9808 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9808 hH).trans (sound2996 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix97 (4 : Fin 6)) =
      Sparse.eval value2997 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix97 (4 : Fin 6) = raw9814 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9814 hH).trans (sound2997 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix97 (5 : Fin 6)) =
      Sparse.eval value2911 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix97 (5 : Fin 6) = raw9815 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9815 hH).trans (sound2911 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix97 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix97 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix97 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix97 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix97 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix97 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow97, value2742, value2911, value2994, value2996, value2997, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal98 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def boundaryMatrix98 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def boundaryRow98 : Integer.Sparse (Fin 909) := [(0, 39), (1, -385), (2, 615), (3, 3600), (4, 960), (5, -740), (6, 65), (7, 720), (8, 1120), (12, 560), (13, 240), (23, -240), (26, 640), (31, -720), (33, -480), (35, 560), (44, 1440), (51, -1440), (52, 880), (54, -960), (81, -480), (95, 720), (99, 1440), (100, 1440)]

theorem boundarySound98 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow98 (momentVector H) = 0 := by
  have hshape : boundaryMatrix98 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix98 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix98 (0 : Fin 6)) =
      Sparse.eval value2748 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix98 (0 : Fin 6) = raw9706 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9706 hH).trans (sound2748 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix98 (1 : Fin 6)) =
      Sparse.eval value2748 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix98 (1 : Fin 6) = raw9770 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9770 hH).trans (sound2748 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix98 (2 : Fin 6)) =
      Sparse.eval value2995 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix98 (2 : Fin 6) = raw9802 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9802 hH).trans (sound2995 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix98 (3 : Fin 6)) =
      Sparse.eval value2998 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix98 (3 : Fin 6) = raw9819 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9819 hH).trans (sound2998 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix98 (4 : Fin 6)) =
      Sparse.eval value2999 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix98 (4 : Fin 6) = raw9822 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9822 hH).trans (sound2999 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix98 (5 : Fin 6)) =
      Sparse.eval value2920 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix98 (5 : Fin 6) = raw9823 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9823 hH).trans (sound2920 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix98 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix98 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix98 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix98 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix98 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix98 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow98, value2748, value2920, value2995, value2998, value2999, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal99 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def boundaryMatrix99 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def boundaryRow99 : Integer.Sparse (Fin 909) := [(0, 24), (1, -795), (2, 495), (3, 4320), (4, 2000), (5, -220), (6, 10), (7, 800), (8, 160), (12, 1120), (13, 960), (25, -960), (26, 1280), (31, -1200), (33, -960), (35, 720), (38, 720), (39, 1440), (41, 1440), (46, 1440), (51, -480), (52, 640), (54, -720), (81, -480), (84, 720), (85, 1440), (95, 720), (103, 1440), (228, -720)]

theorem boundarySound99 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow99 (momentVector H) = 0 := by
  have hshape : boundaryMatrix99 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix99 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix99 (0 : Fin 6)) =
      Sparse.eval value2750 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix99 (0 : Fin 6) = raw9717 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9717 hH).trans (sound2750 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix99 (1 : Fin 6)) =
      Sparse.eval value2750 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix99 (1 : Fin 6) = raw9781 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9781 hH).trans (sound2750 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix99 (2 : Fin 6)) =
      Sparse.eval value3003 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix99 (2 : Fin 6) = raw9852 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9852 hH).trans (sound3003 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix99 (3 : Fin 6)) =
      Sparse.eval value3004 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix99 (3 : Fin 6) = raw9859 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9859 hH).trans (sound3004 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix99 (4 : Fin 6)) =
      Sparse.eval value3002 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix99 (4 : Fin 6) = raw9863 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9863 hH).trans (sound3002 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix99 (5 : Fin 6)) =
      Sparse.eval value2922 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix99 (5 : Fin 6) = raw9864 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9864 hH).trans (sound2922 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix99 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix99 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix99 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix99 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix99 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix99 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow99, value2750, value2922, value3002, value3003, value3004, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal100 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def boundaryMatrix100 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def boundaryRow100 : Integer.Sparse (Fin 909) := [(0, 44), (1, -690), (2, 385), (3, 4960), (4, 2480), (5, -260), (6, 15), (7, 640), (8, 480), (12, 240), (13, 160), (24, -480), (26, 2160), (31, -480), (35, 320), (37, 2160), (40, 1440), (52, 160), (56, -1200), (81, -960), (83, 720), (85, 1440), (99, 1440), (107, 1440), (228, -960)]

theorem boundarySound100 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow100 (momentVector H) = 0 := by
  have hshape : boundaryMatrix100 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix100 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix100 (0 : Fin 6)) =
      Sparse.eval value2532 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix100 (0 : Fin 6) = raw9716 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9716 hH).trans (sound2532 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix100 (1 : Fin 6)) =
      Sparse.eval value2532 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix100 (1 : Fin 6) = raw9780 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9780 hH).trans (sound2532 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix100 (2 : Fin 6)) =
      Sparse.eval value3196 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix100 (2 : Fin 6) = raw9851 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9851 hH).trans (sound3196 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix100 (3 : Fin 6)) =
      Sparse.eval value3197 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix100 (3 : Fin 6) = raw9858 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9858 hH).trans (sound3197 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix100 (4 : Fin 6)) =
      Sparse.eval value3301 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix100 (4 : Fin 6) = raw9861 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9861 hH).trans (sound3301 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix100 (5 : Fin 6)) =
      Sparse.eval value2918 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix100 (5 : Fin 6) = raw9862 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9862 hH).trans (sound2918 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix100 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix100 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix100 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix100 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix100 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix100 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow100, value2532, value2918, value3196, value3197, value3301, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal101 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def boundaryMatrix101 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

def boundaryRow101 : Integer.Sparse (Fin 909) := [(0, -1), (1, -390), (2, 480), (3, 3520), (4, 1120), (5, -420), (6, 35), (7, 1200), (8, 240), (12, 880), (13, 720), (23, -240), (24, -240), (25, -480), (26, 880), (31, -720), (33, -1440), (35, 1200), (41, 720), (43, 1440), (51, -720), (52, 1120), (54, -480), (59, -480), (73, 720), (81, -480), (94, 1440), (95, 720), (103, 1440), (104, 1440), (201, -240)]

theorem boundarySound101 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow101 (momentVector H) = 0 := by
  have hshape : boundaryMatrix101 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix101 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix101 (0 : Fin 6)) =
      Sparse.eval value2740 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix101 (0 : Fin 6) = raw9715 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9715 hH).trans (sound2740 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix101 (1 : Fin 6)) =
      Sparse.eval value2740 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix101 (1 : Fin 6) = raw9779 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9779 hH).trans (sound2740 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix101 (2 : Fin 6)) =
      Sparse.eval value3005 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix101 (2 : Fin 6) = raw9850 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9850 hH).trans (sound3005 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix101 (3 : Fin 6)) =
      Sparse.eval value3006 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix101 (3 : Fin 6) = raw9855 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9855 hH).trans (sound3006 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix101 (4 : Fin 6)) =
      Sparse.eval value3004 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix101 (4 : Fin 6) = raw9859 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9859 hH).trans (sound3004 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix101 (5 : Fin 6)) =
      Sparse.eval value2935 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix101 (5 : Fin 6) = raw9860 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9860 hH).trans (sound2935 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix101 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix101 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix101 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix101 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix101 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix101 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow101, value2740, value2935, value3004, value3005, value3006, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
