import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical232
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical246
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical267
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical268
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical269
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical270
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical298
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical299
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical300
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical301
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical302
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical304
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical309
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical310
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical312
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical313
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical314

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal167 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def boundaryMatrix167 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def boundaryRow167 : Integer.Sparse (Fin 909) := [(0, 126), (1, -2265), (2, 305), (3, 7920), (4, 5120), (5, -20), (7, 240), (12, 2320), (21, 1440), (23, -1200), (24, -1440), (25, -2640), (26, 2000), (27, 180), (31, -1680), (33, -480), (35, 160), (43, 2160), (44, 4320), (47, 720), (48, 1440), (51, -240), (55, -1920), (113, 720), (114, 1440), (191, 1440)]

theorem boundarySound167 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow167 (momentVector H) = 0 := by
  have hshape : boundaryMatrix167 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix167 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix167 (0 : Fin 6)) =
      Sparse.eval value3212 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix167 (0 : Fin 6) = raw9175 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9175 hH).trans (sound3212 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix167 (1 : Fin 6)) =
      Sparse.eval value3079 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix167 (1 : Fin 6) = raw9607 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9607 hH).trans (sound3079 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix167 (2 : Fin 6)) =
      Sparse.eval value3215 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix167 (2 : Fin 6) = raw9679 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9679 hH).trans (sound3215 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix167 (3 : Fin 6)) =
      Sparse.eval value3042 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix167 (3 : Fin 6) = raw9683 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9683 hH).trans (sound3042 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix167 (4 : Fin 6)) =
      Sparse.eval value3095 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix167 (4 : Fin 6) = raw9689 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9689 hH).trans (sound3095 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix167 (5 : Fin 6)) =
      Sparse.eval value3210 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix167 (5 : Fin 6) = raw9690 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9690 hH).trans (sound3210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix167 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix167 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix167 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix167 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix167 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix167 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow167, value3042, value3079, value3095, value3210, value3212, value3215, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal168 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def boundaryMatrix168 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def boundaryRow168 : Integer.Sparse (Fin 909) := [(0, 39), (1, -1590), (2, 670), (3, 8160), (4, 2720), (5, -100), (6, 5), (7, 160), (8, 160), (12, 3200), (13, 3440), (18, 1440), (23, -240), (24, -480), (25, -1200), (26, 320), (27, 180), (31, -1920), (33, -2400), (35, 240), (38, 720), (39, 1440), (42, 4320), (47, 720), (51, -2400), (52, 240), (54, -720), (55, -720), (56, -1200), (64, -480), (97, 720), (110, 1440), (142, 1440), (143, 1440), (238, -240)]

theorem boundarySound168 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow168 (momentVector H) = 0 := by
  have hshape : boundaryMatrix168 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix168 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix168 (0 : Fin 6)) =
      Sparse.eval value3149 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (0 : Fin 6) = raw9172 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9172 hH).trans (sound3149 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix168 (1 : Fin 6)) =
      Sparse.eval value2968 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (1 : Fin 6) = raw9604 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9604 hH).trans (sound2968 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix168 (2 : Fin 6)) =
      Sparse.eval value3146 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (2 : Fin 6) = raw9676 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9676 hH).trans (sound3146 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix168 (3 : Fin 6)) =
      Sparse.eval value3001 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (3 : Fin 6) = raw9680 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9680 hH).trans (sound3001 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix168 (4 : Fin 6)) =
      Sparse.eval value3144 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (4 : Fin 6) = raw9684 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9684 hH).trans (sound3144 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix168 (5 : Fin 6)) =
      Sparse.eval value3174 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (5 : Fin 6) = raw9685 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9685 hH).trans (sound3174 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix168 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix168 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix168 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix168 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix168 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix168 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow168, value2968, value3001, value3144, value3146, value3149, value3174, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal169 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def boundaryMatrix169 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def boundaryRow169 : Integer.Sparse (Fin 909) := [(0, 102), (1, -1245), (2, 365), (3, 3440), (4, 2120), (12, 1280), (13, 240), (25, -480), (26, 320), (31, -1440), (33, -720), (34, 80), (44, 720), (45, 2160), (46, 720), (114, 360), (115, 720), (120, 720)]

theorem boundarySound169 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow169 (momentVector H) = 0 := by
  have hshape : boundaryMatrix169 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix169 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix169 (0 : Fin 6)) =
      Sparse.eval value3088 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix169 (0 : Fin 6) = raw9173 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9173 hH).trans (sound3088 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix169 (1 : Fin 6)) =
      Sparse.eval value3082 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix169 (1 : Fin 6) = raw9605 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9605 hH).trans (sound3082 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix169 (2 : Fin 6)) =
      Sparse.eval value3084 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix169 (2 : Fin 6) = raw9677 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9677 hH).trans (sound3084 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix169 (3 : Fin 6)) =
      Sparse.eval value3085 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix169 (3 : Fin 6) = raw9681 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9681 hH).trans (sound3085 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix169 (4 : Fin 6)) =
      Sparse.eval value3083 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix169 (4 : Fin 6) = raw9686 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9686 hH).trans (sound3083 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix169 (5 : Fin 6)) =
      Sparse.eval value3076 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix169 (5 : Fin 6) = raw9687 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9687 hH).trans (sound3076 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix169 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix169 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix169 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix169 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix169 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix169 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow169, value3076, value3082, value3083, value3084, value3085, value3088, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal171 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def boundaryMatrix171 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def boundaryRow171 : Integer.Sparse (Fin 909) := [(0, 9), (1, -341), (2, 78), (3, 1568), (4, 592), (5, -28), (6, 2), (7, 48), (8, 32), (12, 608), (13, 608), (22, 288), (23, -48), (24, -96), (25, -192), (26, 224), (27, 36), (31, -288), (33, -384), (35, 160), (36, 144), (39, 576), (42, 576), (51, -384), (52, 64), (54, -432), (55, -144), (56, -336), (97, 144), (204, 288), (217, 288), (238, -48)]

theorem boundarySound171 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow171 (momentVector H) = 0 := by
  have hshape : boundaryMatrix171 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix171 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix171 (0 : Fin 6)) =
      Sparse.eval value3279 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix171 (0 : Fin 6) = raw9167 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9167 hH).trans (sound3279 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix171 (1 : Fin 6)) =
      Sparse.eval value2968 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix171 (1 : Fin 6) = raw9596 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9596 hH).trans (sound2968 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix171 (2 : Fin 6)) =
      Sparse.eval value3282 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix171 (2 : Fin 6) = raw9651 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9651 hH).trans (sound3282 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix171 (3 : Fin 6)) =
      Sparse.eval value3283 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix171 (3 : Fin 6) = raw9662 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9662 hH).trans (sound3283 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix171 (4 : Fin 6)) =
      Sparse.eval value3252 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix171 (4 : Fin 6) = raw9665 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9665 hH).trans (sound3252 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix171 (5 : Fin 6)) =
      Sparse.eval value3206 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix171 (5 : Fin 6) = raw9666 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9666 hH).trans (sound3206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix171 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix171 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix171 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix171 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix171 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix171 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow171, value2968, value3206, value3252, value3279, value3282, value3283, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal173 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def boundaryMatrix173 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def boundaryRow173 : Integer.Sparse (Fin 909) := [(0, 9), (1, -307), (2, 90), (3, 1280), (4, 528), (5, -44), (6, 4), (7, 64), (8, 64), (12, 400), (13, 288), (17, 288), (22, 288), (23, -48), (24, -288), (25, -144), (26, 224), (27, 48), (31, -288), (33, -240), (35, 96), (39, 576), (42, 576), (51, -288), (52, 64), (54, -96), (55, -192), (56, -240), (68, 12), (97, 144), (99, 288), (123, -96), (124, -48), (126, -96), (137, 144), (146, 288), (197, -144), (204, 288), (216, 288), (217, 288), (237, -96), (238, -48)]

theorem boundarySound173 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow173 (momentVector H) = 0 := by
  have hshape : boundaryMatrix173 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix173 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix173 (0 : Fin 6)) =
      Sparse.eval value3278 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix173 (0 : Fin 6) = raw9152 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9152 hH).trans (sound3278 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix173 (1 : Fin 6)) =
      Sparse.eval value3280 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix173 (1 : Fin 6) = raw9560 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9560 hH).trans (sound3280 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix173 (2 : Fin 6)) =
      Sparse.eval value3281 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix173 (2 : Fin 6) = raw9585 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9585 hH).trans (sound3281 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix173 (3 : Fin 6)) =
      Sparse.eval value2968 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix173 (3 : Fin 6) = raw9596 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9596 hH).trans (sound2968 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix173 (4 : Fin 6)) =
      Sparse.eval value3251 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix173 (4 : Fin 6) = raw9599 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9599 hH).trans (sound3251 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix173 (5 : Fin 6)) =
      Sparse.eval value3200 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix173 (5 : Fin 6) = raw9600 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9600 hH).trans (sound3200 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix173 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix173 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix173 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix173 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix173 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix173 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow173, value2968, value3200, value3251, value3278, value3280, value3281, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal175 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def boundaryMatrix175 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def boundaryRow175 : Integer.Sparse (Fin 909) := [(0, 53), (1, -1175), (2, 470), (3, 4400), (4, 2400), (5, -160), (7, 480), (8, 320), (12, 1520), (15, 720), (23, -1680), (24, -1680), (25, -3360), (26, 320), (27, 420), (31, -2880), (33, -1200), (44, 1440), (48, 2880), (51, -1920), (54, -960), (55, -960), (64, -480), (68, 60), (100, 1440), (125, -720), (126, -720), (137, 1440), (145, 720), (207, 1440), (238, -480)]

theorem boundarySound175 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow175 (momentVector H) = 0 := by
  have hshape : boundaryMatrix175 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix175 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix175 (0 : Fin 6)) =
      Sparse.eval value1752 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix175 (0 : Fin 6) = raw9728 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9728 hH).trans (sound1752 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix175 (1 : Fin 6)) =
      Sparse.eval value3095 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix175 (1 : Fin 6) = raw9891 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9891 hH).trans (sound3095 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix175 (2 : Fin 6)) =
      Sparse.eval value3095 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix175 (2 : Fin 6) = raw9914 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9914 hH).trans (sound3095 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix175 (3 : Fin 6)) =
      Sparse.eval value3186 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix175 (3 : Fin 6) = raw9924 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9924 hH).trans (sound3186 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix175 (4 : Fin 6)) =
      Sparse.eval value3042 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix175 (4 : Fin 6) = raw9927 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9927 hH).trans (sound3042 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix175 (5 : Fin 6)) =
      Sparse.eval value3187 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix175 (5 : Fin 6) = raw9928 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9928 hH).trans (sound3187 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix175 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix175 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix175 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix175 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix175 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix175 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow175, value1752, value3042, value3095, value3186, value3187, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal176 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def boundaryMatrix176 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def boundaryRow176 : Integer.Sparse (Fin 909) := [(0, 54), (1, -1555), (2, 420), (3, 6320), (4, 3040), (5, -100), (6, 5), (7, 320), (8, 80), (12, 2400), (13, 560), (18, 720), (23, -960), (24, -480), (25, -3360), (26, 720), (27, 240), (31, -2640), (33, -1200), (35, 240), (43, 720), (44, 720), (47, 720), (48, 1440), (50, 1440), (51, -2160), (52, 240), (54, -960), (55, -480), (56, -480), (64, -480), (100, 720), (104, 720), (142, 720), (177, 1440), (209, 720), (238, -240)]

theorem boundarySound176 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow176 (momentVector H) = 0 := by
  have hshape : boundaryMatrix176 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix176 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix176 (0 : Fin 6)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix176 (0 : Fin 6) = raw9734 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9734 hH).trans (sound1800 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix176 (1 : Fin 6)) =
      Sparse.eval value3095 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix176 (1 : Fin 6) = raw9910 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9910 hH).trans (sound3095 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix176 (2 : Fin 6)) =
      Sparse.eval value3190 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix176 (2 : Fin 6) = raw9941 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9941 hH).trans (sound3190 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix176 (3 : Fin 6)) =
      Sparse.eval value3099 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix176 (3 : Fin 6) = raw9943 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9943 hH).trans (sound3099 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix176 (4 : Fin 6)) =
      Sparse.eval value3079 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix176 (4 : Fin 6) = raw9946 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9946 hH).trans (sound3079 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix176 (5 : Fin 6)) =
      Sparse.eval value3189 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix176 (5 : Fin 6) = raw9947 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9947 hH).trans (sound3189 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix176 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix176 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix176 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix176 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix176 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix176 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow176, value1800, value3079, value3095, value3099, value3189, value3190, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal183 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def boundaryMatrix183 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def boundaryRow183 : Integer.Sparse (Fin 909) := [(0, 2), (1, -173), (2, 136), (3, 1264), (4, 480), (5, -72), (6, 3), (7, 240), (8, 112), (12, 128), (13, 128), (15, 144), (23, -48), (24, -192), (25, -96), (26, 528), (27, 36), (31, -192), (33, -384), (34, 112), (35, 80), (37, 288), (51, -288), (52, 32), (55, -144), (64, -96), (68, 12), (107, 288), (112, 288), (125, -48), (126, -144), (137, 288), (138, 144), (145, 144), (146, 144), (197, -48), (236, -48), (238, -96)]

theorem boundarySound183 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow183 (momentVector H) = 0 := by
  have hshape : boundaryMatrix183 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix183 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix183 (0 : Fin 6)) =
      Sparse.eval value2969 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix183 (0 : Fin 6) = raw10049 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10049 hH).trans (sound2969 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix183 (1 : Fin 6)) =
      Sparse.eval value2969 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix183 (1 : Fin 6) = raw10061 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10061 hH).trans (sound2969 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix183 (2 : Fin 6)) =
      Sparse.eval value3126 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix183 (2 : Fin 6) = raw10067 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10067 hH).trans (sound3126 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix183 (3 : Fin 6)) =
      Sparse.eval value3125 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix183 (3 : Fin 6) = raw10071 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10071 hH).trans (sound3125 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix183 (4 : Fin 6)) =
      Sparse.eval value3128 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix183 (4 : Fin 6) = raw10076 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10076 hH).trans (sound3128 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix183 (5 : Fin 6)) =
      Sparse.eval value3170 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix183 (5 : Fin 6) = raw10077 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10077 hH).trans (sound3170 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix183 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix183 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix183 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix183 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix183 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix183 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow183, value2969, value3125, value3126, value3128, value3170, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal184 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def boundaryMatrix184 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def boundaryRow184 : Integer.Sparse (Fin 909) := [(0, 103), (1, -1580), (2, 560), (3, 7920), (4, 3840), (5, -40), (6, 5), (12, 720), (13, 480), (18, 720), (26, 3920), (31, -480), (33, -960), (34, 720), (35, 160), (52, 160), (53, 1440), (55, -480), (57, 1440), (119, 1440), (139, 720), (177, 1440)]

theorem boundarySound184 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow184 (momentVector H) = 0 := by
  have hshape : boundaryMatrix184 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix184 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix184 (0 : Fin 6)) =
      Sparse.eval value3203 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix184 (0 : Fin 6) = raw10048 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10048 hH).trans (sound3203 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix184 (1 : Fin 6)) =
      Sparse.eval value3203 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix184 (1 : Fin 6) = raw10060 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10060 hH).trans (sound3203 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix184 (2 : Fin 6)) =
      Sparse.eval value3358 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix184 (2 : Fin 6) = raw10066 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10066 hH).trans (sound3358 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix184 (3 : Fin 6)) =
      Sparse.eval value3357 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix184 (3 : Fin 6) = raw10070 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10070 hH).trans (sound3357 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix184 (4 : Fin 6)) =
      Sparse.eval value3362 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix184 (4 : Fin 6) = raw10074 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10074 hH).trans (sound3362 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix184 (5 : Fin 6)) =
      Sparse.eval value3217 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix184 (5 : Fin 6) = raw10075 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10075 hH).trans (sound3217 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix184 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix184 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix184 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix184 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix184 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix184 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow184, value3203, value3217, value3357, value3358, value3362, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal187 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def boundaryMatrix187 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def boundaryRow187 : Integer.Sparse (Fin 909) := [(0, 71), (1, -1455), (2, 410), (3, 8000), (4, 3920), (5, -80), (6, 10), (7, 160), (8, 80), (12, 560), (13, 560), (21, 720), (26, 4080), (31, -960), (33, -1440), (34, 720), (35, 320), (37, 1440), (40, 720), (51, -240), (52, 80), (53, 1440), (55, -720), (56, -480), (57, 720), (119, 1440), (190, 720), (204, 720)]

theorem boundarySound187 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow187 (momentVector H) = 0 := by
  have hshape : boundaryMatrix187 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix187 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix187 (0 : Fin 6)) =
      Sparse.eval value3360 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix187 (0 : Fin 6) = raw9998 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9998 hH).trans (sound3360 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix187 (1 : Fin 6)) =
      Sparse.eval value3197 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix187 (1 : Fin 6) = raw10042 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10042 hH).trans (sound3197 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix187 (2 : Fin 6)) =
      Sparse.eval value3359 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix187 (2 : Fin 6) = raw10045 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10045 hH).trans (sound3359 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix187 (3 : Fin 6)) =
      Sparse.eval value3203 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix187 (3 : Fin 6) = raw10048 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10048 hH).trans (sound3203 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix187 (4 : Fin 6)) =
      Sparse.eval value3364 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix187 (4 : Fin 6) = raw10056 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10056 hH).trans (sound3364 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix187 (5 : Fin 6)) =
      Sparse.eval value3210 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix187 (5 : Fin 6) = raw10057 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10057 hH).trans (sound3210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix187 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix187 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix187 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix187 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix187 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix187 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow187, value3197, value3203, value3210, value3359, value3360, value3364, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal240 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def boundaryMatrix240 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def boundaryRow240 : Integer.Sparse (Fin 909) := [(0, 1), (1, -49), (2, -91), (3, -48), (5, 276), (6, -54), (7, -48), (8, -96), (9, 284), (35, -96), (52, -192), (58, -11), (69, -96), (70, -32), (71, -192), (278, -48), (310, -144), (495, -192), (726, 144), (818, 288)]

theorem boundarySound240 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow240 (momentVector H) = 0 := by
  have hshape : boundaryMatrix240 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix240 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix240 (0 : Fin 6)) =
      Sparse.eval value2123 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix240 (0 : Fin 6) = raw4053 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical4053 hH).trans (sound2123 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix240 (1 : Fin 6)) =
      Sparse.eval value2375 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix240 (1 : Fin 6) = raw7367 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7367 hH).trans (sound2375 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix240 (2 : Fin 6)) =
      Sparse.eval value2375 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix240 (2 : Fin 6) = raw7420 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7420 hH).trans (sound2375 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix240 (3 : Fin 6)) =
      Sparse.eval value2375 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix240 (3 : Fin 6) = raw7427 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7427 hH).trans (sound2375 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix240 (4 : Fin 6)) =
      Sparse.eval value2376 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix240 (4 : Fin 6) = raw7429 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7429 hH).trans (sound2376 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix240 (5 : Fin 6)) =
      Sparse.eval value2799 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix240 (5 : Fin 6) = raw7430 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7430 hH).trans (sound2799 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix240 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix240 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix240 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix240 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix240 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix240 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow240, value2123, value2375, value2376, value2799, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal241 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def boundaryMatrix241 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def boundaryRow241 : Integer.Sparse (Fin 909) := [(0, 9), (1, -255), (2, -530), (3, -480), (5, 1520), (6, -180), (7, -1920), (8, -1920), (9, 740), (35, -640), (58, -20), (69, -2400), (70, -1280), (71, -3840), (277, 720), (278, -240)]

theorem boundarySound241 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow241 (momentVector H) = 0 := by
  have hshape : boundaryMatrix241 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix241 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix241 (0 : Fin 6)) =
      Sparse.eval value1436 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix241 (0 : Fin 6) = raw4928 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical4928 hH).trans (sound1436 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix241 (1 : Fin 6)) =
      Sparse.eval value1437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix241 (1 : Fin 6) = raw7877 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7877 hH).trans (sound1437 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix241 (2 : Fin 6)) =
      Sparse.eval value1437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix241 (2 : Fin 6) = raw7887 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7887 hH).trans (sound1437 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix241 (3 : Fin 6)) =
      Sparse.eval value1437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix241 (3 : Fin 6) = raw7889 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7889 hH).trans (sound1437 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix241 (4 : Fin 6)) =
      Sparse.eval value1437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix241 (4 : Fin 6) = raw7890 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7890 hH).trans (sound1437 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix241 (5 : Fin 6)) =
      Sparse.eval value2384 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix241 (5 : Fin 6) = raw7891 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7891 hH).trans (sound2384 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix241 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix241 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix241 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix241 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix241 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix241 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow241, value1436, value1437, value2384, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal242 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def boundaryMatrix242 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def boundaryRow242 : Integer.Sparse (Fin 909) := [(1, 3), (2, -28), (3, -192), (4, -48), (5, 76), (6, -12), (7, -144), (9, 28), (11, -48), (26, -96), (35, -224), (52, -144), (58, -1), (69, -96), (70, -64), (228, 144), (278, -48), (310, -48), (495, -96), (726, 144)]

theorem boundarySound242 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow242 (momentVector H) = 0 := by
  have hshape : boundaryMatrix242 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix242 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix242 (0 : Fin 6)) =
      Sparse.eval value2113 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix242 (0 : Fin 6) = raw8178 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8178 hH).trans (sound2113 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix242 (1 : Fin 6)) =
      Sparse.eval value2113 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix242 (1 : Fin 6) = raw8555 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8555 hH).trans (sound2113 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix242 (2 : Fin 6)) =
      Sparse.eval value653 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix242 (2 : Fin 6) = raw8607 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8607 hH).trans (sound653 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix242 (3 : Fin 6)) =
      Sparse.eval value2127 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix242 (3 : Fin 6) = raw8629 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8629 hH).trans (sound2127 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix242 (4 : Fin 6)) =
      Sparse.eval value1875 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix242 (4 : Fin 6) = raw8632 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8632 hH).trans (sound1875 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix242 (5 : Fin 6)) =
      Sparse.eval value2128 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix242 (5 : Fin 6) = raw8633 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8633 hH).trans (sound2128 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix242 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix242 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix242 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix242 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix242 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix242 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow242, value1875, value2113, value2127, value2128, value653, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal243 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def boundaryMatrix243 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def boundaryRow243 : Integer.Sparse (Fin 909) := [(0, -1), (1, 70), (2, -25), (3, -1440), (4, -480), (5, 420), (6, -75), (9, 100), (11, -480), (26, -960), (35, -1440), (52, -1280), (55, 720), (58, -5), (228, 1440), (278, -80), (727, 720), (728, 480)]

theorem boundarySound243 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow243 (momentVector H) = 0 := by
  have hshape : boundaryMatrix243 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix243 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix243 (0 : Fin 6)) =
      Sparse.eval value2672 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (0 : Fin 6) = raw8188 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8188 hH).trans (sound2672 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix243 (1 : Fin 6)) =
      Sparse.eval value2672 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (1 : Fin 6) = raw8565 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8565 hH).trans (sound2672 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix243 (2 : Fin 6)) =
      Sparse.eval value2382 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (2 : Fin 6) = raw8658 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8658 hH).trans (sound2382 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix243 (3 : Fin 6)) =
      Sparse.eval value2382 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (3 : Fin 6) = raw8664 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8664 hH).trans (sound2382 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix243 (4 : Fin 6)) =
      Sparse.eval value2475 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (4 : Fin 6) = raw8670 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8670 hH).trans (sound2475 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix243 (5 : Fin 6)) =
      Sparse.eval value2671 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (5 : Fin 6) = raw8671 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8671 hH).trans (sound2671 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix243 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix243 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix243 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix243 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix243 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix243 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow243, value2382, value2475, value2671, value2672, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal244 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def boundaryMatrix244 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def boundaryRow244 : Integer.Sparse (Fin 909) := [(0, 6), (1, -105), (2, -260), (3, -1440), (5, 480), (6, -90), (7, -480), (9, 120), (12, -480), (13, -2160), (35, -1680), (52, -1440), (54, 720), (58, -5), (69, -240), (70, -160), (82, -1280), (128, -1200), (199, 1440), (201, 1440), (278, -320), (310, -240), (492, 720), (495, -480), (723, 480), (726, 720)]

theorem boundarySound244 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow244 (momentVector H) = 0 := by
  have hshape : boundaryMatrix244 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix244 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix244 (0 : Fin 6)) =
      Sparse.eval value2117 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix244 (0 : Fin 6) = raw8184 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8184 hH).trans (sound2117 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix244 (1 : Fin 6)) =
      Sparse.eval value2117 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix244 (1 : Fin 6) = raw8561 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8561 hH).trans (sound2117 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix244 (2 : Fin 6)) =
      Sparse.eval value2133 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix244 (2 : Fin 6) = raw8647 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8647 hH).trans (sound2133 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix244 (3 : Fin 6)) =
      Sparse.eval value2134 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix244 (3 : Fin 6) = raw8652 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8652 hH).trans (sound2134 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix244 (4 : Fin 6)) =
      Sparse.eval value1879 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix244 (4 : Fin 6) = raw8655 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8655 hH).trans (sound1879 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix244 (5 : Fin 6)) =
      Sparse.eval value2132 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix244 (5 : Fin 6) = raw8656 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8656 hH).trans (sound2132 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix244 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix244 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix244 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix244 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix244 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix244 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow244, value1879, value2117, value2132, value2133, value2134, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal245 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def boundaryMatrix245 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

def boundaryRow245 : Integer.Sparse (Fin 909) := [(0, 1), (1, -80), (2, -270), (3, -480), (4, -80), (5, 560), (6, -60), (7, -720), (8, -800), (9, 180), (35, -160), (51, 720), (52, -240), (58, -5), (69, -480), (70, -160), (71, -960), (308, 720), (309, 480), (310, -80)]

theorem boundarySound245 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow245 (momentVector H) = 0 := by
  have hshape : boundaryMatrix245 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix245 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix245 (0 : Fin 6)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix245 (0 : Fin 6) = raw9692 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9692 hH).trans (sound440 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix245 (1 : Fin 6)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix245 (1 : Fin 6) = raw10002 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10002 hH).trans (sound440 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix245 (2 : Fin 6)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix245 (2 : Fin 6) = raw10010 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10010 hH).trans (sound440 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix245 (3 : Fin 6)) =
      Sparse.eval value1541 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix245 (3 : Fin 6) = raw10017 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10017 hH).trans (sound1541 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix245 (4 : Fin 6)) =
      Sparse.eval value1542 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix245 (4 : Fin 6) = raw10022 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10022 hH).trans (sound1542 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix245 (5 : Fin 6)) =
      Sparse.eval value1437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix245 (5 : Fin 6) = raw10023 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10023 hH).trans (sound1437 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix245 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix245 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix245 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix245 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix245 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix245 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow245, value1437, value1541, value1542, value440, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
