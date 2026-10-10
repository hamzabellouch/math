import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical284
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical287
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical288
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical289
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical290
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical292
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical293
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical294
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical295
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical296
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical299
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical300
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical301
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical302
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical304
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical305
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical306
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical307
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical308
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical309
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical310

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal303 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def boundaryMatrix303 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def boundaryRow303 : Integer.Sparse (Fin 909) := [(0, -13), (1, -30), (2, 155), (3, 2000), (5, -580), (6, 70), (7, 1840), (8, 960), (9, -160), (10, -480), (12, 160), (13, 80), (23, -720), (24, -240), (26, 160), (27, 120), (35, 1520), (51, -480), (52, 160), (54, -1200), (55, -240), (59, -480), (69, 1600), (70, 960), (71, 640), (72, 1440), (73, 720), (77, 1440), (199, -480), (228, -480), (256, -480), (277, -240), (279, 720), (282, 720), (286, 1440), (287, 1440), (726, -480)]

theorem boundarySound303 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow303 (momentVector H) = 0 := by
  have hshape : boundaryMatrix303 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix303 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix303 (0 : Fin 6)) =
      Sparse.eval value2739 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix303 (0 : Fin 6) = raw9705 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9705 hH).trans (sound2739 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix303 (1 : Fin 6)) =
      Sparse.eval value2739 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix303 (1 : Fin 6) = raw9769 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9769 hH).trans (sound2739 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix303 (2 : Fin 6)) =
      Sparse.eval value2870 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix303 (2 : Fin 6) = raw9801 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9801 hH).trans (sound2870 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix303 (3 : Fin 6)) =
      Sparse.eval value2872 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix303 (3 : Fin 6) = raw9809 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9809 hH).trans (sound2872 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix303 (4 : Fin 6)) =
      Sparse.eval value2873 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix303 (4 : Fin 6) = raw9816 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9816 hH).trans (sound2873 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix303 (5 : Fin 6)) =
      Sparse.eval value2863 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix303 (5 : Fin 6) = raw9817 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9817 hH).trans (sound2863 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix303 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix303 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix303 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix303 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix303 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix303 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow303, value2739, value2863, value2870, value2872, value2873, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal304 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def boundaryMatrix304 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def boundaryRow304 : Integer.Sparse (Fin 909) := [(0, -11), (1, 10), (2, 605), (3, 3120), (4, 400), (5, -900), (6, 70), (7, 2400), (8, 720), (9, -80), (12, 160), (13, 320), (24, -240), (26, 480), (35, 2320), (51, -480), (52, 1920), (69, 640), (70, 320), (71, 640), (73, 1440), (81, -960), (84, 720), (85, 1440), (201, -480), (228, -720), (256, -1440), (277, -720), (279, 720), (280, 1440), (322, 2160), (327, 1440), (726, -240), (818, -720)]

theorem boundarySound304 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow304 (momentVector H) = 0 := by
  have hshape : boundaryMatrix304 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix304 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix304 (0 : Fin 6)) =
      Sparse.eval value2402 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix304 (0 : Fin 6) = raw9718 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9718 hH).trans (sound2402 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix304 (1 : Fin 6)) =
      Sparse.eval value2402 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix304 (1 : Fin 6) = raw9782 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9782 hH).trans (sound2402 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix304 (2 : Fin 6)) =
      Sparse.eval value2934 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix304 (2 : Fin 6) = raw9853 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9853 hH).trans (sound2934 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix304 (3 : Fin 6)) =
      Sparse.eval value2935 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix304 (3 : Fin 6) = raw9860 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9860 hH).trans (sound2935 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix304 (4 : Fin 6)) =
      Sparse.eval value2922 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix304 (4 : Fin 6) = raw9864 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9864 hH).trans (sound2922 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix304 (5 : Fin 6)) =
      Sparse.eval value2868 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix304 (5 : Fin 6) = raw9865 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9865 hH).trans (sound2868 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix304 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix304 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix304 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix304 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix304 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix304 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow304, value2402, value2868, value2922, value2934, value2935, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal305 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def boundaryMatrix305 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def boundaryRow305 : Integer.Sparse (Fin 909) := [(0, -28), (1, 415), (2, 840), (3, 1760), (4, 400), (5, -1660), (6, 105), (7, 1920), (8, 2880), (9, -120), (13, 320), (26, 160), (35, 800), (51, -1680), (52, 640), (56, -1440), (59, -1200), (69, 1040), (70, 400), (71, 1600), (76, 2880), (77, 720), (201, -960), (228, -240), (256, -480), (281, 1440), (286, 1440), (287, 720), (288, 1440), (726, -240), (818, -480)]

theorem boundarySound305 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow305 (momentVector H) = 0 := by
  have hshape : boundaryMatrix305 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix305 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix305 (0 : Fin 6)) =
      Sparse.eval value2596 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix305 (0 : Fin 6) = raw9730 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9730 hH).trans (sound2596 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix305 (1 : Fin 6)) =
      Sparse.eval value2879 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix305 (1 : Fin 6) = raw9894 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9894 hH).trans (sound2879 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix305 (2 : Fin 6)) =
      Sparse.eval value2879 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix305 (2 : Fin 6) = raw9916 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9916 hH).trans (sound2879 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix305 (3 : Fin 6)) =
      Sparse.eval value2877 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix305 (3 : Fin 6) = raw9926 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9926 hH).trans (sound2877 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix305 (4 : Fin 6)) =
      Sparse.eval value3439 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix305 (4 : Fin 6) = raw9930 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9930 hH).trans (sound3439 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix305 (5 : Fin 6)) =
      Sparse.eval value2867 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix305 (5 : Fin 6) = raw9931 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9931 hH).trans (sound2867 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix305 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix305 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix305 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix305 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix305 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix305 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow305, value2596, value2867, value2877, value2879, value3439, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal306 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def boundaryMatrix306 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def boundaryRow306 : Integer.Sparse (Fin 909) := [(0, -27), (1, 555), (2, 1085), (3, 1600), (4, 80), (5, -2280), (6, 225), (7, 2320), (8, 3040), (9, -160), (26, 160), (35, 880), (51, -720), (52, 1280), (69, 720), (70, 80), (71, 2400), (85, 1440), (228, -480), (256, -480), (277, -240), (280, 720), (322, 720), (325, 1440), (327, 1440), (818, -480)]

theorem boundarySound306 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow306 (momentVector H) = 0 := by
  have hshape : boundaryMatrix306 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix306 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix306 (0 : Fin 6)) =
      Sparse.eval value2390 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (0 : Fin 6) = raw9727 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9727 hH).trans (sound2390 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix306 (1 : Fin 6)) =
      Sparse.eval value2913 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (1 : Fin 6) = raw9890 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9890 hH).trans (sound2913 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix306 (2 : Fin 6)) =
      Sparse.eval value2913 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (2 : Fin 6) = raw9913 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9913 hH).trans (sound2913 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix306 (3 : Fin 6)) =
      Sparse.eval value2927 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (3 : Fin 6) = raw9919 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9919 hH).trans (sound2927 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix306 (4 : Fin 6)) =
      Sparse.eval value3334 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (4 : Fin 6) = raw9922 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9922 hH).trans (sound3334 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix306 (5 : Fin 6)) =
      Sparse.eval value2864 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (5 : Fin 6) = raw9923 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9923 hH).trans (sound2864 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix306 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix306 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix306 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix306 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix306 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix306 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow306, value2390, value2864, value2913, value2927, value3334, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal307 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def boundaryMatrix307 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def boundaryRow307 : Integer.Sparse (Fin 909) := [(0, -9), (1, 20), (2, 95), (3, 800), (5, -180), (6, 20), (7, 480), (9, -40), (12, 160), (13, 160), (23, -240), (31, -480), (33, -480), (35, 320), (52, 320), (69, 160), (70, 160), (81, -960), (95, 1440), (124, -240), (196, -240), (256, -480), (322, 1440), (379, 1440), (818, -480)]

theorem boundarySound307 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow307 (momentVector H) = 0 := by
  have hshape : boundaryMatrix307 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix307 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix307 (0 : Fin 6)) =
      Sparse.eval value2980 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix307 (0 : Fin 6) = raw9118 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9118 hH).trans (sound2980 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix307 (1 : Fin 6)) =
      Sparse.eval value2738 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix307 (1 : Fin 6) = raw9387 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9387 hH).trans (sound2738 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix307 (2 : Fin 6)) =
      Sparse.eval value2738 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix307 (2 : Fin 6) = raw9425 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9425 hH).trans (sound2738 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix307 (3 : Fin 6)) =
      Sparse.eval value2983 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix307 (3 : Fin 6) = raw9439 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9439 hH).trans (sound2983 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix307 (4 : Fin 6)) =
      Sparse.eval value2899 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix307 (4 : Fin 6) = raw9441 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9441 hH).trans (sound2899 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix307 (5 : Fin 6)) =
      Sparse.eval value2985 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix307 (5 : Fin 6) = raw9442 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9442 hH).trans (sound2985 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix307 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix307 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix307 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix307 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix307 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix307 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow307, value2738, value2899, value2980, value2983, value2985, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal308 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def boundaryMatrix308 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def boundaryRow308 : Integer.Sparse (Fin 909) := [(0, -4), (1, 15), (2, 20), (3, 2400), (4, 640), (5, -380), (6, 45), (7, 2560), (8, 480), (9, -40), (12, 320), (13, 160), (23, -480), (24, -480), (25, -1200), (26, 1120), (35, 1440), (52, 320), (54, -1200), (69, 240), (70, 80), (71, 160), (97, 2880), (113, 720), (124, -480), (197, -480), (228, -960), (256, -480), (277, -240), (291, 720), (378, 1440)]

theorem boundarySound308 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow308 (momentVector H) = 0 := by
  have hshape : boundaryMatrix308 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix308 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix308 (0 : Fin 6)) =
      Sparse.eval value2981 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix308 (0 : Fin 6) = raw9126 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9126 hH).trans (sound2981 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix308 (1 : Fin 6)) =
      Sparse.eval value2436 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix308 (1 : Fin 6) = raw9394 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9394 hH).trans (sound2436 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix308 (2 : Fin 6)) =
      Sparse.eval value2986 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix308 (2 : Fin 6) = raw9455 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9455 hH).trans (sound2986 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix308 (3 : Fin 6)) =
      Sparse.eval value2986 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix308 (3 : Fin 6) = raw9477 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9477 hH).trans (sound2986 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix308 (4 : Fin 6)) =
      Sparse.eval value2895 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix308 (4 : Fin 6) = raw9485 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9485 hH).trans (sound2895 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix308 (5 : Fin 6)) =
      Sparse.eval value3422 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix308 (5 : Fin 6) = raw9486 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9486 hH).trans (sound3422 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix308 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix308 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix308 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix308 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix308 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix308 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow308, value2436, value2895, value2981, value2986, value3422, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal311 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def boundaryMatrix311 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def boundaryRow311 : Integer.Sparse (Fin 909) := [(0, -3), (1, -76), (2, 172), (3, 1232), (4, 224), (5, -136), (6, 11), (7, 352), (8, 224), (9, -8), (12, 256), (13, 160), (23, -144), (24, -96), (26, 256), (33, -768), (35, 208), (52, 224), (54, -240), (55, -48), (69, 48), (70, 16), (71, 32), (81, -576), (100, 576), (104, 288), (125, -96), (126, -96), (228, -192), (256, -96), (277, -48), (291, 144), (379, 288)]

theorem boundarySound311 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow311 (momentVector H) = 0 := by
  have hshape : boundaryMatrix311 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix311 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix311 (0 : Fin 6)) =
      Sparse.eval value2982 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (0 : Fin 6) = raw9161 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9161 hH).trans (sound2982 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix311 (1 : Fin 6)) =
      Sparse.eval value2989 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (1 : Fin 6) = raw9579 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9579 hH).trans (sound2989 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix311 (2 : Fin 6)) =
      Sparse.eval value2989 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (2 : Fin 6) = raw9615 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9615 hH).trans (sound2989 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix311 (3 : Fin 6)) =
      Sparse.eval value2992 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (3 : Fin 6) = raw9633 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9633 hH).trans (sound2992 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix311 (4 : Fin 6)) =
      Sparse.eval value2897 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (4 : Fin 6) = raw9640 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9640 hH).trans (sound2897 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix311 (5 : Fin 6)) =
      Sparse.eval value3400 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (5 : Fin 6) = raw9641 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9641 hH).trans (sound3400 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix311 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix311 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix311 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix311 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix311 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix311 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow311, value2897, value2982, value2989, value2992, value3400, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal312 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def boundaryMatrix312 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def boundaryRow312 : Integer.Sparse (Fin 909) := [(0, -19), (1, -5), (2, 440), (3, 3680), (4, 160), (5, -1260), (6, 220), (7, 1760), (8, 320), (9, -160), (12, 400), (13, 2080), (23, -240), (26, 480), (35, 2720), (51, -480), (52, 3520), (54, -1200), (69, 560), (70, 400), (71, 160), (103, 2880), (125, -960), (126, -480), (228, -960), (256, -480), (277, -240), (291, 720), (322, 1440), (378, 1440), (818, -480)]

theorem boundarySound312 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow312 (momentVector H) = 0 := by
  have hshape : boundaryMatrix312 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix312 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix312 (0 : Fin 6)) =
      Sparse.eval value2958 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix312 (0 : Fin 6) = raw9155 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9155 hH).trans (sound2958 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix312 (1 : Fin 6)) =
      Sparse.eval value2962 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix312 (1 : Fin 6) = raw9573 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9573 hH).trans (sound2962 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix312 (2 : Fin 6)) =
      Sparse.eval value2962 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix312 (2 : Fin 6) = raw9609 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9609 hH).trans (sound2962 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix312 (3 : Fin 6)) =
      Sparse.eval value2984 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix312 (3 : Fin 6) = raw9619 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9619 hH).trans (sound2984 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix312 (4 : Fin 6)) =
      Sparse.eval value2896 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix312 (4 : Fin 6) = raw9623 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9623 hH).trans (sound2896 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix312 (5 : Fin 6)) =
      Sparse.eval value3392 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix312 (5 : Fin 6) = raw9624 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9624 hH).trans (sound3392 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix312 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix312 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix312 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix312 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix312 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix312 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow312, value2896, value2958, value2962, value2984, value3392, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal313 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def boundaryMatrix313 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def boundaryRow313 : Integer.Sparse (Fin 909) := [(0, -33), (1, 100), (2, 985), (3, 5680), (5, -1360), (6, 170), (7, 1680), (8, 960), (9, -120), (12, 1840), (13, 4720), (23, -720), (35, 2800), (51, -480), (52, 3520), (54, -240), (59, -1200), (69, 560), (70, 400), (71, 160), (98, 1440), (102, 2880), (125, -1440), (126, -480), (201, -960), (256, -480), (287, 720), (327, 1440), (352, 1440), (726, -240), (818, -480)]

theorem boundarySound313 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow313 (momentVector H) = 0 := by
  have hshape : boundaryMatrix313 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix313 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix313 (0 : Fin 6)) =
      Sparse.eval value2941 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix313 (0 : Fin 6) = raw9169 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9169 hH).trans (sound2941 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix313 (1 : Fin 6)) =
      Sparse.eval value2990 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix313 (1 : Fin 6) = raw9598 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9598 hH).trans (sound2990 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix313 (2 : Fin 6)) =
      Sparse.eval value2942 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix313 (2 : Fin 6) = raw9653 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9653 hH).trans (sound2942 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix313 (3 : Fin 6)) =
      Sparse.eval value2955 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix313 (3 : Fin 6) = raw9664 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9664 hH).trans (sound2955 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix313 (4 : Fin 6)) =
      Sparse.eval value2898 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix313 (4 : Fin 6) = raw9670 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9670 hH).trans (sound2898 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix313 (5 : Fin 6)) =
      Sparse.eval value3388 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix313 (5 : Fin 6) = raw9671 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9671 hH).trans (sound3388 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix313 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix313 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix313 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix313 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix313 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix313 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow313, value2898, value2941, value2942, value2955, value2990, value3388, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal314 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def boundaryMatrix314 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def boundaryRow314 : Integer.Sparse (Fin 909) := [(0, -19), (1, 50), (2, 170), (3, 2400), (5, -360), (6, 35), (7, 1760), (8, 800), (9, -40), (10, -480), (12, 960), (13, 880), (23, -240), (26, 320), (27, 360), (35, 720), (51, -1200), (52, 160), (55, -1200), (59, -480), (69, 240), (71, 240), (105, 1440), (124, -480), (228, -480), (236, -480), (256, -480), (277, -240), (290, 720), (352, 1440)]

theorem boundarySound314 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow314 (momentVector H) = 0 := by
  have hshape : boundaryMatrix314 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix314 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix314 (0 : Fin 6)) =
      Sparse.eval value2940 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix314 (0 : Fin 6) = raw8321 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8321 hH).trans (sound2940 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix314 (1 : Fin 6)) =
      Sparse.eval value2940 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix314 (1 : Fin 6) = raw9208 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9208 hH).trans (sound2940 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix314 (2 : Fin 6)) =
      Sparse.eval value2943 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix314 (2 : Fin 6) = raw9257 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9257 hH).trans (sound2943 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix314 (3 : Fin 6)) =
      Sparse.eval value2407 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix314 (3 : Fin 6) = raw9287 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9287 hH).trans (sound2407 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix314 (4 : Fin 6)) =
      Sparse.eval value2883 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix314 (4 : Fin 6) = raw9294 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9294 hH).trans (sound2883 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix314 (5 : Fin 6)) =
      Sparse.eval value3338 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix314 (5 : Fin 6) = raw9295 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9295 hH).trans (sound3338 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix314 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix314 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix314 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix314 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix314 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix314 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow314, value2407, value2883, value2940, value2943, value3338, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal315 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def boundaryMatrix315 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def boundaryRow315 : Integer.Sparse (Fin 909) := [(0, -3), (1, 14), (2, 7), (3, 368), (5, -36), (6, 16), (7, 448), (8, 96), (9, -40), (10, -48), (12, 80), (13, 64), (23, -144), (26, 96), (27, 36), (35, 208), (51, -48), (54, -48), (55, -240), (69, 160), (70, 64), (71, 96), (87, 288), (124, -240), (196, -96), (197, -48), (228, -288), (236, -96), (277, -48), (282, 144), (290, 144), (726, -48)]

theorem boundarySound315 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow315 (momentVector H) = 0 := by
  have hshape : boundaryMatrix315 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix315 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix315 (0 : Fin 6)) =
      Sparse.eval value2939 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix315 (0 : Fin 6) = raw8331 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8331 hH).trans (sound2939 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix315 (1 : Fin 6)) =
      Sparse.eval value2959 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix315 (1 : Fin 6) = raw9218 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9218 hH).trans (sound2959 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix315 (2 : Fin 6)) =
      Sparse.eval value2959 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix315 (2 : Fin 6) = raw9420 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9420 hH).trans (sound2959 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix315 (3 : Fin 6)) =
      Sparse.eval value3335 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix315 (3 : Fin 6) = raw9429 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9429 hH).trans (sound3335 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix315 (4 : Fin 6)) =
      Sparse.eval value2869 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix315 (4 : Fin 6) = raw9430 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9430 hH).trans (sound2869 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix315 (5 : Fin 6)) =
      Sparse.eval value3336 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix315 (5 : Fin 6) = raw9431 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9431 hH).trans (sound3336 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix315 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix315 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix315 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix315 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix315 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix315 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow315, value2869, value2939, value2959, value3335, value3336, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal332 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def boundaryMatrix332 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def boundaryRow332 : Integer.Sparse (Fin 909) := [(0, 1), (1, -320), (2, 200), (3, 2000), (4, 560), (5, -220), (6, 15), (7, 960), (9, -20), (12, 720), (13, 160), (23, -2160), (24, -2400), (25, -720), (27, 600), (35, 320), (48, 2160), (51, -720), (55, -1440), (63, -480), (68, 240), (69, 240), (70, 160), (124, -1440), (126, -1440), (196, -480), (197, -1440), (308, -240), (643, 1440), (751, 2160)]

theorem boundarySound332 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow332 (momentVector H) = 0 := by
  have hshape : boundaryMatrix332 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix332 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix332 (0 : Fin 6)) =
      Sparse.eval value3284 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix332 (0 : Fin 6) = raw9095 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9095 hH).trans (sound3284 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix332 (1 : Fin 6)) =
      Sparse.eval value3284 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix332 (1 : Fin 6) = raw9225 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9225 hH).trans (sound3284 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix332 (2 : Fin 6)) =
      Sparse.eval value1521 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix332 (2 : Fin 6) = raw9280 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9280 hH).trans (sound1521 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix332 (3 : Fin 6)) =
      Sparse.eval value3288 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix332 (3 : Fin 6) = raw9292 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9292 hH).trans (sound3288 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix332 (4 : Fin 6)) =
      Sparse.eval value3255 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix332 (4 : Fin 6) = raw9297 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9297 hH).trans (sound3255 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix332 (5 : Fin 6)) =
      Sparse.eval value3092 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix332 (5 : Fin 6) = raw9298 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9298 hH).trans (sound3092 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix332 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix332 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix332 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix332 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix332 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix332 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow332, value1521, value3092, value3255, value3284, value3288, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal337 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def boundaryMatrix337 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def boundaryRow337 : Integer.Sparse (Fin 909) := [(0, 54), (1, -660), (2, 935), (3, 4320), (4, 2000), (5, -940), (6, 45), (7, 1920), (8, 1920), (12, 240), (13, 160), (26, 1200), (31, -3600), (35, 800), (43, 2160), (51, -3600), (56, -1440), (77, 2160), (97, 4320), (107, 4320), (228, -240), (238, -2400), (737, 1440)]

theorem boundarySound337 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow337 (momentVector H) = 0 := by
  have hshape : boundaryMatrix337 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix337 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix337 (0 : Fin 6)) =
      Sparse.eval value3225 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix337 (0 : Fin 6) = raw9112 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9112 hH).trans (sound3225 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix337 (1 : Fin 6)) =
      Sparse.eval value3225 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix337 (1 : Fin 6) = raw9241 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9241 hH).trans (sound3225 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix337 (2 : Fin 6)) =
      Sparse.eval value3224 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix337 (2 : Fin 6) = raw9357 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9357 hH).trans (sound3224 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix337 (3 : Fin 6)) =
      Sparse.eval value3230 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix337 (3 : Fin 6) = raw9382 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9382 hH).trans (sound3230 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix337 (4 : Fin 6)) =
      Sparse.eval value2886 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix337 (4 : Fin 6) = raw9383 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9383 hH).trans (sound2886 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix337 (5 : Fin 6)) =
      Sparse.eval value3078 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix337 (5 : Fin 6) = raw9384 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9384 hH).trans (sound3078 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix337 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix337 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix337 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix337 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix337 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix337 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow337, value2886, value3078, value3224, value3225, value3230, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal338 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix338 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryRow338 : Integer.Sparse (Fin 909) := [(0, -3), (1, -190), (2, 385), (3, 2880), (4, 720), (5, -560), (6, 30), (7, 1440), (8, 960), (10, -1080), (11, 240), (12, 520), (13, 720), (26, 960), (35, 1120), (38, 1080), (40, 2160), (52, 240), (55, -1080), (59, -720), (72, 1080), (75, 2160), (199, -120), (228, -720), (321, 2160), (505, 720), (508, 4320), (727, -480)]

theorem boundarySound338 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow338 (momentVector H) = 0 := by
  have hshape : boundaryMatrix338 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix338 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix338 (0 : Fin 6)) =
      Sparse.eval value3121 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (0 : Fin 6) = raw9106 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9106 hH).trans (sound3121 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix338 (1 : Fin 6)) =
      Sparse.eval value3121 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (1 : Fin 6) = raw9235 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9235 hH).trans (sound3121 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix338 (2 : Fin 6)) =
      Sparse.eval value3120 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (2 : Fin 6) = raw9351 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9351 hH).trans (sound3120 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix338 (3 : Fin 6)) =
      Sparse.eval value3120 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (3 : Fin 6) = raw9360 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9360 hH).trans (sound3120 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix338 (4 : Fin 6)) =
      Sparse.eval value2880 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (4 : Fin 6) = raw9366 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9366 hH).trans (sound2880 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix338 (5 : Fin 6)) =
      Sparse.eval value2979 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (5 : Fin 6) = raw9367 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9367 hH).trans (sound2979 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix338 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix338 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix338 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix338 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix338 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix338 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow338, value2880, value2979, value3120, value3121, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal339 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryMatrix339 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryRow339 : Integer.Sparse (Fin 909) := [(0, 9), (1, -315), (2, 170), (3, 2880), (4, 960), (5, -680), (6, 120), (7, 960), (9, -20), (11, 480), (12, 240), (26, 960), (33, -2880), (35, 2080), (36, 2160), (40, 4320), (52, 1440), (54, -720), (55, -2160), (69, 240), (70, 160), (228, -1440), (306, -2160), (312, 4320), (498, 2160), (721, -1440), (723, -240), (728, -960), (760, 4320), (783, 1440), (794, 8640)]

theorem boundarySound339 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow339 (momentVector H) = 0 := by
  have hshape : boundaryMatrix339 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix339 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix339 (0 : Fin 6)) =
      Sparse.eval value3285 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix339 (0 : Fin 6) = raw9108 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9108 hH).trans (sound3285 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix339 (1 : Fin 6)) =
      Sparse.eval value3285 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix339 (1 : Fin 6) = raw9237 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9237 hH).trans (sound3285 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix339 (2 : Fin 6)) =
      Sparse.eval value3292 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix339 (2 : Fin 6) = raw9353 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9353 hH).trans (sound3292 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix339 (3 : Fin 6)) =
      Sparse.eval value3292 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix339 (3 : Fin 6) = raw9362 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9362 hH).trans (sound3292 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix339 (4 : Fin 6)) =
      Sparse.eval value3256 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix339 (4 : Fin 6) = raw9369 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9369 hH).trans (sound3256 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix339 (5 : Fin 6)) =
      Sparse.eval value2976 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix339 (5 : Fin 6) = raw9370 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9370 hH).trans (sound2976 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix339 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix339 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix339 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix339 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix339 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix339 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow339, value2976, value3256, value3285, value3292, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal340 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def boundaryMatrix340 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def boundaryRow340 : Integer.Sparse (Fin 909) := [(0, -29), (1, -490), (2, 485), (3, 3920), (5, -340), (7, 1840), (8, 160), (10, -240), (12, 1200), (13, 320), (23, -3360), (24, -2400), (25, -480), (26, 160), (27, 1020), (33, -480), (35, 160), (51, -2880), (54, -1200), (55, -2400), (65, -480), (79, 720), (94, 720), (122, 2880), (127, -240), (299, 1440), (300, 1440)]

theorem boundarySound340 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow340 (momentVector H) = 0 := by
  have hshape : boundaryMatrix340 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix340 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix340 (0 : Fin 6)) =
      Sparse.eval value2890 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix340 (0 : Fin 6) = raw9132 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9132 hH).trans (sound2890 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix340 (1 : Fin 6)) =
      Sparse.eval value1521 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix340 (1 : Fin 6) = raw9400 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9400 hH).trans (sound1521 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix340 (2 : Fin 6)) =
      Sparse.eval value2893 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix340 (2 : Fin 6) = raw9462 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9462 hH).trans (sound2893 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix340 (3 : Fin 6)) =
      Sparse.eval value2893 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix340 (3 : Fin 6) = raw9483 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9483 hH).trans (sound2893 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix340 (4 : Fin 6)) =
      Sparse.eval value2892 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix340 (4 : Fin 6) = raw9494 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9494 hH).trans (sound2892 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix340 (5 : Fin 6)) =
      Sparse.eval value2885 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix340 (5 : Fin 6) = raw9495 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9495 hH).trans (sound2885 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix340 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix340 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix340 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix340 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix340 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix340 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow340, value1521, value2885, value2890, value2892, value2893, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
