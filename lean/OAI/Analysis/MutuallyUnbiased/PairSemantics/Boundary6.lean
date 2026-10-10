import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound44
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical284
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical287
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical288
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical289
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical290
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical291
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical292
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical297
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical304
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical309
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical310
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical314
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical315

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal102 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def boundaryMatrix102 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def boundaryRow102 : Integer.Sparse (Fin 909) := [(0, 23), (1, -385), (2, 310), (3, 1720), (4, 760), (5, -210), (6, 10), (7, 280), (8, 360), (12, 160), (13, 80), (24, -240), (25, -240), (26, 400), (31, -720), (33, -600), (35, 120), (39, 720), (42, 720), (44, 360), (52, 200), (54, -240), (56, -120), (81, -240), (85, 360), (86, 360), (97, 360), (99, 720), (100, 360), (228, -120)]

theorem boundarySound102 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow102 (momentVector H) = 0 := by
  have hshape : boundaryMatrix102 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix102 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix102 (0 : Fin 6)) =
      Sparse.eval value2627 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix102 (0 : Fin 6) = raw9733 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9733 hH).trans (sound2627 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix102 (1 : Fin 6)) =
      Sparse.eval value3013 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix102 (1 : Fin 6) = raw9909 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9909 hH).trans (sound3013 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix102 (2 : Fin 6)) =
      Sparse.eval value3008 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix102 (2 : Fin 6) = raw9940 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9940 hH).trans (sound3008 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix102 (3 : Fin 6)) =
      Sparse.eval value3012 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix102 (3 : Fin 6) = raw9942 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9942 hH).trans (sound3012 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix102 (4 : Fin 6)) =
      Sparse.eval value3441 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix102 (4 : Fin 6) = raw9944 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9944 hH).trans (sound3441 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix102 (5 : Fin 6)) =
      Sparse.eval value2914 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix102 (5 : Fin 6) = raw9945 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9945 hH).trans (sound2914 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix102 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix102 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix102 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix102 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix102 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix102 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow102, value2627, value2914, value3008, value3012, value3013, value3441, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal103 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def boundaryMatrix103 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def boundaryRow103 : Integer.Sparse (Fin 909) := [(0, 21), (1, -255), (2, 170), (3, 880), (4, 432), (5, -88), (6, 4), (7, 80), (8, 192), (26, 288), (30, -96), (31, -96), (35, 32), (40, 288), (52, 80), (56, -96), (57, 288), (81, -96), (85, 144), (86, 144), (107, 288), (228, -48), (239, 288)]

theorem boundarySound103 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow103 (momentVector H) = 0 := by
  have hshape : boundaryMatrix103 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix103 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix103 (0 : Fin 6)) =
      Sparse.eval value2531 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix103 (0 : Fin 6) = raw9731 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9731 hH).trans (sound2531 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix103 (1 : Fin 6)) =
      Sparse.eval value3356 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix103 (1 : Fin 6) = raw9907 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9907 hH).trans (sound3356 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix103 (2 : Fin 6)) =
      Sparse.eval value3352 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix103 (2 : Fin 6) = raw9932 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9932 hH).trans (sound3352 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix103 (3 : Fin 6)) =
      Sparse.eval value3354 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix103 (3 : Fin 6) = raw9934 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9934 hH).trans (sound3354 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix103 (4 : Fin 6)) =
      Sparse.eval value3373 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix103 (4 : Fin 6) = raw9936 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9936 hH).trans (sound3373 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix103 (5 : Fin 6)) =
      Sparse.eval value2914 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix103 (5 : Fin 6) = raw9937 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9937 hH).trans (sound2914 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix103 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix103 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix103 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix103 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix103 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix103 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow103, value2531, value2914, value3352, value3354, value3356, value3373, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal104 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def boundaryMatrix104 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def boundaryRow104 : Integer.Sparse (Fin 909) := [(0, 3), (1, -113), (2, 53), (3, 640), (4, 240), (5, -26), (6, 1), (7, 72), (8, 32), (12, 200), (13, 144), (25, -72), (26, 176), (33, -120), (35, 80), (37, 144), (38, 144), (39, 288), (40, 288), (51, -48), (52, 64), (54, -48), (55, -240), (81, -48), (84, 72), (85, 144), (89, 144), (104, 72), (228, -72)]

theorem boundarySound104 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow104 (momentVector H) = 0 := by
  have hshape : boundaryMatrix104 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix104 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix104 (0 : Fin 6)) =
      Sparse.eval value2977 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix104 (0 : Fin 6) = raw10059 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10059 hH).trans (sound2977 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix104 (1 : Fin 6)) =
      Sparse.eval value2977 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix104 (1 : Fin 6) = raw10065 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10065 hH).trans (sound2977 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix104 (2 : Fin 6)) =
      Sparse.eval value2978 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix104 (2 : Fin 6) = raw10083 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10083 hH).trans (sound2978 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix104 (3 : Fin 6)) =
      Sparse.eval value2979 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix104 (3 : Fin 6) = raw10085 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10085 hH).trans (sound2979 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix104 (4 : Fin 6)) =
      Sparse.eval value3457 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix104 (4 : Fin 6) = raw10088 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10088 hH).trans (sound3457 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix104 (5 : Fin 6)) =
      Sparse.eval value2922 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix104 (5 : Fin 6) = raw10089 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10089 hH).trans (sound2922 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix104 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix104 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix104 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix104 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix104 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix104 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow104, value2922, value2977, value2978, value2979, value3457, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal105 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def boundaryMatrix105 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def boundaryRow105 : Integer.Sparse (Fin 909) := [(0, 7), (1, -235), (2, 111), (3, 1424), (4, 464), (5, -60), (6, 3), (7, 160), (8, 96), (12, 352), (13, 144), (23, -96), (25, -144), (26, 416), (31, -96), (33, -480), (35, 80), (36, 288), (37, 288), (39, 576), (40, 576), (52, 32), (54, -144), (55, -480), (81, -192), (83, 144), (85, 288), (87, 288), (100, 288), (228, -192)]

theorem boundarySound105 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow105 (momentVector H) = 0 := by
  have hshape : boundaryMatrix105 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix105 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix105 (0 : Fin 6)) =
      Sparse.eval value2977 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix105 (0 : Fin 6) = raw10058 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10058 hH).trans (sound2977 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix105 (1 : Fin 6)) =
      Sparse.eval value2977 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix105 (1 : Fin 6) = raw10064 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10064 hH).trans (sound2977 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix105 (2 : Fin 6)) =
      Sparse.eval value2975 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix105 (2 : Fin 6) = raw10082 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10082 hH).trans (sound2975 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix105 (3 : Fin 6)) =
      Sparse.eval value2976 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix105 (3 : Fin 6) = raw10084 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10084 hH).trans (sound2976 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix105 (4 : Fin 6)) =
      Sparse.eval value3455 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix105 (4 : Fin 6) = raw10086 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10086 hH).trans (sound3455 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix105 (5 : Fin 6)) =
      Sparse.eval value2918 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix105 (5 : Fin 6) = raw10087 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10087 hH).trans (sound2918 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix105 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix105 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix105 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix105 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix105 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix105 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow105, value2918, value2975, value2976, value2977, value3455, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal106 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def boundaryMatrix106 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def boundaryRow106 : Integer.Sparse (Fin 909) := [(0, 11), (1, -185), (2, 160), (3, 1680), (4, 360), (5, -90), (7, 480), (8, 120), (12, 880), (13, 80), (23, -360), (24, -600), (25, -360), (27, 180), (31, -240), (33, -240), (35, 80), (48, 360), (51, -600), (54, -240), (100, 720), (105, 720)]

theorem boundarySound106 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow106 (momentVector H) = 0 := by
  have hshape : boundaryMatrix106 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix106 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix106 (0 : Fin 6)) =
      Sparse.eval value3023 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix106 (0 : Fin 6) = raw8322 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8322 hH).trans (sound3023 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix106 (1 : Fin 6)) =
      Sparse.eval value3023 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix106 (1 : Fin 6) = raw9209 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9209 hH).trans (sound3023 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix106 (2 : Fin 6)) =
      Sparse.eval value3039 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix106 (2 : Fin 6) = raw9258 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9258 hH).trans (sound3039 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix106 (3 : Fin 6)) =
      Sparse.eval value2830 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix106 (3 : Fin 6) = raw9288 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9288 hH).trans (sound2830 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix106 (4 : Fin 6)) =
      Sparse.eval value3445 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix106 (4 : Fin 6) = raw9296 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9296 hH).trans (sound3445 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix106 (5 : Fin 6)) =
      Sparse.eval value3092 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix106 (5 : Fin 6) = raw9298 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9298 hH).trans (sound3092 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix106 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix106 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix106 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix106 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix106 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix106 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow106, value2830, value3023, value3039, value3092, value3445, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal107 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def boundaryMatrix107 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def boundaryRow107 : Integer.Sparse (Fin 909) := [(0, 21), (1, -333), (2, 124), (3, 1072), (4, 672), (5, -36), (7, 192), (8, 48), (12, 192), (23, -144), (24, -240), (25, -288), (26, 128), (27, 72), (31, -672), (35, 32), (46, 576), (47, 144), (51, -240), (54, -96), (97, 288), (106, 288)]

theorem boundarySound107 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow107 (momentVector H) = 0 := by
  have hshape : boundaryMatrix107 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix107 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix107 (0 : Fin 6)) =
      Sparse.eval value3027 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix107 (0 : Fin 6) = raw8328 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8328 hH).trans (sound3027 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix107 (1 : Fin 6)) =
      Sparse.eval value3027 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix107 (1 : Fin 6) = raw9215 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9215 hH).trans (sound3027 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix107 (2 : Fin 6)) =
      Sparse.eval value2831 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix107 (2 : Fin 6) = raw9286 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9286 hH).trans (sound2831 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix107 (3 : Fin 6)) =
      Sparse.eval value3040 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix107 (3 : Fin 6) = raw9336 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9336 hH).trans (sound3040 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix107 (4 : Fin 6)) =
      Sparse.eval value3444 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix107 (4 : Fin 6) = raw9342 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9342 hH).trans (sound3444 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix107 (5 : Fin 6)) =
      Sparse.eval value3094 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix107 (5 : Fin 6) = raw9343 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9343 hH).trans (sound3094 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix107 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix107 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix107 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix107 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix107 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix107 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow107, value2831, value3027, value3040, value3094, value3444, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal108 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def boundaryMatrix108 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def boundaryRow108 : Integer.Sparse (Fin 909) := [(0, -18), (1, -560), (2, 555), (3, 5200), (4, 720), (5, -440), (6, 25), (7, 1200), (8, 560), (10, -720), (12, 2240), (13, 3200), (26, 640), (33, -960), (35, 1040), (37, 720), (39, 720), (40, 720), (41, 1440), (51, -960), (52, 800), (54, -480), (55, -720), (59, -960), (73, 720), (74, 720), (75, 720), (95, 1440), (102, 720), (103, 720), (201, -240)]

theorem boundarySound108 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow108 (momentVector H) = 0 := by
  have hshape : boundaryMatrix108 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix108 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix108 (0 : Fin 6)) =
      Sparse.eval value2949 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix108 (0 : Fin 6) = raw8335 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8335 hH).trans (sound2949 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix108 (1 : Fin 6)) =
      Sparse.eval value3018 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix108 (1 : Fin 6) = raw9222 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9222 hH).trans (sound3018 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix108 (2 : Fin 6)) =
      Sparse.eval value2948 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix108 (2 : Fin 6) = raw9513 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9513 hH).trans (sound2948 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix108 (3 : Fin 6)) =
      Sparse.eval value2951 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix108 (3 : Fin 6) = raw9523 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9523 hH).trans (sound2951 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix108 (4 : Fin 6)) =
      Sparse.eval value2954 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix108 (4 : Fin 6) = raw9533 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9533 hH).trans (sound2954 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix108 (5 : Fin 6)) =
      Sparse.eval value3391 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix108 (5 : Fin 6) = raw9535 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9535 hH).trans (sound3391 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix108 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix108 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix108 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix108 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix108 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix108 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow108, value2948, value2949, value2951, value2954, value3018, value3391, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal128 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def boundaryMatrix128 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def boundaryRow128 : Integer.Sparse (Fin 909) := [(0, 4), (1, -44), (2, 7), (5, -12), (6, 3), (23, -144), (25, -144), (27, 84), (30, -144), (31, -288), (63, -96), (68, 24), (105, 432), (124, -144), (196, -48), (236, -288), (237, -144)]

theorem boundarySound128 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow128 (momentVector H) = 0 := by
  have hshape : boundaryMatrix128 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix128 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix128 (0 : Fin 6)) =
      Sparse.eval value3313 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix128 (0 : Fin 6) = raw9098 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9098 hH).trans (sound3313 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix128 (1 : Fin 6)) =
      Sparse.eval value3313 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix128 (1 : Fin 6) = raw9228 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9228 hH).trans (sound3313 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix128 (2 : Fin 6)) =
      Sparse.eval value1524 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix128 (2 : Fin 6) = raw9283 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9283 hH).trans (sound1524 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix128 (3 : Fin 6)) =
      Sparse.eval value3312 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix128 (3 : Fin 6) = raw9303 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9303 hH).trans (sound3312 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix128 (4 : Fin 6)) =
      Sparse.eval value3312 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix128 (4 : Fin 6) = raw9307 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9307 hH).trans (sound3312 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix128 (5 : Fin 6)) =
      Sparse.eval value3043 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix128 (5 : Fin 6) = raw9308 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9308 hH).trans (sound3043 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix128 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix128 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix128 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix128 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix128 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix128 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow128, value1524, value3043, value3312, value3313, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal129 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def boundaryMatrix129 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def boundaryRow129 : Integer.Sparse (Fin 909) := [(0, 6), (1, -53), (2, 119), (3, 240), (5, -112), (6, 6), (7, 144), (8, 288), (12, 96), (13, 32), (23, -144), (27, 108), (30, -288), (35, 32), (51, -288), (54, -144), (68, 24), (124, -144), (196, -48), (236, -288)]

theorem boundarySound129 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow129 (momentVector H) = 0 := by
  have hshape : boundaryMatrix129 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix129 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix129 (0 : Fin 6)) =
      Sparse.eval value3244 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix129 (0 : Fin 6) = raw9103 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9103 hH).trans (sound3244 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix129 (1 : Fin 6)) =
      Sparse.eval value3244 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix129 (1 : Fin 6) = raw9233 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9233 hH).trans (sound3244 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix129 (2 : Fin 6)) =
      Sparse.eval value2888 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix129 (2 : Fin 6) = raw9326 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9326 hH).trans (sound2888 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix129 (3 : Fin 6)) =
      Sparse.eval value3242 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix129 (3 : Fin 6) = raw9335 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9335 hH).trans (sound3242 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix129 (4 : Fin 6)) =
      Sparse.eval value3242 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix129 (4 : Fin 6) = raw9338 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9338 hH).trans (sound3242 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix129 (5 : Fin 6)) =
      Sparse.eval value3046 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix129 (5 : Fin 6) = raw9339 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9339 hH).trans (sound3046 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix129 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix129 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix129 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix129 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix129 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix129 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow129, value2888, value3046, value3242, value3244, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal130 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def boundaryMatrix130 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def boundaryRow130 : Integer.Sparse (Fin 909) := [(0, 37), (1, -930), (2, 975), (3, 4880), (4, 1360), (5, -840), (6, 40), (7, 1760), (8, 1920), (12, 960), (13, 480), (23, -480), (24, -1440), (26, 640), (27, 600), (30, -960), (31, -960), (35, 800), (51, -4320), (52, 320), (54, -960), (55, -480), (56, -1200), (95, 1440), (97, 720), (107, 1440), (238, -720)]

theorem boundarySound130 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow130 (momentVector H) = 0 := by
  have hshape : boundaryMatrix130 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix130 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix130 (0 : Fin 6)) =
      Sparse.eval value3234 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix130 (0 : Fin 6) = raw8326 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8326 hH).trans (sound3234 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix130 (1 : Fin 6)) =
      Sparse.eval value3234 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix130 (1 : Fin 6) = raw9213 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9213 hH).trans (sound3234 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix130 (2 : Fin 6)) =
      Sparse.eval value3466 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix130 (2 : Fin 6) = raw9278 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9278 hH).trans (sound3466 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix130 (3 : Fin 6)) =
      Sparse.eval value3243 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix130 (3 : Fin 6) = raw9319 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9319 hH).trans (sound3243 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix130 (4 : Fin 6)) =
      Sparse.eval value2888 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix130 (4 : Fin 6) = raw9326 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9326 hH).trans (sound2888 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix130 (5 : Fin 6)) =
      Sparse.eval value3440 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix130 (5 : Fin 6) = raw9327 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9327 hH).trans (sound3440 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix130 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix130 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix130 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix130 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix130 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix130 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow130, value2888, value3234, value3243, value3440, value3466, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal131 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def boundaryMatrix131 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def boundaryRow131 : Integer.Sparse (Fin 909) := [(0, -1), (1, 110), (2, 5), (14, 2160), (23, -2400), (25, -1440), (63, -1440), (68, 60), (124, -960), (129, 1440), (196, -480), (230, 2160)]

theorem boundarySound131 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow131 (momentVector H) = 0 := by
  have hshape : boundaryMatrix131 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix131 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix131 (0 : Fin 6)) =
      Sparse.eval value3318 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (0 : Fin 6) = raw9094 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9094 hH).trans (sound3318 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix131 (1 : Fin 6)) =
      Sparse.eval value3318 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (1 : Fin 6) = raw9224 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9224 hH).trans (sound3318 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix131 (2 : Fin 6)) =
      Sparse.eval value1746 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (2 : Fin 6) = raw9279 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9279 hH).trans (sound1746 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix131 (3 : Fin 6)) =
      Sparse.eval value1746 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (3 : Fin 6) = raw9289 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9289 hH).trans (sound1746 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix131 (4 : Fin 6)) =
      Sparse.eval value3317 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (4 : Fin 6) = raw9290 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9290 hH).trans (sound3317 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix131 (5 : Fin 6)) =
      Sparse.eval value3165 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (5 : Fin 6) = raw9291 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9291 hH).trans (sound3165 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix131 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix131 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix131 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix131 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix131 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix131 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow131, value1746, value3165, value3317, value3318, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal133 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def boundaryMatrix133 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def boundaryRow133 : Integer.Sparse (Fin 909) := [(0, -2), (1, -455), (2, 195), (3, 3040), (4, 720), (5, -80), (7, 480), (12, 1840), (13, 480), (15, 2160), (23, -2160), (24, -720), (25, -1440), (27, 420), (33, -1440), (35, 160), (51, -1440), (54, -1440), (63, -480), (68, 60), (124, -720), (126, -240), (144, 1440), (196, -480), (205, 2160)]

theorem boundarySound133 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow133 (momentVector H) = 0 := by
  have hshape : boundaryMatrix133 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix133 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix133 (0 : Fin 6)) =
      Sparse.eval value3258 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix133 (0 : Fin 6) = raw9096 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9096 hH).trans (sound3258 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix133 (1 : Fin 6)) =
      Sparse.eval value3258 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix133 (1 : Fin 6) = raw9226 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9226 hH).trans (sound3258 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix133 (2 : Fin 6)) =
      Sparse.eval value1749 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix133 (2 : Fin 6) = raw9281 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9281 hH).trans (sound1749 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix133 (3 : Fin 6)) =
      Sparse.eval value3030 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix133 (3 : Fin 6) = raw9293 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9293 hH).trans (sound3030 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix133 (4 : Fin 6)) =
      Sparse.eval value3257 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix133 (4 : Fin 6) = raw9299 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9299 hH).trans (sound3257 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix133 (5 : Fin 6)) =
      Sparse.eval value3166 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix133 (5 : Fin 6) = raw9300 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9300 hH).trans (sound3166 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix133 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix133 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix133 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix133 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix133 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix133 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow133, value1749, value3030, value3166, value3257, value3258, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal134 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def boundaryMatrix134 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def boundaryRow134 : Integer.Sparse (Fin 909) := [(0, 8), (1, -30), (2, 25), (5, -12), (6, 3), (17, 432), (23, -288), (25, -624), (27, 48), (30, -144), (31, -576), (63, -96), (68, 12), (87, 432), (108, 432), (123, -432), (124, -144), (196, -96), (203, 432), (216, 288), (226, -144), (236, -48), (237, -144)]

theorem boundarySound134 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow134 (momentVector H) = 0 := by
  have hshape : boundaryMatrix134 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix134 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix134 (0 : Fin 6)) =
      Sparse.eval value3327 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix134 (0 : Fin 6) = raw9097 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9097 hH).trans (sound3327 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix134 (1 : Fin 6)) =
      Sparse.eval value3327 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix134 (1 : Fin 6) = raw9227 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9227 hH).trans (sound3327 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix134 (2 : Fin 6)) =
      Sparse.eval value1752 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix134 (2 : Fin 6) = raw9282 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9282 hH).trans (sound1752 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix134 (3 : Fin 6)) =
      Sparse.eval value3329 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix134 (3 : Fin 6) = raw9302 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9302 hH).trans (sound3329 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix134 (4 : Fin 6)) =
      Sparse.eval value3319 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix134 (4 : Fin 6) = raw9305 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9305 hH).trans (sound3319 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix134 (5 : Fin 6)) =
      Sparse.eval value3167 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix134 (5 : Fin 6) = raw9306 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9306 hH).trans (sound3167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix134 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix134 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix134 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix134 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix134 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix134 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow134, value1752, value3167, value3319, value3327, value3329, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal135 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def boundaryMatrix135 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def boundaryRow135 : Integer.Sparse (Fin 909) := [(0, 52), (1, -425), (2, 55), (17, 2160), (23, -1440), (25, -3600), (27, 480), (30, -960), (31, -4080), (63, -960), (105, 2160), (108, 2160), (123, -720), (231, 1440), (237, -720)]

theorem boundarySound135 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow135 (momentVector H) = 0 := by
  have hshape : boundaryMatrix135 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix135 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix135 (0 : Fin 6)) =
      Sparse.eval value3322 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix135 (0 : Fin 6) = raw9099 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9099 hH).trans (sound3322 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix135 (1 : Fin 6)) =
      Sparse.eval value3322 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix135 (1 : Fin 6) = raw9229 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9229 hH).trans (sound3322 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix135 (2 : Fin 6)) =
      Sparse.eval value1823 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix135 (2 : Fin 6) = raw9284 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9284 hH).trans (sound1823 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix135 (3 : Fin 6)) =
      Sparse.eval value3321 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix135 (3 : Fin 6) = raw9304 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9304 hH).trans (sound3321 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix135 (4 : Fin 6)) =
      Sparse.eval value3043 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix135 (4 : Fin 6) = raw9308 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9308 hH).trans (sound3043 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix135 (5 : Fin 6)) =
      Sparse.eval value3167 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix135 (5 : Fin 6) = raw9309 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9309 hH).trans (sound3167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix135 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix135 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix135 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix135 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix135 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix135 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow135, value1823, value3043, value3167, value3321, value3322, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal138 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def boundaryMatrix138 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def boundaryRow138 : Integer.Sparse (Fin 909) := [(0, -9), (1, -845), (2, 530), (3, 6960), (5, -160), (7, 960), (12, 3440), (13, 4560), (16, 2160), (23, -2880), (27, 540), (35, 320), (38, 4320), (51, -2880), (54, -2880), (55, -1440), (68, 60), (124, -720), (125, -240), (140, 2160), (141, 1440), (196, -480)]

theorem boundarySound138 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow138 (momentVector H) = 0 := by
  have hshape : boundaryMatrix138 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix138 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix138 (0 : Fin 6)) =
      Sparse.eval value3137 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix138 (0 : Fin 6) = raw9101 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9101 hH).trans (sound3137 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix138 (1 : Fin 6)) =
      Sparse.eval value3137 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix138 (1 : Fin 6) = raw9231 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9231 hH).trans (sound3137 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix138 (2 : Fin 6)) =
      Sparse.eval value2966 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix138 (2 : Fin 6) = raw9314 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9314 hH).trans (sound2966 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix138 (3 : Fin 6)) =
      Sparse.eval value2966 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix138 (3 : Fin 6) = raw9330 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9330 hH).trans (sound2966 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix138 (4 : Fin 6)) =
      Sparse.eval value3135 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix138 (4 : Fin 6) = raw9331 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9331 hH).trans (sound3135 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix138 (5 : Fin 6)) =
      Sparse.eval value3168 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix138 (5 : Fin 6) = raw9332 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9332 hH).trans (sound3168 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix138 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix138 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix138 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix138 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix138 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix138 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow138, value2966, value3135, value3137, value3168, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal139 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

def boundaryMatrix139 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

def boundaryRow139 : Integer.Sparse (Fin 909) := [(0, 101), (1, -2045), (2, 420), (3, 8560), (4, 3280), (5, -20), (7, 240), (12, 2640), (13, 480), (18, 2160), (23, -1440), (24, -1440), (25, -1440), (26, 1760), (27, 240), (31, -1440), (33, -1440), (35, 160), (43, 4320), (47, 2160), (51, -240), (55, -1440), (63, -480), (143, 1440)]

theorem boundarySound139 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow139 (momentVector H) = 0 := by
  have hshape : boundaryMatrix139 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix139 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix139 (0 : Fin 6)) =
      Sparse.eval value3268 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix139 (0 : Fin 6) = raw9104 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9104 hH).trans (sound3268 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix139 (1 : Fin 6)) =
      Sparse.eval value3268 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix139 (1 : Fin 6) = raw9234 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9234 hH).trans (sound3268 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix139 (2 : Fin 6)) =
      Sparse.eval value3045 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix139 (2 : Fin 6) = raw9328 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9328 hH).trans (sound3045 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix139 (3 : Fin 6)) =
      Sparse.eval value3086 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix139 (3 : Fin 6) = raw9341 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9341 hH).trans (sound3086 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix139 (4 : Fin 6)) =
      Sparse.eval value3094 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix139 (4 : Fin 6) = raw9343 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9343 hH).trans (sound3094 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix139 (5 : Fin 6)) =
      Sparse.eval value3207 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix139 (5 : Fin 6) = raw9344 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9344 hH).trans (sound3207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix139 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix139 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix139 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix139 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix139 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix139 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow139, value3045, value3086, value3094, value3207, value3268, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
