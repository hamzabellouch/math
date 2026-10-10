import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical108
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical232
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical266
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical267
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical268
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical269
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical270
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical271
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical272
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical284
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical288
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical291
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical293
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical294
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical295
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical296
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical297
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical298
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical299
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical300
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical308

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal0 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def boundaryMatrix0 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def boundaryRow0 : Integer.Sparse (Fin 909) := [(0, 9), (1, 170), (2, -25), (3, -80), (4, -160), (12, -40)]

theorem boundarySound0 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow0 (momentVector H) = 0 := by
  have hshape : boundaryMatrix0 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix0 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix0 (0 : Fin 6)) =
      Sparse.eval value2137 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix0 (0 : Fin 6) = raw4066 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical4066 hH).trans (sound2137 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix0 (1 : Fin 6)) =
      Sparse.eval value2660 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix0 (1 : Fin 6) = raw7371 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7371 hH).trans (sound2660 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix0 (2 : Fin 6)) =
      Sparse.eval value2796 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix0 (2 : Fin 6) = raw7424 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7424 hH).trans (sound2796 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix0 (3 : Fin 6)) =
      Sparse.eval value2796 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix0 (3 : Fin 6) = raw7438 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7438 hH).trans (sound2796 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix0 (4 : Fin 6)) =
      Sparse.eval value2800 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix0 (4 : Fin 6) = raw7439 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7439 hH).trans (sound2800 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix0 (5 : Fin 6)) =
      Sparse.eval value1294 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix0 (5 : Fin 6) = raw7440 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7440 hH).trans (sound1294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix0 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix0 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix0 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix0 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix0 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix0 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow0, value1294, value2137, value2660, value2796, value2800, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal1 : Matrix (Fin 7) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def boundaryMatrix1 : Matrix (Fin 7) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def boundaryRow1 : Integer.Sparse (Fin 909) := [(0, -1), (1, -4), (5, -8), (6, 1), (27, 12)]

theorem boundarySound1 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow1 (momentVector H) = 0 := by
  have hshape : boundaryMatrix1 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix1 1 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix1 (0 : Fin 6)) =
      Sparse.eval value717 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (0 : Fin 6) = raw5120 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5120 hH).trans (sound717 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix1 (1 : Fin 6)) =
      Sparse.eval value717 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (1 : Fin 6) = raw7624 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7624 hH).trans (sound717 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix1 (2 : Fin 6)) =
      Sparse.eval value717 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (2 : Fin 6) = raw7646 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7646 hH).trans (sound717 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix1 (3 : Fin 6)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (3 : Fin 6) = raw7654 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7654 hH).trans (sound232 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix1 (4 : Fin 6)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (4 : Fin 6) = raw7657 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7657 hH).trans (sound232 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix1 (5 : Fin 6)) =
      Sparse.eval value1323 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (5 : Fin 6) = raw7658 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7658 hH).trans (sound1323 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix1 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix1 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix1 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix1 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix1 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix1 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow1, value1323, value232, value717, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal2 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def boundaryMatrix2 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def boundaryRow2 : Integer.Sparse (Fin 909) := [(0, -1), (1, 18), (2, -8), (3, -64), (4, -32), (5, 3), (7, -16), (8, -8), (12, -24), (23, 12), (24, 24)]

theorem boundarySound2 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow2 (momentVector H) = 0 := by
  have hshape : boundaryMatrix2 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix2 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix2 (0 : Fin 6)) =
      Sparse.eval value2120 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix2 (0 : Fin 6) = raw8201 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8201 hH).trans (sound2120 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix2 (1 : Fin 6)) =
      Sparse.eval value1291 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix2 (1 : Fin 6) = raw8679 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8679 hH).trans (sound1291 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix2 (2 : Fin 6)) =
      Sparse.eval value1291 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix2 (2 : Fin 6) = raw8705 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8705 hH).trans (sound1291 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix2 (3 : Fin 6)) =
      Sparse.eval value2137 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix2 (3 : Fin 6) = raw8725 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8725 hH).trans (sound2137 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix2 (4 : Fin 6)) =
      Sparse.eval value2137 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix2 (4 : Fin 6) = raw8730 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8730 hH).trans (sound2137 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix2 (5 : Fin 6)) =
      Sparse.eval value1884 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix2 (5 : Fin 6) = raw8731 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8731 hH).trans (sound1884 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix2 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix2 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix2 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix2 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix2 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix2 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow2, value1291, value1884, value2120, value2137, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal3 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def boundaryMatrix3 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def boundaryRow3 : Integer.Sparse (Fin 909) := [(0, -9), (1, 205), (2, -110), (3, -160), (4, -160), (5, 30), (7, -40), (8, -200), (24, 120), (30, 240)]

theorem boundarySound3 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow3 (momentVector H) = 0 := by
  have hshape : boundaryMatrix3 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix3 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix3 (0 : Fin 6)) =
      Sparse.eval value2651 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix3 (0 : Fin 6) = raw6849 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6849 hH).trans (sound2651 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix3 (1 : Fin 6)) =
      Sparse.eval value2660 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix3 (1 : Fin 6) = raw8540 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8540 hH).trans (sound2660 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix3 (2 : Fin 6)) =
      Sparse.eval value2660 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix3 (2 : Fin 6) = raw8695 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8695 hH).trans (sound2660 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix3 (3 : Fin 6)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix3 (3 : Fin 6) = raw8714 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8714 hH).trans (sound1151 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix3 (4 : Fin 6)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix3 (4 : Fin 6) = raw8729 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8729 hH).trans (sound1151 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix3 (5 : Fin 6)) =
      Sparse.eval value1884 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix3 (5 : Fin 6) = raw8731 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8731 hH).trans (sound1884 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix3 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix3 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix3 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix3 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix3 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix3 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow3, value1151, value1884, value2651, value2660, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal4 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def boundaryMatrix4 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def boundaryRow4 : Integer.Sparse (Fin 909) := [(0, -4), (1, 95), (2, -25), (3, -320), (4, -160), (12, -160), (13, -80)]

theorem boundarySound4 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow4 (momentVector H) = 0 := by
  have hshape : boundaryMatrix4 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix4 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix4 (0 : Fin 6)) =
      Sparse.eval value2139 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix4 (0 : Fin 6) = raw8181 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8181 hH).trans (sound2139 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix4 (1 : Fin 6)) =
      Sparse.eval value2139 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix4 (1 : Fin 6) = raw8558 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8558 hH).trans (sound2139 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix4 (2 : Fin 6)) =
      Sparse.eval value668 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix4 (2 : Fin 6) = raw8611 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8611 hH).trans (sound668 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix4 (3 : Fin 6)) =
      Sparse.eval value2137 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix4 (3 : Fin 6) = raw8635 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8635 hH).trans (sound2137 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix4 (4 : Fin 6)) =
      Sparse.eval value2137 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix4 (4 : Fin 6) = raw8642 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8642 hH).trans (sound2137 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix4 (5 : Fin 6)) =
      Sparse.eval value2306 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix4 (5 : Fin 6) = raw8643 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8643 hH).trans (sound2306 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix4 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix4 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix4 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix4 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix4 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix4 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow4, value2137, value2139, value2306, value668, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal5 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def boundaryMatrix5 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def boundaryRow5 : Integer.Sparse (Fin 909) := [(0, -11), (1, 250), (2, -45), (3, -800), (4, -480), (12, -320), (25, 120), (26, -160)]

theorem boundarySound5 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow5 (momentVector H) = 0 := by
  have hshape : boundaryMatrix5 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix5 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix5 (0 : Fin 6)) =
      Sparse.eval value2301 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix5 (0 : Fin 6) = raw8199 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8199 hH).trans (sound2301 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix5 (1 : Fin 6)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix5 (1 : Fin 6) = raw8677 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8677 hH).trans (sound711 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix5 (2 : Fin 6)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix5 (2 : Fin 6) = raw8701 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8701 hH).trans (sound711 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix5 (3 : Fin 6)) =
      Sparse.eval value2305 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix5 (3 : Fin 6) = raw8717 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8717 hH).trans (sound2305 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix5 (4 : Fin 6)) =
      Sparse.eval value2306 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix5 (4 : Fin 6) = raw8724 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8724 hH).trans (sound2306 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix5 (5 : Fin 6)) =
      Sparse.eval value2137 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix5 (5 : Fin 6) = raw8725 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8725 hH).trans (sound2137 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix5 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix5 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix5 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix5 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix5 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix5 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow5, value2137, value2301, value2305, value2306, value711, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal6 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1]]

def boundaryMatrix6 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1]]

def boundaryRow6 : Integer.Sparse (Fin 909) := [(0, -9), (1, 315), (2, -70), (3, -480), (4, -400), (12, -80), (26, -80), (31, 240)]

theorem boundarySound6 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow6 (momentVector H) = 0 := by
  have hshape : boundaryMatrix6 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix6 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix6 (0 : Fin 6)) =
      Sparse.eval value2669 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix6 (0 : Fin 6) = raw6811 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6811 hH).trans (sound2669 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix6 (1 : Fin 6)) =
      Sparse.eval value2669 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix6 (1 : Fin 6) = raw8529 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8529 hH).trans (sound2669 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix6 (2 : Fin 6)) =
      Sparse.eval value2660 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix6 (2 : Fin 6) = raw8576 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8576 hH).trans (sound2660 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix6 (3 : Fin 6)) =
      Sparse.eval value2675 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix6 (3 : Fin 6) = raw8616 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8616 hH).trans (sound2675 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix6 (4 : Fin 6)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix6 (4 : Fin 6) = raw8634 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8634 hH).trans (sound1151 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix6 (5 : Fin 6)) =
      Sparse.eval value2137 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix6 (5 : Fin 6) = raw8635 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8635 hH).trans (sound2137 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix6 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix6 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix6 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix6 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix6 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix6 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow6, value1151, value2137, value2660, value2669, value2675, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal7 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def boundaryMatrix7 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def boundaryRow7 : Integer.Sparse (Fin 909) := [(0, 1), (1, -8), (2, 4), (14, 18), (17, 72), (23, -48), (25, -96), (27, 9), (30, -24), (31, -96)]

theorem boundarySound7 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow7 (momentVector H) = 0 := by
  have hshape : boundaryMatrix7 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix7 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix7 (0 : Fin 6)) =
      Sparse.eval value3155 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix7 (0 : Fin 6) = raw9119 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9119 hH).trans (sound3155 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix7 (1 : Fin 6)) =
      Sparse.eval value2851 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix7 (1 : Fin 6) = raw9388 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9388 hH).trans (sound2851 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix7 (2 : Fin 6)) =
      Sparse.eval value2851 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix7 (2 : Fin 6) = raw9426 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9426 hH).trans (sound2851 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix7 (3 : Fin 6)) =
      Sparse.eval value3167 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix7 (3 : Fin 6) = raw9440 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9440 hH).trans (sound3167 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix7 (4 : Fin 6)) =
      Sparse.eval value3167 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix7 (4 : Fin 6) = raw9443 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9443 hH).trans (sound3167 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix7 (5 : Fin 6)) =
      Sparse.eval value3043 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix7 (5 : Fin 6) = raw9444 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9444 hH).trans (sound3043 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix7 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix7 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix7 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix7 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix7 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix7 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow7, value2851, value3043, value3155, value3167, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal8 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def boundaryMatrix8 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def boundaryRow8 : Integer.Sparse (Fin 909) := [(0, 149), (1, -1760), (2, 285), (3, 2080), (4, 2880), (12, 800), (15, 720), (20, 1440), (23, -240), (24, -720), (25, -480), (27, 180), (30, -480), (31, -960)]

theorem boundarySound8 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow8 (momentVector H) = 0 := by
  have hshape : boundaryMatrix8 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix8 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix8 (0 : Fin 6)) =
      Sparse.eval value3170 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix8 (0 : Fin 6) = raw9135 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9135 hH).trans (sound3170 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix8 (1 : Fin 6)) =
      Sparse.eval value2734 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix8 (1 : Fin 6) = raw9403 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9403 hH).trans (sound2734 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix8 (2 : Fin 6)) =
      Sparse.eval value3433 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix8 (2 : Fin 6) = raw9470 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9470 hH).trans (sound3433 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix8 (3 : Fin 6)) =
      Sparse.eval value3199 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix8 (3 : Fin 6) = raw9499 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9499 hH).trans (sound3199 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix8 (4 : Fin 6)) =
      Sparse.eval value3199 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix8 (4 : Fin 6) = raw9502 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9502 hH).trans (sound3199 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix8 (5 : Fin 6)) =
      Sparse.eval value3433 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix8 (5 : Fin 6) = raw9503 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9503 hH).trans (sound3433 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix8 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix8 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix8 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix8 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix8 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix8 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow8, value2734, value3170, value3199, value3433, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal9 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def boundaryMatrix9 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def boundaryRow9 : Integer.Sparse (Fin 909) := [(0, -11), (1, -150), (2, 80), (3, 640), (4, 320), (12, 240), (16, 180), (17, 360), (23, -240), (27, 45), (30, -120)]

theorem boundarySound9 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow9 (momentVector H) = 0 := by
  have hshape : boundaryMatrix9 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix9 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix9 (0 : Fin 6)) =
      Sparse.eval value3168 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix9 (0 : Fin 6) = raw9157 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9157 hH).trans (sound3168 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix9 (1 : Fin 6)) =
      Sparse.eval value3437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix9 (1 : Fin 6) = raw9575 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9575 hH).trans (sound3437 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix9 (2 : Fin 6)) =
      Sparse.eval value3437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix9 (2 : Fin 6) = raw9611 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9611 hH).trans (sound3437 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix9 (3 : Fin 6)) =
      Sparse.eval value3169 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix9 (3 : Fin 6) = raw9621 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9621 hH).trans (sound3169 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix9 (4 : Fin 6)) =
      Sparse.eval value3169 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix9 (4 : Fin 6) = raw9627 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9627 hH).trans (sound3169 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix9 (5 : Fin 6)) =
      Sparse.eval value3397 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix9 (5 : Fin 6) = raw9628 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9628 hH).trans (sound3397 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix9 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix9 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix9 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix9 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix9 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix9 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow9, value3168, value3169, value3397, value3437, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal10 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def boundaryMatrix10 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def boundaryRow10 : Integer.Sparse (Fin 909) := [(0, 11), (1, -890), (2, 45), (3, 1120), (4, 1080), (12, 440), (18, 360), (22, 720)]

theorem boundarySound10 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow10 (momentVector H) = 0 := by
  have hshape : boundaryMatrix10 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix10 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix10 (0 : Fin 6)) =
      Sparse.eval value2607 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix10 (0 : Fin 6) = raw9721 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9721 hH).trans (sound2607 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix10 (1 : Fin 6)) =
      Sparse.eval value3217 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix10 (1 : Fin 6) = raw9868 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9868 hH).trans (sound3217 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix10 (2 : Fin 6)) =
      Sparse.eval value3397 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix10 (2 : Fin 6) = raw9879 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9879 hH).trans (sound3397 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix10 (3 : Fin 6)) =
      Sparse.eval value3216 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix10 (3 : Fin 6) = raw9882 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9882 hH).trans (sound3216 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix10 (4 : Fin 6)) =
      Sparse.eval value3216 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix10 (4 : Fin 6) = raw9886 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9886 hH).trans (sound3216 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix10 (5 : Fin 6)) =
      Sparse.eval value3437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix10 (5 : Fin 6) = raw9887 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9887 hH).trans (sound3437 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix10 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix10 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix10 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix10 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix10 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix10 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow10, value2607, value3216, value3217, value3397, value3437, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal11 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def boundaryMatrix11 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def boundaryRow11 : Integer.Sparse (Fin 909) := [(0, 12), (1, -121), (2, 33), (3, 320), (4, 224), (12, 192), (15, 144), (17, 72), (23, -72), (24, -48), (25, -144), (27, 18), (30, -24), (31, -144)]

theorem boundarySound11 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow11 (momentVector H) = 0 := by
  have hshape : boundaryMatrix11 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix11 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix11 (0 : Fin 6)) =
      Sparse.eval value3170 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (0 : Fin 6) = raw8332 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8332 hH).trans (sound3170 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix11 (1 : Fin 6)) =
      Sparse.eval value3436 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (1 : Fin 6) = raw9219 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9219 hH).trans (sound3436 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix11 (2 : Fin 6)) =
      Sparse.eval value3436 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (2 : Fin 6) = raw9421 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9421 hH).trans (sound3436 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix11 (3 : Fin 6)) =
      Sparse.eval value3166 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (3 : Fin 6) = raw9438 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9438 hH).trans (sound3166 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix11 (4 : Fin 6)) =
      Sparse.eval value3167 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (4 : Fin 6) = raw9443 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9443 hH).trans (sound3167 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix11 (5 : Fin 6)) =
      Sparse.eval value3393 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (5 : Fin 6) = raw9445 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9445 hH).trans (sound3393 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix11 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix11 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix11 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix11 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix11 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix11 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow11, value3166, value3167, value3170, value3393, value3436, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal12 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def boundaryMatrix12 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def boundaryRow12 : Integer.Sparse (Fin 909) := [(0, 3), (1, -65), (2, 11), (3, 80), (4, 80), (12, 20), (17, 36), (19, 36), (20, 36), (22, 36), (24, -60), (27, 9), (30, -12), (31, -48)]

theorem boundarySound12 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow12 (momentVector H) = 0 := by
  have hshape : boundaryMatrix12 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix12 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix12 (0 : Fin 6)) =
      Sparse.eval value3200 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix12 (0 : Fin 6) = raw8334 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8334 hH).trans (sound3200 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix12 (1 : Fin 6)) =
      Sparse.eval value3434 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix12 (1 : Fin 6) = raw9221 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9221 hH).trans (sound3434 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix12 (2 : Fin 6)) =
      Sparse.eval value2724 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix12 (2 : Fin 6) = raw9427 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9427 hH).trans (sound2724 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix12 (3 : Fin 6)) =
      Sparse.eval value3198 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix12 (3 : Fin 6) = raw9497 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9497 hH).trans (sound3198 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix12 (4 : Fin 6)) =
      Sparse.eval value3199 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix12 (4 : Fin 6) = raw9502 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9502 hH).trans (sound3199 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix12 (5 : Fin 6)) =
      Sparse.eval value3442 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix12 (5 : Fin 6) = raw9504 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9504 hH).trans (sound3442 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix12 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix12 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix12 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix12 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix12 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix12 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow12, value2724, value3198, value3199, value3200, value3434, value3442, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal13 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def boundaryMatrix13 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def boundaryRow13 : Integer.Sparse (Fin 909) := [(0, 93), (1, -1715), (2, 210), (3, 2880), (4, 2400), (12, 1520), (21, 720), (22, 720), (31, -480)]

theorem boundarySound13 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow13 (momentVector H) = 0 := by
  have hshape : boundaryMatrix13 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix13 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix13 (0 : Fin 6)) =
      Sparse.eval value3206 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (0 : Fin 6) = raw8333 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8333 hH).trans (sound3206 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix13 (1 : Fin 6)) =
      Sparse.eval value3442 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (1 : Fin 6) = raw9220 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9220 hH).trans (sound3442 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix13 (2 : Fin 6)) =
      Sparse.eval value3393 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (2 : Fin 6) = raw9422 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9422 hH).trans (sound3393 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix13 (3 : Fin 6)) =
      Sparse.eval value3205 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (3 : Fin 6) = raw9464 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9464 hH).trans (sound3205 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix13 (4 : Fin 6)) =
      Sparse.eval value3433 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (4 : Fin 6) = raw9470 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9470 hH).trans (sound3433 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix13 (5 : Fin 6)) =
      Sparse.eval value3442 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (5 : Fin 6) = raw9471 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9471 hH).trans (sound3442 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix13 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix13 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix13 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix13 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix13 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix13 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow13, value3205, value3206, value3393, value3433, value3442, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal14 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def boundaryMatrix14 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def boundaryRow14 : Integer.Sparse (Fin 909) := [(0, 16), (1, -315), (2, 65), (3, 960), (4, 600), (12, 360), (18, 360), (25, -240), (31, -240)]

theorem boundarySound14 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow14 (momentVector H) = 0 := by
  have hshape : boundaryMatrix14 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix14 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix14 (0 : Fin 6)) =
      Sparse.eval value3174 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix14 (0 : Fin 6) = raw8340 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8340 hH).trans (sound3174 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix14 (1 : Fin 6)) =
      Sparse.eval value3437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix14 (1 : Fin 6) = raw9340 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9340 hH).trans (sound3437 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix14 (2 : Fin 6)) =
      Sparse.eval value2759 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix14 (2 : Fin 6) = raw9566 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9566 hH).trans (sound2759 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix14 (3 : Fin 6)) =
      Sparse.eval value3174 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix14 (3 : Fin 6) = raw9572 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9572 hH).trans (sound3174 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix14 (4 : Fin 6)) =
      Sparse.eval value3437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix14 (4 : Fin 6) = raw9575 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9575 hH).trans (sound3437 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix14 (5 : Fin 6)) =
      Sparse.eval value3083 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix14 (5 : Fin 6) = raw9576 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9576 hH).trans (sound3083 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix14 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix14 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix14 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix14 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix14 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix14 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow14, value2759, value3083, value3174, value3437, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal16 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def boundaryMatrix16 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def boundaryRow16 : Integer.Sparse (Fin 909) := [(0, -69), (1, -470), (2, 110), (3, 160), (4, 160), (12, 160), (17, 180), (23, -60), (27, 45), (28, 360), (30, -300)]

theorem boundarySound16 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow16 (momentVector H) = 0 := by
  have hshape : boundaryMatrix16 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix16 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix16 (0 : Fin 6)) =
      Sparse.eval value3169 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix16 (0 : Fin 6) = raw3486 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3486 hH).trans (sound3169 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix16 (1 : Fin 6)) =
      Sparse.eval value3404 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix16 (1 : Fin 6) = raw7273 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7273 hH).trans (sound3404 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix16 (2 : Fin 6)) =
      Sparse.eval value3399 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix16 (2 : Fin 6) = raw7345 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7345 hH).trans (sound3399 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix16 (3 : Fin 6)) =
      Sparse.eval value3399 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix16 (3 : Fin 6) = raw7346 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7346 hH).trans (sound3399 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix16 (4 : Fin 6)) =
      Sparse.eval value3404 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix16 (4 : Fin 6) = raw7347 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7347 hH).trans (sound3404 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix16 (5 : Fin 6)) =
      Sparse.eval value3450 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix16 (5 : Fin 6) = raw7348 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7348 hH).trans (sound3450 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix16 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix16 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix16 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix16 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix16 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix16 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow16, value3169, value3399, value3404, value3450, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
