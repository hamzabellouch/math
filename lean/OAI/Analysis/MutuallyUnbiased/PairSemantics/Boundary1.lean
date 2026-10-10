import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical232
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical246
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical266
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical267
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical268
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical269
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical270
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical271
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical273
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical274
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical277
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical287
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical289
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical290
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical291
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical299
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical300
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical302
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical305
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical306
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical307
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical308
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical309
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical310
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical312
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical313

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal17 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def boundaryMatrix17 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def boundaryRow17 : Integer.Sparse (Fin 909) := [(0, -11), (1, 220), (2, -250), (3, -1200), (4, -240), (5, 260), (6, -15), (7, -480), (8, -480), (12, -480), (13, -320), (35, -160), (51, 720), (52, -240)]

theorem boundarySound17 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow17 (momentVector H) = 0 := by
  have hshape : boundaryMatrix17 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix17 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix17 (0 : Fin 6)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix17 (0 : Fin 6) = raw9691 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9691 hH).trans (sound570 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix17 (1 : Fin 6)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix17 (1 : Fin 6) = raw10001 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10001 hH).trans (sound570 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix17 (2 : Fin 6)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix17 (2 : Fin 6) = raw10009 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10009 hH).trans (sound570 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix17 (3 : Fin 6)) =
      Sparse.eval value1890 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix17 (3 : Fin 6) = raw10016 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10016 hH).trans (sound1890 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix17 (4 : Fin 6)) =
      Sparse.eval value1891 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix17 (4 : Fin 6) = raw10021 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10021 hH).trans (sound1891 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix17 (5 : Fin 6)) =
      Sparse.eval value1542 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix17 (5 : Fin 6) = raw10022 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10022 hH).trans (sound1542 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix17 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix17 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix17 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix17 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix17 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix17 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow17, value1542, value1890, value1891, value570, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal18 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def boundaryMatrix18 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def boundaryRow18 : Integer.Sparse (Fin 909) := [(0, -32), (1, 615), (2, -60), (3, -2160), (4, -960), (5, 60), (6, -15), (12, -240), (13, -160), (26, -960), (35, -240), (55, 720)]

theorem boundarySound18 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow18 (momentVector H) = 0 := by
  have hshape : boundaryMatrix18 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix18 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix18 (0 : Fin 6)) =
      Sparse.eval value2671 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix18 (0 : Fin 6) = raw6802 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6802 hH).trans (sound2671 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix18 (1 : Fin 6)) =
      Sparse.eval value2671 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix18 (1 : Fin 6) = raw8524 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8524 hH).trans (sound2671 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix18 (2 : Fin 6)) =
      Sparse.eval value2671 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix18 (2 : Fin 6) = raw8571 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8571 hH).trans (sound2671 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix18 (3 : Fin 6)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix18 (3 : Fin 6) = raw8587 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8587 hH).trans (sound884 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix18 (4 : Fin 6)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix18 (4 : Fin 6) = raw8599 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8599 hH).trans (sound884 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix18 (5 : Fin 6)) =
      Sparse.eval value1891 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix18 (5 : Fin 6) = raw8601 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8601 hH).trans (sound1891 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix18 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix18 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix18 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix18 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix18 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix18 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow18, value1891, value2671, value884, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal19 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def boundaryMatrix19 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def boundaryRow19 : Integer.Sparse (Fin 909) := [(0, -7), (1, 125), (2, -70), (3, -480), (4, -160), (5, 160), (6, -20), (7, -80), (8, -160), (26, -160), (35, -80), (52, -160)]

theorem boundarySound19 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow19 (momentVector H) = 0 := by
  have hshape : boundaryMatrix19 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix19 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix19 (0 : Fin 6)) =
      Sparse.eval value2128 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix19 (0 : Fin 6) = raw4054 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical4054 hH).trans (sound2128 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix19 (1 : Fin 6)) =
      Sparse.eval value2466 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix19 (1 : Fin 6) = raw7368 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7368 hH).trans (sound2466 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix19 (2 : Fin 6)) =
      Sparse.eval value2466 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix19 (2 : Fin 6) = raw7421 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7421 hH).trans (sound2466 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix19 (3 : Fin 6)) =
      Sparse.eval value2469 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix19 (3 : Fin 6) = raw7428 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7428 hH).trans (sound2469 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix19 (4 : Fin 6)) =
      Sparse.eval value2478 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix19 (4 : Fin 6) = raw7432 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7432 hH).trans (sound2478 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix19 (5 : Fin 6)) =
      Sparse.eval value2801 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix19 (5 : Fin 6) = raw7433 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7433 hH).trans (sound2801 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix19 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix19 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix19 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix19 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix19 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix19 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow19, value2128, value2466, value2469, value2478, value2801, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal20 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def boundaryMatrix20 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def boundaryRow20 : Integer.Sparse (Fin 909) := [(0, -2), (1, 55), (2, -11), (3, -304), (4, -64), (5, 52), (6, -8), (7, -16), (8, -32), (12, -64), (13, -208), (26, -64), (35, -80), (52, -64), (54, 48), (56, 96)]

theorem boundarySound20 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow20 (momentVector H) = 0 := by
  have hshape : boundaryMatrix20 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix20 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix20 (0 : Fin 6)) =
      Sparse.eval value2132 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix20 (0 : Fin 6) = raw4057 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical4057 hH).trans (sound2132 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix20 (1 : Fin 6)) =
      Sparse.eval value2657 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix20 (1 : Fin 6) = raw7370 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7370 hH).trans (sound2657 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix20 (2 : Fin 6)) =
      Sparse.eval value2657 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix20 (2 : Fin 6) = raw7423 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7423 hH).trans (sound2657 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix20 (3 : Fin 6)) =
      Sparse.eval value2797 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix20 (3 : Fin 6) = raw7431 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7431 hH).trans (sound2797 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix20 (4 : Fin 6)) =
      Sparse.eval value1293 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix20 (4 : Fin 6) = raw7435 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7435 hH).trans (sound1293 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix20 (5 : Fin 6)) =
      Sparse.eval value2469 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix20 (5 : Fin 6) = raw7437 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7437 hH).trans (sound2469 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix20 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix20 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix20 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix20 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix20 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix20 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow20, value1293, value2132, value2469, value2657, value2797, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal21 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def boundaryMatrix21 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def boundaryRow21 : Integer.Sparse (Fin 909) := [(0, -11), (1, 215), (2, -95), (3, -720), (4, -240), (5, 160), (6, -15), (7, -240), (8, -240), (26, -240), (35, -80)]

theorem boundarySound21 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow21 (momentVector H) = 0 := by
  have hshape : boundaryMatrix21 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix21 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix21 (0 : Fin 6)) =
      Sparse.eval value2469 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix21 (0 : Fin 6) = raw7894 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7894 hH).trans (sound2469 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix21 (1 : Fin 6)) =
      Sparse.eval value2469 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix21 (1 : Fin 6) = raw9999 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9999 hH).trans (sound2469 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix21 (2 : Fin 6)) =
      Sparse.eval value2469 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix21 (2 : Fin 6) = raw10008 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10008 hH).trans (sound2469 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix21 (3 : Fin 6)) =
      Sparse.eval value2478 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix21 (3 : Fin 6) = raw10015 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10015 hH).trans (sound2478 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix21 (4 : Fin 6)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix21 (4 : Fin 6) = raw10020 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10020 hH).trans (sound884 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix21 (5 : Fin 6)) =
      Sparse.eval value1542 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix21 (5 : Fin 6) = raw10022 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10022 hH).trans (sound1542 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix21 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix21 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix21 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix21 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix21 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix21 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow21, value1542, value2469, value2478, value884, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal22 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def boundaryMatrix22 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def boundaryRow22 : Integer.Sparse (Fin 909) := [(0, 1), (1, 5), (3, -400), (5, 10), (7, -160), (12, -240), (13, -240), (23, 360), (25, 360), (35, -80), (54, 240)]

theorem boundarySound22 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow22 (momentVector H) = 0 := by
  have hshape : boundaryMatrix22 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix22 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix22 (0 : Fin 6)) =
      Sparse.eval value2126 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix22 (0 : Fin 6) = raw8177 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8177 hH).trans (sound2126 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix22 (1 : Fin 6)) =
      Sparse.eval value2126 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix22 (1 : Fin 6) = raw8553 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8553 hH).trans (sound2126 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix22 (2 : Fin 6)) =
      Sparse.eval value655 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix22 (2 : Fin 6) = raw8605 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8605 hH).trans (sound655 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix22 (3 : Fin 6)) =
      Sparse.eval value655 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix22 (3 : Fin 6) = raw8619 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8619 hH).trans (sound655 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix22 (4 : Fin 6)) =
      Sparse.eval value2125 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix22 (4 : Fin 6) = raw8624 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8624 hH).trans (sound2125 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix22 (5 : Fin 6)) =
      Sparse.eval value2304 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix22 (5 : Fin 6) = raw8625 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8625 hH).trans (sound2304 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix22 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix22 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix22 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix22 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix22 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix22 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow22, value2125, value2126, value2304, value655, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal23 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def boundaryMatrix23 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def boundaryRow23 : Integer.Sparse (Fin 909) := [(0, -7), (1, 180), (2, -15), (3, -720), (12, -360), (13, -960), (32, -80)]

theorem boundarySound23 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow23 (momentVector H) = 0 := by
  have hshape : boundaryMatrix23 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix23 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix23 (0 : Fin 6)) =
      Sparse.eval value1410 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix23 (0 : Fin 6) = raw8189 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8189 hH).trans (sound1410 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix23 (1 : Fin 6)) =
      Sparse.eval value1410 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix23 (1 : Fin 6) = raw8566 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8566 hH).trans (sound1410 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix23 (2 : Fin 6)) =
      Sparse.eval value2791 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix23 (2 : Fin 6) = raw8659 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8659 hH).trans (sound2791 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix23 (3 : Fin 6)) =
      Sparse.eval value2791 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix23 (3 : Fin 6) = raw8665 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8665 hH).trans (sound2791 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix23 (4 : Fin 6)) =
      Sparse.eval value2791 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix23 (4 : Fin 6) = raw8672 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8672 hH).trans (sound2791 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix23 (5 : Fin 6)) =
      Sparse.eval value1891 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix23 (5 : Fin 6) = raw8673 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8673 hH).trans (sound1891 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix23 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix23 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix23 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix23 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix23 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix23 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow23, value1410, value1891, value2791, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal24 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def boundaryMatrix24 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def boundaryRow24 : Integer.Sparse (Fin 909) := [(0, -7), (1, 145), (2, -30), (3, -680), (4, -240), (12, -120), (13, -160), (26, -280), (33, 120), (34, -80)]

theorem boundarySound24 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow24 (momentVector H) = 0 := by
  have hshape : boundaryMatrix24 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix24 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix24 (0 : Fin 6)) =
      Sparse.eval value1432 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix24 (0 : Fin 6) = raw8209 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8209 hH).trans (sound1432 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix24 (1 : Fin 6)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix24 (1 : Fin 6) = raw8686 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8686 hH).trans (sound570 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix24 (2 : Fin 6)) =
      Sparse.eval value1430 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix24 (2 : Fin 6) = raw8739 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8739 hH).trans (sound1430 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix24 (3 : Fin 6)) =
      Sparse.eval value2469 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix24 (3 : Fin 6) = raw8750 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8750 hH).trans (sound2469 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix24 (4 : Fin 6)) =
      Sparse.eval value2469 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix24 (4 : Fin 6) = raw8758 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8758 hH).trans (sound2469 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix24 (5 : Fin 6)) =
      Sparse.eval value2469 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix24 (5 : Fin 6) = raw8759 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8759 hH).trans (sound2469 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix24 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix24 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix24 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix24 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix24 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix24 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow24, value1430, value1432, value2469, value570, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal25 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def boundaryMatrix25 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def boundaryRow25 : Integer.Sparse (Fin 909) := [(0, -19), (1, 300), (2, -75), (3, -640), (4, -480), (12, -200), (25, 240), (26, -80), (31, 480), (33, 240)]

theorem boundarySound25 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow25 (momentVector H) = 0 := by
  have hshape : boundaryMatrix25 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix25 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix25 (0 : Fin 6)) =
      Sparse.eval value2099 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix25 (0 : Fin 6) = raw8219 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8219 hH).trans (sound2099 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix25 (1 : Fin 6)) =
      Sparse.eval value2295 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix25 (1 : Fin 6) = raw8782 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8782 hH).trans (sound2295 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix25 (2 : Fin 6)) =
      Sparse.eval value2667 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix25 (2 : Fin 6) = raw8788 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8788 hH).trans (sound2667 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix25 (3 : Fin 6)) =
      Sparse.eval value2667 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix25 (3 : Fin 6) = raw8790 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8790 hH).trans (sound2667 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix25 (4 : Fin 6)) =
      Sparse.eval value2301 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix25 (4 : Fin 6) = raw8792 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8792 hH).trans (sound2301 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix25 (5 : Fin 6)) =
      Sparse.eval value2660 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix25 (5 : Fin 6) = raw8793 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8793 hH).trans (sound2660 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix25 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix25 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix25 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix25 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix25 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix25 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow25, value2099, value2295, value2301, value2660, value2667, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal26 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def boundaryMatrix26 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def boundaryRow26 : Integer.Sparse (Fin 909) := [(0, 157), (1, -2040), (2, 585), (3, 5280), (4, 3520), (12, 2240), (13, 560), (25, -1200), (31, -2880), (33, -960), (50, 720)]

theorem boundarySound26 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow26 (momentVector H) = 0 := by
  have hshape : boundaryMatrix26 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix26 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix26 (0 : Fin 6)) =
      Sparse.eval value3098 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix26 (0 : Fin 6) = raw9158 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9158 hH).trans (sound3098 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix26 (1 : Fin 6)) =
      Sparse.eval value3083 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix26 (1 : Fin 6) = raw9576 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9576 hH).trans (sound3083 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix26 (2 : Fin 6)) =
      Sparse.eval value3083 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix26 (2 : Fin 6) = raw9612 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9612 hH).trans (sound3083 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix26 (3 : Fin 6)) =
      Sparse.eval value3100 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix26 (3 : Fin 6) = raw9622 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9622 hH).trans (sound3100 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix26 (4 : Fin 6)) =
      Sparse.eval value3081 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix26 (4 : Fin 6) = raw9629 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9629 hH).trans (sound3081 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix26 (5 : Fin 6)) =
      Sparse.eval value3446 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix26 (5 : Fin 6) = raw9630 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9630 hH).trans (sound3446 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix26 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix26 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix26 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix26 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix26 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix26 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow26, value3081, value3083, value3098, value3100, value3446, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal27 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def boundaryMatrix27 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def boundaryRow27 : Integer.Sparse (Fin 909) := [(0, 59), (1, -575), (2, 320), (3, 1040), (4, 480), (5, -80), (7, 80), (8, 320), (12, 480), (23, -240), (25, -240), (27, 180), (30, -480), (31, -480), (33, -480), (45, 1440), (51, -480), (54, -240)]

theorem boundarySound27 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow27 (momentVector H) = 0 := by
  have hshape : boundaryMatrix27 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix27 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix27 (0 : Fin 6)) =
      Sparse.eval value2448 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix27 (0 : Fin 6) = raw9711 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9711 hH).trans (sound2448 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix27 (1 : Fin 6)) =
      Sparse.eval value2448 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix27 (1 : Fin 6) = raw9775 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9775 hH).trans (sound2448 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix27 (2 : Fin 6)) =
      Sparse.eval value3046 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix27 (2 : Fin 6) = raw9820 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9820 hH).trans (sound3046 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix27 (3 : Fin 6)) =
      Sparse.eval value3085 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix27 (3 : Fin 6) = raw9839 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9839 hH).trans (sound3085 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix27 (4 : Fin 6)) =
      Sparse.eval value3085 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix27 (4 : Fin 6) = raw9841 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9841 hH).trans (sound3085 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix27 (5 : Fin 6)) =
      Sparse.eval value2888 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix27 (5 : Fin 6) = raw9842 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9842 hH).trans (sound2888 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix27 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix27 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix27 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix27 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix27 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix27 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow27, value2448, value2888, value3046, value3085, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal28 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def boundaryMatrix28 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def boundaryRow28 : Integer.Sparse (Fin 909) := [(0, 29), (1, -334), (2, 99), (3, 896), (4, 512), (12, 352), (13, 32), (25, -96), (26, 112), (31, -336), (33, -192), (43, 144), (45, 288)]

theorem boundarySound28 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow28 (momentVector H) = 0 := by
  have hshape : boundaryMatrix28 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix28 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix28 (0 : Fin 6)) =
      Sparse.eval value2448 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix28 (0 : Fin 6) = raw9726 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9726 hH).trans (sound2448 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix28 (1 : Fin 6)) =
      Sparse.eval value3083 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix28 (1 : Fin 6) = raw9888 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9888 hH).trans (sound3083 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix28 (2 : Fin 6)) =
      Sparse.eval value3083 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix28 (2 : Fin 6) = raw9912 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9912 hH).trans (sound3083 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix28 (3 : Fin 6)) =
      Sparse.eval value3085 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix28 (3 : Fin 6) = raw9918 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9918 hH).trans (sound3085 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix28 (4 : Fin 6)) =
      Sparse.eval value3086 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix28 (4 : Fin 6) = raw9920 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9920 hH).trans (sound3086 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix28 (5 : Fin 6)) =
      Sparse.eval value3440 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix28 (5 : Fin 6) = raw9921 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9921 hH).trans (sound3440 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix28 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix28 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix28 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix28 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix28 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix28 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow28, value2448, value3083, value3085, value3086, value3440, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal29 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def boundaryMatrix29 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def boundaryRow29 : Integer.Sparse (Fin 909) := [(0, 128), (1, -1575), (2, 405), (3, 4480), (4, 2960), (12, 1360), (25, -960), (26, 960), (31, -1680), (43, 720), (44, 720), (45, 720), (46, 720)]

theorem boundarySound29 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow29 (momentVector H) = 0 := by
  have hshape : boundaryMatrix29 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix29 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix29 (0 : Fin 6)) =
      Sparse.eval value2449 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix29 (0 : Fin 6) = raw9722 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9722 hH).trans (sound2449 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix29 (1 : Fin 6)) =
      Sparse.eval value3079 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix29 (1 : Fin 6) = raw9869 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9869 hH).trans (sound3079 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix29 (2 : Fin 6)) =
      Sparse.eval value3081 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix29 (2 : Fin 6) = raw9880 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9880 hH).trans (sound3081 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix29 (3 : Fin 6)) =
      Sparse.eval value3082 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix29 (3 : Fin 6) = raw9883 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9883 hH).trans (sound3082 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix29 (4 : Fin 6)) =
      Sparse.eval value3083 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix29 (4 : Fin 6) = raw9888 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9888 hH).trans (sound3083 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix29 (5 : Fin 6)) =
      Sparse.eval value3441 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix29 (5 : Fin 6) = raw9889 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9889 hH).trans (sound3441 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix29 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix29 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix29 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix29 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix29 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix29 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow29, value2449, value3079, value3081, value3082, value3083, value3441, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal30 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def boundaryMatrix30 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def boundaryRow30 : Integer.Sparse (Fin 909) := [(0, 58), (1, -605), (2, 235), (3, 1280), (4, 920), (5, -30), (7, 40), (8, 80), (12, 560), (23, -240), (24, -720), (25, -600), (27, 300), (30, -480), (31, -1200), (33, -480), (48, 360), (49, 720), (51, -360), (55, -240)]

theorem boundarySound30 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow30 (momentVector H) = 0 := by
  have hshape : boundaryMatrix30 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix30 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix30 (0 : Fin 6)) =
      Sparse.eval value3093 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix30 (0 : Fin 6) = raw8323 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8323 hH).trans (sound3093 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix30 (1 : Fin 6)) =
      Sparse.eval value3093 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix30 (1 : Fin 6) = raw9210 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9210 hH).trans (sound3093 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix30 (2 : Fin 6)) =
      Sparse.eval value3081 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix30 (2 : Fin 6) = raw9259 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9259 hH).trans (sound3081 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix30 (3 : Fin 6)) =
      Sparse.eval value3092 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix30 (3 : Fin 6) = raw9301 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9301 hH).trans (sound3092 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix30 (4 : Fin 6)) =
      Sparse.eval value3043 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix30 (4 : Fin 6) = raw9308 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9308 hH).trans (sound3043 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix30 (5 : Fin 6)) =
      Sparse.eval value3393 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix30 (5 : Fin 6) = raw9310 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9310 hH).trans (sound3393 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix30 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix30 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix30 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix30 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix30 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix30 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow30, value3043, value3081, value3092, value3093, value3393, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal31 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def boundaryMatrix31 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def boundaryRow31 : Integer.Sparse (Fin 909) := [(0, 141), (1, -1765), (2, 580), (3, 3600), (4, 2560), (5, -60), (7, 80), (8, 160), (12, 1440), (13, 320), (23, -480), (24, -1440), (27, 600), (30, -960), (31, -1920), (47, 720), (49, 1440), (51, -720), (55, -480)]

theorem boundarySound31 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow31 (momentVector H) = 0 := by
  have hshape : boundaryMatrix31 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix31 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix31 (0 : Fin 6)) =
      Sparse.eval value3091 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix31 (0 : Fin 6) = raw8327 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8327 hH).trans (sound3091 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix31 (1 : Fin 6)) =
      Sparse.eval value3091 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix31 (1 : Fin 6) = raw9214 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9214 hH).trans (sound3091 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix31 (2 : Fin 6)) =
      Sparse.eval value2448 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix31 (2 : Fin 6) = raw9285 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9285 hH).trans (sound2448 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix31 (3 : Fin 6)) =
      Sparse.eval value3094 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix31 (3 : Fin 6) = raw9333 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9333 hH).trans (sound3094 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix31 (4 : Fin 6)) =
      Sparse.eval value3046 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix31 (4 : Fin 6) = raw9339 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9339 hH).trans (sound3046 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix31 (5 : Fin 6)) =
      Sparse.eval value3437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix31 (5 : Fin 6) = raw9340 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9340 hH).trans (sound3437 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix31 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix31 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix31 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix31 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix31 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix31 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow31, value2448, value3046, value3091, value3094, value3437, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal32 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def boundaryMatrix32 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

def boundaryRow32 : Integer.Sparse (Fin 909) := [(0, 109), (1, -1300), (2, 565), (3, 2880), (4, 1760), (5, -120), (7, 160), (8, 320), (12, 800), (23, -480), (24, -1440), (26, 400), (27, 600), (30, -960), (31, -1200), (43, 720), (55, -480)]

theorem boundarySound32 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow32 (momentVector H) = 0 := by
  have hshape : boundaryMatrix32 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix32 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix32 (0 : Fin 6)) =
      Sparse.eval value3044 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix32 (0 : Fin 6) = raw8865 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8865 hH).trans (sound3044 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix32 (1 : Fin 6)) =
      Sparse.eval value3044 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix32 (1 : Fin 6) = raw9762 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9762 hH).trans (sound3044 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix32 (2 : Fin 6)) =
      Sparse.eval value3458 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix32 (2 : Fin 6) = raw9787 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9787 hH).trans (sound3458 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix32 (3 : Fin 6)) =
      Sparse.eval value3045 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix32 (3 : Fin 6) = raw9818 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9818 hH).trans (sound3045 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix32 (4 : Fin 6)) =
      Sparse.eval value3046 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix32 (4 : Fin 6) = raw9820 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9820 hH).trans (sound3046 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix32 (5 : Fin 6)) =
      Sparse.eval value3457 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix32 (5 : Fin 6) = raw9821 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9821 hH).trans (sound3457 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix32 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix32 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix32 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix32 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix32 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix32 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow32, value3044, value3045, value3046, value3457, value3458, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
