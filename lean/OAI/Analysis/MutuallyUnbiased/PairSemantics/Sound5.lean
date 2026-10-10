import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical153
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation320 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix320 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem sound320 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node320 = Sparse.eval value320 (momentVector H) := by
  have heq : pivotMatrix320 = (fun u v => node320 (pivotPermutation320 u) v) := by apply Matrix.ext; unfold pivotMatrix320 node320 pivotPermutation320; decide +kernel
  have hmoment : injectiveMoment H node320 = injectiveMoment H pivotMatrix320 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix320 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix320 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix320 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix320 (0 : Fin 4) = raw578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix320 raw578; decide +kernel
    rw [heq]
    exact (canonical578 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix320 (1 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix320 (1 : Fin 4) = raw329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix320 raw329; decide +kernel
    rw [heq]
    exact (canonical329 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix320 (2 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix320 (2 : Fin 4) = raw326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix320 raw326; decide +kernel
    rw [heq]
    exact (canonical326 hH).trans (sound173 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix320 (3 : Fin 4)) =
      Sparse.eval value90 (momentVector H) := by
    have heq : mergeFirst pivotMatrix320 (3 : Fin 4) = raw325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix320 raw325; decide +kernel
    rw [heq]
    exact (canonical325 hH).trans (sound90 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node320 + (injectiveMoment H (mergeFirst pivotMatrix320 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix320 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix320 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix320 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value320, value173, value188, value90, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation321 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix321 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem sound321 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node321 = Sparse.eval value321 (momentVector H) := by
  have heq : pivotMatrix321 = (fun u v => node321 (pivotPermutation321 u) v) := by apply Matrix.ext; unfold pivotMatrix321 node321 pivotPermutation321; decide +kernel
  have hmoment : injectiveMoment H node321 = injectiveMoment H pivotMatrix321 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix321 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix321 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix321 (0 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix321 (0 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix321 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix321 (1 : Fin 4)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix321 (1 : Fin 4) = raw331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix321 raw331; decide +kernel
    rw [heq]
    exact (canonical331 hH).trans (sound89 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix321 (2 : Fin 4)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix321 (2 : Fin 4) = raw311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix321 raw311; decide +kernel
    rw [heq]
    exact (canonical311 hH).trans (sound85 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix321 (3 : Fin 4)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix321 (3 : Fin 4) = raw304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix321 raw304; decide +kernel
    rw [heq]
    exact (canonical304 hH).trans (sound84 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node321 + (injectiveMoment H (mergeFirst pivotMatrix321 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix321 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix321 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix321 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value321, value184, value84, value85, value89, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation322 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix322 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem sound322 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node322 = Sparse.eval value322 (momentVector H) := by
  have heq : pivotMatrix322 = (fun u v => node322 (pivotPermutation322 u) v) := by apply Matrix.ext; unfold pivotMatrix322 node322 pivotPermutation322; decide +kernel
  have hmoment : injectiveMoment H node322 = injectiveMoment H pivotMatrix322 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix322 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix322 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix322 (0 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix322 (0 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix322 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix322 (1 : Fin 4)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix322 (1 : Fin 4) = raw330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix322 raw330; decide +kernel
    rw [heq]
    exact (canonical330 hH).trans (sound244 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix322 (2 : Fin 4)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix322 (2 : Fin 4) = raw311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix322 raw311; decide +kernel
    rw [heq]
    exact (canonical311 hH).trans (sound85 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix322 (3 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix322 (3 : Fin 4) = raw307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix322 raw307; decide +kernel
    rw [heq]
    exact (canonical307 hH).trans (sound201 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node322 + (injectiveMoment H (mergeFirst pivotMatrix322 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix322 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix322 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix322 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value322, value153, value201, value244, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation323 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix323 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem sound323 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node323 = Sparse.eval value323 (momentVector H) := by
  have heq : pivotMatrix323 = (fun u v => node323 (pivotPermutation323 u) v) := by apply Matrix.ext; unfold pivotMatrix323 node323 pivotPermutation323; decide +kernel
  have hmoment : injectiveMoment H node323 = injectiveMoment H pivotMatrix323 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix323 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix323 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix323 (0 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix323 (0 : Fin 4) = raw2847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix323 raw2847; decide +kernel
    rw [heq]
    exact (canonical2847 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix323 (1 : Fin 4)) =
      Sparse.eval value80 (momentVector H) := by
    have heq : mergeFirst pivotMatrix323 (1 : Fin 4) = raw334 := by apply Matrix.ext; unfold mergeFirst pivotMatrix323 raw334; decide +kernel
    rw [heq]
    exact (canonical334 hH).trans (sound80 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix323 (2 : Fin 4)) =
      Sparse.eval value88 (momentVector H) := by
    have heq : mergeFirst pivotMatrix323 (2 : Fin 4) = raw319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix323 raw319; decide +kernel
    rw [heq]
    exact (canonical319 hH).trans (sound88 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix323 (3 : Fin 4)) =
      Sparse.eval value86 (momentVector H) := by
    have heq : mergeFirst pivotMatrix323 (3 : Fin 4) = raw314 := by apply Matrix.ext; unfold mergeFirst pivotMatrix323 raw314; decide +kernel
    rw [heq]
    exact (canonical314 hH).trans (sound86 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node323 + (injectiveMoment H (mergeFirst pivotMatrix323 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix323 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix323 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix323 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value323, value187, value80, value86, value88, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation324 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix324 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound324 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node324 = Sparse.eval value324 (momentVector H) := by
  have heq : pivotMatrix324 = (fun u v => node324 (pivotPermutation324 u) v) := by apply Matrix.ext; unfold pivotMatrix324 node324 pivotPermutation324; decide +kernel
  have hmoment : injectiveMoment H node324 = injectiveMoment H pivotMatrix324 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix324 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix324 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix324 (0 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix324 (0 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix324 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix324 (1 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix324 (1 : Fin 4) = raw332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix324 raw332; decide +kernel
    rw [heq]
    exact (canonical332 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix324 (2 : Fin 4)) =
      Sparse.eval value88 (momentVector H) := by
    have heq : mergeFirst pivotMatrix324 (2 : Fin 4) = raw319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix324 raw319; decide +kernel
    rw [heq]
    exact (canonical319 hH).trans (sound88 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix324 (3 : Fin 4)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix324 (3 : Fin 4) = raw317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix324 raw317; decide +kernel
    rw [heq]
    exact (canonical317 hH).trans (sound87 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node324 + (injectiveMoment H (mergeFirst pivotMatrix324 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix324 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix324 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix324 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value324, value155, value173, value87, value88, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation325 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix325 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

theorem sound325 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node325 = Sparse.eval value325 (momentVector H) := by
  have heq : pivotMatrix325 = (fun u v => node325 (pivotPermutation325 u) v) := by apply Matrix.ext; unfold pivotMatrix325 node325 pivotPermutation325; decide +kernel
  have hmoment : injectiveMoment H node325 = injectiveMoment H pivotMatrix325 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix325 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix325 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix325 (0 : Fin 4)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix325 (0 : Fin 4) = raw704 := by apply Matrix.ext; unfold mergeFirst pivotMatrix325 raw704; decide +kernel
    rw [heq]
    exact (canonical704 hH).trans (sound101 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix325 (1 : Fin 4)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix325 (1 : Fin 4) = raw499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix325 raw499; decide +kernel
    rw [heq]
    exact (canonical499 hH).trans (sound214 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix325 (2 : Fin 4)) =
      Sparse.eval value91 (momentVector H) := by
    have heq : mergeFirst pivotMatrix325 (2 : Fin 4) = raw475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix325 raw475; decide +kernel
    rw [heq]
    exact (canonical475 hH).trans (sound91 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix325 (3 : Fin 4)) =
      Sparse.eval value192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix325 (3 : Fin 4) = raw471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix325 raw471; decide +kernel
    rw [heq]
    exact (canonical471 hH).trans (sound192 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node325 + (injectiveMoment H (mergeFirst pivotMatrix325 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix325 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix325 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix325 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value325, value101, value192, value214, value91, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation326 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix326 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

theorem sound326 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node326 = Sparse.eval value326 (momentVector H) := by
  have heq : pivotMatrix326 = (fun u v => node326 (pivotPermutation326 u) v) := by apply Matrix.ext; unfold pivotMatrix326 node326 pivotPermutation326; decide +kernel
  have hmoment : injectiveMoment H node326 = injectiveMoment H pivotMatrix326 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix326 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix326 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix326 (0 : Fin 4)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix326 (0 : Fin 4) = raw708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix326 raw708; decide +kernel
    rw [heq]
    exact (canonical708 hH).trans (sound102 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix326 (1 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix326 (1 : Fin 4) = raw505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix326 raw505; decide +kernel
    rw [heq]
    exact (canonical505 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix326 (2 : Fin 4)) =
      Sparse.eval value141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix326 (2 : Fin 4) = raw480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix326 raw480; decide +kernel
    rw [heq]
    exact (canonical480 hH).trans (sound141 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix326 (3 : Fin 4)) =
      Sparse.eval value75 (momentVector H) := by
    have heq : mergeFirst pivotMatrix326 (3 : Fin 4) = raw478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix326 raw478; decide +kernel
    rw [heq]
    exact (canonical478 hH).trans (sound75 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node326 + (injectiveMoment H (mergeFirst pivotMatrix326 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix326 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix326 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix326 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value326, value102, value141, value155, value75, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation327 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix327 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem sound327 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node327 = Sparse.eval value327 (momentVector H) := by
  have heq : pivotMatrix327 = (fun u v => node327 (pivotPermutation327 u) v) := by apply Matrix.ext; unfold pivotMatrix327 node327 pivotPermutation327; decide +kernel
  have hmoment : injectiveMoment H node327 = injectiveMoment H pivotMatrix327 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix327 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix327 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix327 (0 : Fin 4)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix327 (0 : Fin 4) = raw714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix327 raw714; decide +kernel
    rw [heq]
    exact (canonical714 hH).trans (sound103 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix327 (1 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix327 (1 : Fin 4) = raw506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix327 raw506; decide +kernel
    rw [heq]
    exact (canonical506 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix327 (2 : Fin 4)) =
      Sparse.eval value86 (momentVector H) := by
    have heq : mergeFirst pivotMatrix327 (2 : Fin 4) = raw485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix327 raw485; decide +kernel
    rw [heq]
    exact (canonical485 hH).trans (sound86 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix327 (3 : Fin 4)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix327 (3 : Fin 4) = raw484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix327 raw484; decide +kernel
    rw [heq]
    exact (canonical484 hH).trans (sound163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node327 + (injectiveMoment H (mergeFirst pivotMatrix327 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix327 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix327 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix327 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value327, value103, value163, value187, value86, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation328 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix328 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem sound328 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node328 = Sparse.eval value328 (momentVector H) := by
  have heq : pivotMatrix328 = (fun u v => node328 (pivotPermutation328 u) v) := by apply Matrix.ext; unfold pivotMatrix328 node328 pivotPermutation328; decide +kernel
  have hmoment : injectiveMoment H node328 = injectiveMoment H pivotMatrix328 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix328 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix328 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix328 (0 : Fin 4)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix328 (0 : Fin 4) = raw2718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix328 raw2718; decide +kernel
    rw [heq]
    exact (canonical2718 hH).trans (sound162 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix328 (1 : Fin 4)) =
      Sparse.eval value96 (momentVector H) := by
    have heq : mergeFirst pivotMatrix328 (1 : Fin 4) = raw567 := by apply Matrix.ext; unfold mergeFirst pivotMatrix328 raw567; decide +kernel
    rw [heq]
    exact (canonical567 hH).trans (sound96 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix328 (2 : Fin 4)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix328 (2 : Fin 4) = raw482 := by apply Matrix.ext; unfold mergeFirst pivotMatrix328 raw482; decide +kernel
    rw [heq]
    exact (canonical482 hH).trans (sound196 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix328 (3 : Fin 4)) =
      Sparse.eval value192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix328 (3 : Fin 4) = raw471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix328 raw471; decide +kernel
    rw [heq]
    exact (canonical471 hH).trans (sound192 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node328 + (injectiveMoment H (mergeFirst pivotMatrix328 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix328 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix328 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix328 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value328, value162, value192, value196, value96, Sparse.eval] at hc ⊢
  linarith

theorem sound329 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node329 = Sparse.eval value329 (momentVector H) := by
  have hc : momentVector H 263 = injectiveMoment H node329 := rfl
  simp [value329, Sparse.eval, hc]

def pivotPermutation330 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix330 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem sound330 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node330 = Sparse.eval value330 (momentVector H) := by
  have heq : pivotMatrix330 = (fun u v => node330 (pivotPermutation330 u) v) := by apply Matrix.ext; unfold pivotMatrix330 node330 pivotPermutation330; decide +kernel
  have hmoment : injectiveMoment H node330 = injectiveMoment H pivotMatrix330 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix330 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix330 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix330 (0 : Fin 4)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix330 (0 : Fin 4) = raw2721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix330 raw2721; decide +kernel
    rw [heq]
    exact (canonical2721 hH).trans (sound163 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix330 (1 : Fin 4)) =
      Sparse.eval value91 (momentVector H) := by
    have heq : mergeFirst pivotMatrix330 (1 : Fin 4) = raw569 := by apply Matrix.ext; unfold mergeFirst pivotMatrix330 raw569; decide +kernel
    rw [heq]
    exact (canonical569 hH).trans (sound91 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix330 (2 : Fin 4)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix330 (2 : Fin 4) = raw484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix330 raw484; decide +kernel
    rw [heq]
    exact (canonical484 hH).trans (sound163 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix330 (3 : Fin 4)) =
      Sparse.eval value91 (momentVector H) := by
    have heq : mergeFirst pivotMatrix330 (3 : Fin 4) = raw475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix330 raw475; decide +kernel
    rw [heq]
    exact (canonical475 hH).trans (sound91 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node330 + (injectiveMoment H (mergeFirst pivotMatrix330 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix330 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix330 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix330 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value330, value163, value91, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation331 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix331 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem sound331 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node331 = Sparse.eval value331 (momentVector H) := by
  have heq : pivotMatrix331 = (fun u v => node331 (pivotPermutation331 u) v) := by apply Matrix.ext; unfold pivotMatrix331 node331 pivotPermutation331; decide +kernel
  have hmoment : injectiveMoment H node331 = injectiveMoment H pivotMatrix331 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix331 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix331 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix331 (0 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix331 (0 : Fin 4) = raw4037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix331 raw4037; decide +kernel
    rw [heq]
    exact (canonical4037 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix331 (1 : Fin 4)) =
      Sparse.eval value98 (momentVector H) := by
    have heq : mergeFirst pivotMatrix331 (1 : Fin 4) = raw573 := by apply Matrix.ext; unfold mergeFirst pivotMatrix331 raw573; decide +kernel
    rw [heq]
    exact (canonical573 hH).trans (sound98 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix331 (2 : Fin 4)) =
      Sparse.eval value86 (momentVector H) := by
    have heq : mergeFirst pivotMatrix331 (2 : Fin 4) = raw485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix331 raw485; decide +kernel
    rw [heq]
    exact (canonical485 hH).trans (sound86 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix331 (3 : Fin 4)) =
      Sparse.eval value91 (momentVector H) := by
    have heq : mergeFirst pivotMatrix331 (3 : Fin 4) = raw475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix331 raw475; decide +kernel
    rw [heq]
    exact (canonical475 hH).trans (sound91 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node331 + (injectiveMoment H (mergeFirst pivotMatrix331 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix331 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix331 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix331 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value331, value198, value86, value91, value98, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation332 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix332 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem sound332 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node332 = Sparse.eval value332 (momentVector H) := by
  have heq : pivotMatrix332 = (fun u v => node332 (pivotPermutation332 u) v) := by apply Matrix.ext; unfold pivotMatrix332 node332 pivotPermutation332; decide +kernel
  have hmoment : injectiveMoment H node332 = injectiveMoment H pivotMatrix332 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix332 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix332 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix332 (0 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix332 (0 : Fin 4) = raw2726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix332 raw2726; decide +kernel
    rw [heq]
    exact (canonical2726 hH).trans (sound167 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix332 (1 : Fin 4)) =
      Sparse.eval value100 (momentVector H) := by
    have heq : mergeFirst pivotMatrix332 (1 : Fin 4) = raw571 := by apply Matrix.ext; unfold mergeFirst pivotMatrix332 raw571; decide +kernel
    rw [heq]
    exact (canonical571 hH).trans (sound100 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix332 (2 : Fin 4)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix332 (2 : Fin 4) = raw486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix332 raw486; decide +kernel
    rw [heq]
    exact (canonical486 hH).trans (sound163 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix332 (3 : Fin 4)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix332 (3 : Fin 4) = raw482 := by apply Matrix.ext; unfold mergeFirst pivotMatrix332 raw482; decide +kernel
    rw [heq]
    exact (canonical482 hH).trans (sound196 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node332 + (injectiveMoment H (mergeFirst pivotMatrix332 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix332 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix332 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix332 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value332, value100, value163, value167, value196, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation333 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix333 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

theorem sound333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node333 = Sparse.eval value333 (momentVector H) := by
  have heq : pivotMatrix333 = (fun u v => node333 (pivotPermutation333 u) v) := by apply Matrix.ext; unfold pivotMatrix333 node333 pivotPermutation333; decide +kernel
  have hmoment : injectiveMoment H node333 = injectiveMoment H pivotMatrix333 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix333 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix333 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix333 (0 : Fin 4)) =
      Sparse.eval value79 (momentVector H) := by
    have heq : mergeFirst pivotMatrix333 (0 : Fin 4) = raw274 := by apply Matrix.ext; unfold mergeFirst pivotMatrix333 raw274; decide +kernel
    rw [heq]
    exact (canonical274 hH).trans (sound79 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix333 (1 : Fin 4)) =
      Sparse.eval value91 (momentVector H) := by
    have heq : mergeFirst pivotMatrix333 (1 : Fin 4) = raw475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix333 raw475; decide +kernel
    rw [heq]
    exact (canonical475 hH).trans (sound91 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix333 (2 : Fin 4)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix333 (2 : Fin 4) = raw499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix333 raw499; decide +kernel
    rw [heq]
    exact (canonical499 hH).trans (sound214 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix333 (3 : Fin 4)) =
      Sparse.eval value92 (momentVector H) := by
    have heq : mergeFirst pivotMatrix333 (3 : Fin 4) = raw502 := by apply Matrix.ext; unfold mergeFirst pivotMatrix333 raw502; decide +kernel
    rw [heq]
    exact (canonical502 hH).trans (sound92 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node333 + (injectiveMoment H (mergeFirst pivotMatrix333 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix333 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix333 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix333 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value333, value214, value79, value91, value92, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation334 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix334 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

theorem sound334 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node334 = Sparse.eval value334 (momentVector H) := by
  have heq : pivotMatrix334 = (fun u v => node334 (pivotPermutation334 u) v) := by apply Matrix.ext; unfold pivotMatrix334 node334 pivotPermutation334; decide +kernel
  have hmoment : injectiveMoment H node334 = injectiveMoment H pivotMatrix334 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix334 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix334 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix334 (0 : Fin 4)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix334 (0 : Fin 4) = raw289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix334 raw289; decide +kernel
    rw [heq]
    exact (canonical289 hH).trans (sound81 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix334 (1 : Fin 4)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix334 (1 : Fin 4) = raw508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix334 raw508; decide +kernel
    rw [heq]
    exact (canonical508 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix334 (2 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix334 (2 : Fin 4) = raw522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix334 raw522; decide +kernel
    rw [heq]
    exact (canonical522 hH).trans (sound188 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix334 (3 : Fin 4)) =
      Sparse.eval value93 (momentVector H) := by
    have heq : mergeFirst pivotMatrix334 (3 : Fin 4) = raw527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix334 raw527; decide +kernel
    rw [heq]
    exact (canonical527 hH).trans (sound93 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node334 + (injectiveMoment H (mergeFirst pivotMatrix334 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix334 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix334 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix334 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value334, value188, value37, value81, value93, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation335 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix335 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]

theorem sound335 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node335 = Sparse.eval value335 (momentVector H) := by
  have heq : pivotMatrix335 = (fun u v => node335 (pivotPermutation335 u) v) := by apply Matrix.ext; unfold pivotMatrix335 node335 pivotPermutation335; decide +kernel
  have hmoment : injectiveMoment H node335 = injectiveMoment H pivotMatrix335 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix335 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix335 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix335 (0 : Fin 4)) =
      Sparse.eval value82 (momentVector H) := by
    have heq : mergeFirst pivotMatrix335 (0 : Fin 4) = raw292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix335 raw292; decide +kernel
    rw [heq]
    exact (canonical292 hH).trans (sound82 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix335 (1 : Fin 4)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix335 (1 : Fin 4) = raw510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix335 raw510; decide +kernel
    rw [heq]
    exact (canonical510 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix335 (2 : Fin 4)) =
      Sparse.eval value94 (momentVector H) := by
    have heq : mergeFirst pivotMatrix335 (2 : Fin 4) = raw529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix335 raw529; decide +kernel
    rw [heq]
    exact (canonical529 hH).trans (sound94 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix335 (3 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix335 (3 : Fin 4) = raw532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix335 raw532; decide +kernel
    rw [heq]
    exact (canonical532 hH).trans (sound222 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node335 + (injectiveMoment H (mergeFirst pivotMatrix335 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix335 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix335 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix335 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value335, value222, value32, value82, value94, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation336 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix336 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

theorem sound336 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node336 = Sparse.eval value336 (momentVector H) := by
  have heq : pivotMatrix336 = (fun u v => node336 (pivotPermutation336 u) v) := by apply Matrix.ext; unfold pivotMatrix336 node336 pivotPermutation336; decide +kernel
  have hmoment : injectiveMoment H node336 = injectiveMoment H pivotMatrix336 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix336 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix336 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix336 (0 : Fin 4)) =
      Sparse.eval value83 (momentVector H) := by
    have heq : mergeFirst pivotMatrix336 (0 : Fin 4) = raw298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix336 raw298; decide +kernel
    rw [heq]
    exact (canonical298 hH).trans (sound83 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix336 (1 : Fin 4)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix336 (1 : Fin 4) = raw512 := by apply Matrix.ext; unfold mergeFirst pivotMatrix336 raw512; decide +kernel
    rw [heq]
    exact (canonical512 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix336 (2 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix336 (2 : Fin 4) = raw538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix336 raw538; decide +kernel
    rw [heq]
    exact (canonical538 hH).trans (sound215 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix336 (3 : Fin 4)) =
      Sparse.eval value95 (momentVector H) := by
    have heq : mergeFirst pivotMatrix336 (3 : Fin 4) = raw539 := by apply Matrix.ext; unfold mergeFirst pivotMatrix336 raw539; decide +kernel
    rw [heq]
    exact (canonical539 hH).trans (sound95 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node336 + (injectiveMoment H (mergeFirst pivotMatrix336 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix336 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix336 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix336 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value336, value215, value37, value83, value95, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation337 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix337 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem sound337 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node337 = Sparse.eval value337 (momentVector H) := by
  have heq : pivotMatrix337 = (fun u v => node337 (pivotPermutation337 u) v) := by apply Matrix.ext; unfold pivotMatrix337 node337 pivotPermutation337; decide +kernel
  have hmoment : injectiveMoment H node337 = injectiveMoment H pivotMatrix337 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix337 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix337 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix337 (0 : Fin 4)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix337 (0 : Fin 4) = raw304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix337 raw304; decide +kernel
    rw [heq]
    exact (canonical304 hH).trans (sound84 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix337 (1 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix337 (1 : Fin 4) = raw532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix337 raw532; decide +kernel
    rw [heq]
    exact (canonical532 hH).trans (sound222 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix337 (2 : Fin 4)) =
      Sparse.eval value96 (momentVector H) := by
    have heq : mergeFirst pivotMatrix337 (2 : Fin 4) = raw547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix337 raw547; decide +kernel
    rw [heq]
    exact (canonical547 hH).trans (sound96 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix337 (3 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix337 (3 : Fin 4) = raw550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix337 raw550; decide +kernel
    rw [heq]
    exact (canonical550 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node337 + (injectiveMoment H (mergeFirst pivotMatrix337 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix337 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix337 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix337 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value337, value198, value222, value84, value96, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation338 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix338 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem sound338 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node338 = Sparse.eval value338 (momentVector H) := by
  have heq : pivotMatrix338 = (fun u v => node338 (pivotPermutation338 u) v) := by apply Matrix.ext; unfold pivotMatrix338 node338 pivotPermutation338; decide +kernel
  have hmoment : injectiveMoment H node338 = injectiveMoment H pivotMatrix338 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix338 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix338 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix338 (0 : Fin 4)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix338 (0 : Fin 4) = raw310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix338 raw310; decide +kernel
    rw [heq]
    exact (canonical310 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix338 (1 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix338 (1 : Fin 4) = raw538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix338 raw538; decide +kernel
    rw [heq]
    exact (canonical538 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix338 (2 : Fin 4)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix338 (2 : Fin 4) = raw553 := by apply Matrix.ext; unfold mergeFirst pivotMatrix338 raw553; decide +kernel
    rw [heq]
    exact (canonical553 hH).trans (sound204 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix338 (3 : Fin 4)) =
      Sparse.eval value97 (momentVector H) := by
    have heq : mergeFirst pivotMatrix338 (3 : Fin 4) = raw554 := by apply Matrix.ext; unfold mergeFirst pivotMatrix338 raw554; decide +kernel
    rw [heq]
    exact (canonical554 hH).trans (sound97 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node338 + (injectiveMoment H (mergeFirst pivotMatrix338 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix338 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix338 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix338 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value338, value204, value215, value85, value97, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation339 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix339 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem sound339 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node339 = Sparse.eval value339 (momentVector H) := by
  have heq : pivotMatrix339 = (fun u v => node339 (pivotPermutation339 u) v) := by apply Matrix.ext; unfold pivotMatrix339 node339 pivotPermutation339; decide +kernel
  have hmoment : injectiveMoment H node339 = injectiveMoment H pivotMatrix339 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix339 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix339 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix339 (0 : Fin 4)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix339 (0 : Fin 4) = raw317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix339 raw317; decide +kernel
    rw [heq]
    exact (canonical317 hH).trans (sound87 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix339 (1 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix339 (1 : Fin 4) = raw552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix339 raw552; decide +kernel
    rw [heq]
    exact (canonical552 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix339 (2 : Fin 4)) =
      Sparse.eval value98 (momentVector H) := by
    have heq : mergeFirst pivotMatrix339 (2 : Fin 4) = raw560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix339 raw560; decide +kernel
    rw [heq]
    exact (canonical560 hH).trans (sound98 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix339 (3 : Fin 4)) =
      Sparse.eval value93 (momentVector H) := by
    have heq : mergeFirst pivotMatrix339 (3 : Fin 4) = raw563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix339 raw563; decide +kernel
    rw [heq]
    exact (canonical563 hH).trans (sound93 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node339 + (injectiveMoment H (mergeFirst pivotMatrix339 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix339 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix339 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix339 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value339, value215, value87, value93, value98, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation340 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix340 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

theorem sound340 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node340 = Sparse.eval value340 (momentVector H) := by
  have heq : pivotMatrix340 = (fun u v => node340 (pivotPermutation340 u) v) := by apply Matrix.ext; unfold pivotMatrix340 node340 pivotPermutation340; decide +kernel
  have hmoment : injectiveMoment H node340 = injectiveMoment H pivotMatrix340 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix340 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix340 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix340 (0 : Fin 4)) =
      Sparse.eval value88 (momentVector H) := by
    have heq : mergeFirst pivotMatrix340 (0 : Fin 4) = raw318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix340 raw318; decide +kernel
    rw [heq]
    exact (canonical318 hH).trans (sound88 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix340 (1 : Fin 4)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix340 (1 : Fin 4) = raw553 := by apply Matrix.ext; unfold mergeFirst pivotMatrix340 raw553; decide +kernel
    rw [heq]
    exact (canonical553 hH).trans (sound204 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix340 (2 : Fin 4)) =
      Sparse.eval value93 (momentVector H) := by
    have heq : mergeFirst pivotMatrix340 (2 : Fin 4) = raw563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix340 raw563; decide +kernel
    rw [heq]
    exact (canonical563 hH).trans (sound93 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix340 (3 : Fin 4)) =
      Sparse.eval value92 (momentVector H) := by
    have heq : mergeFirst pivotMatrix340 (3 : Fin 4) = raw564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix340 raw564; decide +kernel
    rw [heq]
    exact (canonical564 hH).trans (sound92 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node340 + (injectiveMoment H (mergeFirst pivotMatrix340 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix340 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix340 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix340 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value340, value204, value88, value92, value93, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation341 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix341 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]

theorem sound341 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node341 = Sparse.eval value341 (momentVector H) := by
  have heq : pivotMatrix341 = (fun u v => node341 (pivotPermutation341 u) v) := by apply Matrix.ext; unfold pivotMatrix341 node341 pivotPermutation341; decide +kernel
  have hmoment : injectiveMoment H node341 = injectiveMoment H pivotMatrix341 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix341 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix341 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix341 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix341 (0 : Fin 4) = raw771 := by apply Matrix.ext; unfold mergeFirst pivotMatrix341 raw771; decide +kernel
    rw [heq]
    exact (canonical771 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix341 (1 : Fin 4)) =
      Sparse.eval value93 (momentVector H) := by
    have heq : mergeFirst pivotMatrix341 (1 : Fin 4) = raw544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix341 raw544; decide +kernel
    rw [heq]
    exact (canonical544 hH).trans (sound93 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix341 (2 : Fin 4)) =
      Sparse.eval value93 (momentVector H) := by
    have heq : mergeFirst pivotMatrix341 (2 : Fin 4) = raw527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix341 raw527; decide +kernel
    rw [heq]
    exact (canonical527 hH).trans (sound93 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix341 (3 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix341 (3 : Fin 4) = raw522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix341 raw522; decide +kernel
    rw [heq]
    exact (canonical522 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node341 + (injectiveMoment H (mergeFirst pivotMatrix341 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix341 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix341 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix341 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value341, value188, value93, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation342 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix342 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

theorem sound342 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node342 = Sparse.eval value342 (momentVector H) := by
  have heq : pivotMatrix342 = (fun u v => node342 (pivotPermutation342 u) v) := by apply Matrix.ext; unfold pivotMatrix342 node342 pivotPermutation342; decide +kernel
  have hmoment : injectiveMoment H node342 = injectiveMoment H pivotMatrix342 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix342 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix342 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix342 (0 : Fin 4)) =
      Sparse.eval value108 (momentVector H) := by
    have heq : mergeFirst pivotMatrix342 (0 : Fin 4) = raw775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix342 raw775; decide +kernel
    rw [heq]
    exact (canonical775 hH).trans (sound108 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix342 (1 : Fin 4)) =
      Sparse.eval value96 (momentVector H) := by
    have heq : mergeFirst pivotMatrix342 (1 : Fin 4) = raw547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix342 raw547; decide +kernel
    rw [heq]
    exact (canonical547 hH).trans (sound96 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix342 (2 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix342 (2 : Fin 4) = raw532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix342 raw532; decide +kernel
    rw [heq]
    exact (canonical532 hH).trans (sound222 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix342 (3 : Fin 4)) =
      Sparse.eval value94 (momentVector H) := by
    have heq : mergeFirst pivotMatrix342 (3 : Fin 4) = raw529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix342 raw529; decide +kernel
    rw [heq]
    exact (canonical529 hH).trans (sound94 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node342 + (injectiveMoment H (mergeFirst pivotMatrix342 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix342 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix342 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix342 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value342, value108, value222, value94, value96, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation343 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix343 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem sound343 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node343 = Sparse.eval value343 (momentVector H) := by
  have heq : pivotMatrix343 = (fun u v => node343 (pivotPermutation343 u) v) := by apply Matrix.ext; unfold pivotMatrix343 node343 pivotPermutation343; decide +kernel
  have hmoment : injectiveMoment H node343 = injectiveMoment H pivotMatrix343 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix343 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix343 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix343 (0 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix343 (0 : Fin 4) = raw783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix343 raw783; decide +kernel
    rw [heq]
    exact (canonical783 hH).trans (sound109 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix343 (1 : Fin 4)) =
      Sparse.eval value97 (momentVector H) := by
    have heq : mergeFirst pivotMatrix343 (1 : Fin 4) = raw554 := by apply Matrix.ext; unfold mergeFirst pivotMatrix343 raw554; decide +kernel
    rw [heq]
    exact (canonical554 hH).trans (sound97 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix343 (2 : Fin 4)) =
      Sparse.eval value95 (momentVector H) := by
    have heq : mergeFirst pivotMatrix343 (2 : Fin 4) = raw539 := by apply Matrix.ext; unfold mergeFirst pivotMatrix343 raw539; decide +kernel
    rw [heq]
    exact (canonical539 hH).trans (sound95 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix343 (3 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix343 (3 : Fin 4) = raw538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix343 raw538; decide +kernel
    rw [heq]
    exact (canonical538 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node343 + (injectiveMoment H (mergeFirst pivotMatrix343 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix343 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix343 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix343 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value343, value109, value215, value95, value97, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation344 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix344 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

theorem sound344 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node344 = Sparse.eval value344 (momentVector H) := by
  have heq : pivotMatrix344 = (fun u v => node344 (pivotPermutation344 u) v) := by apply Matrix.ext; unfold pivotMatrix344 node344 pivotPermutation344; decide +kernel
  have hmoment : injectiveMoment H node344 = injectiveMoment H pivotMatrix344 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix344 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix344 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix344 (0 : Fin 4)) =
      Sparse.eval value110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix344 (0 : Fin 4) = raw786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix344 raw786; decide +kernel
    rw [heq]
    exact (canonical786 hH).trans (sound110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix344 (1 : Fin 4)) =
      Sparse.eval value91 (momentVector H) := by
    have heq : mergeFirst pivotMatrix344 (1 : Fin 4) = raw558 := by apply Matrix.ext; unfold mergeFirst pivotMatrix344 raw558; decide +kernel
    rw [heq]
    exact (canonical558 hH).trans (sound91 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix344 (2 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix344 (2 : Fin 4) = raw550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix344 raw550; decide +kernel
    rw [heq]
    exact (canonical550 hH).trans (sound198 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix344 (3 : Fin 4)) =
      Sparse.eval value96 (momentVector H) := by
    have heq : mergeFirst pivotMatrix344 (3 : Fin 4) = raw547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix344 raw547; decide +kernel
    rw [heq]
    exact (canonical547 hH).trans (sound96 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node344 + (injectiveMoment H (mergeFirst pivotMatrix344 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix344 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix344 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix344 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value344, value110, value198, value91, value96, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation345 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix345 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem sound345 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node345 = Sparse.eval value345 (momentVector H) := by
  have heq : pivotMatrix345 = (fun u v => node345 (pivotPermutation345 u) v) := by apply Matrix.ext; unfold pivotMatrix345 node345 pivotPermutation345; decide +kernel
  have hmoment : injectiveMoment H node345 = injectiveMoment H pivotMatrix345 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix345 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix345 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix345 (0 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix345 (0 : Fin 4) = raw789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix345 raw789; decide +kernel
    rw [heq]
    exact (canonical789 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix345 (1 : Fin 4)) =
      Sparse.eval value98 (momentVector H) := by
    have heq : mergeFirst pivotMatrix345 (1 : Fin 4) = raw560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix345 raw560; decide +kernel
    rw [heq]
    exact (canonical560 hH).trans (sound98 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix345 (2 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix345 (2 : Fin 4) = raw552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix345 raw552; decide +kernel
    rw [heq]
    exact (canonical552 hH).trans (sound215 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix345 (3 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix345 (3 : Fin 4) = raw550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix345 raw550; decide +kernel
    rw [heq]
    exact (canonical550 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node345 + (injectiveMoment H (mergeFirst pivotMatrix345 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix345 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix345 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix345 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value345, value111, value198, value215, value98, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation346 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix346 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

theorem sound346 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node346 = Sparse.eval value346 (momentVector H) := by
  have heq : pivotMatrix346 = (fun u v => node346 (pivotPermutation346 u) v) := by apply Matrix.ext; unfold pivotMatrix346 node346 pivotPermutation346; decide +kernel
  have hmoment : injectiveMoment H node346 = injectiveMoment H pivotMatrix346 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix346 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix346 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix346 (0 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix346 (0 : Fin 4) = raw792 := by apply Matrix.ext; unfold mergeFirst pivotMatrix346 raw792; decide +kernel
    rw [heq]
    exact (canonical792 hH).trans (sound177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix346 (1 : Fin 4)) =
      Sparse.eval value93 (momentVector H) := by
    have heq : mergeFirst pivotMatrix346 (1 : Fin 4) = raw563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix346 raw563; decide +kernel
    rw [heq]
    exact (canonical563 hH).trans (sound93 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix346 (2 : Fin 4)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix346 (2 : Fin 4) = raw553 := by apply Matrix.ext; unfold mergeFirst pivotMatrix346 raw553; decide +kernel
    rw [heq]
    exact (canonical553 hH).trans (sound204 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix346 (3 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix346 (3 : Fin 4) = raw552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix346 raw552; decide +kernel
    rw [heq]
    exact (canonical552 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node346 + (injectiveMoment H (mergeFirst pivotMatrix346 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix346 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix346 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix346 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value346, value177, value204, value215, value93, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation347 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix347 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

theorem sound347 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node347 = Sparse.eval value347 (momentVector H) := by
  have heq : pivotMatrix347 = (fun u v => node347 (pivotPermutation347 u) v) := by apply Matrix.ext; unfold pivotMatrix347 node347 pivotPermutation347; decide +kernel
  have hmoment : injectiveMoment H node347 = injectiveMoment H pivotMatrix347 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix347 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix347 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix347 (0 : Fin 4)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix347 (0 : Fin 4) = raw793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix347 raw793; decide +kernel
    rw [heq]
    exact (canonical793 hH).trans (sound107 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix347 (1 : Fin 4)) =
      Sparse.eval value92 (momentVector H) := by
    have heq : mergeFirst pivotMatrix347 (1 : Fin 4) = raw564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix347 raw564; decide +kernel
    rw [heq]
    exact (canonical564 hH).trans (sound92 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix347 (2 : Fin 4)) =
      Sparse.eval value97 (momentVector H) := by
    have heq : mergeFirst pivotMatrix347 (2 : Fin 4) = raw554 := by apply Matrix.ext; unfold mergeFirst pivotMatrix347 raw554; decide +kernel
    rw [heq]
    exact (canonical554 hH).trans (sound97 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix347 (3 : Fin 4)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix347 (3 : Fin 4) = raw553 := by apply Matrix.ext; unfold mergeFirst pivotMatrix347 raw553; decide +kernel
    rw [heq]
    exact (canonical553 hH).trans (sound204 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node347 + (injectiveMoment H (mergeFirst pivotMatrix347 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix347 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix347 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix347 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value347, value107, value204, value92, value97, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation348 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix348 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

theorem sound348 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node348 = Sparse.eval value348 (momentVector H) := by
  have heq : pivotMatrix348 = (fun u v => node348 (pivotPermutation348 u) v) := by apply Matrix.ext; unfold pivotMatrix348 node348 pivotPermutation348; decide +kernel
  have hmoment : injectiveMoment H node348 = injectiveMoment H pivotMatrix348 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix348 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix348 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix348 (0 : Fin 4)) =
      Sparse.eval value108 (momentVector H) := by
    have heq : mergeFirst pivotMatrix348 (0 : Fin 4) = raw799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix348 raw799; decide +kernel
    rw [heq]
    exact (canonical799 hH).trans (sound108 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix348 (1 : Fin 4)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix348 (1 : Fin 4) = raw575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix348 raw575; decide +kernel
    rw [heq]
    exact (canonical575 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix348 (2 : Fin 4)) =
      Sparse.eval value100 (momentVector H) := by
    have heq : mergeFirst pivotMatrix348 (2 : Fin 4) = raw571 := by apply Matrix.ext; unfold mergeFirst pivotMatrix348 raw571; decide +kernel
    rw [heq]
    exact (canonical571 hH).trans (sound100 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix348 (3 : Fin 4)) =
      Sparse.eval value79 (momentVector H) := by
    have heq : mergeFirst pivotMatrix348 (3 : Fin 4) = raw570 := by apply Matrix.ext; unfold mergeFirst pivotMatrix348 raw570; decide +kernel
    rw [heq]
    exact (canonical570 hH).trans (sound79 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node348 + (injectiveMoment H (mergeFirst pivotMatrix348 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix348 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix348 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix348 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value348, value100, value108, value170, value79, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation349 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix349 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

theorem sound349 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node349 = Sparse.eval value349 (momentVector H) := by
  have heq : pivotMatrix349 = (fun u v => node349 (pivotPermutation349 u) v) := by apply Matrix.ext; unfold pivotMatrix349 node349 pivotPermutation349; decide +kernel
  have hmoment : injectiveMoment H node349 = injectiveMoment H pivotMatrix349 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix349 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix349 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix349 (0 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix349 (0 : Fin 4) = raw804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix349 raw804; decide +kernel
    rw [heq]
    exact (canonical804 hH).trans (sound109 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix349 (1 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix349 (1 : Fin 4) = raw578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix349 raw578; decide +kernel
    rw [heq]
    exact (canonical578 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix349 (2 : Fin 4)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix349 (2 : Fin 4) = raw575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix349 raw575; decide +kernel
    rw [heq]
    exact (canonical575 hH).trans (sound170 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix349 (3 : Fin 4)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix349 (3 : Fin 4) = raw574 := by apply Matrix.ext; unfold mergeFirst pivotMatrix349 raw574; decide +kernel
    rw [heq]
    exact (canonical574 hH).trans (sound87 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node349 + (injectiveMoment H (mergeFirst pivotMatrix349 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix349 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix349 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix349 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value349, value109, value170, value188, value87, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation350 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix350 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem sound350 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node350 = Sparse.eval value350 (momentVector H) := by
  have heq : pivotMatrix350 = (fun u v => node350 (pivotPermutation350 u) v) := by apply Matrix.ext; unfold pivotMatrix350 node350 pivotPermutation350; decide +kernel
  have hmoment : injectiveMoment H node350 = injectiveMoment H pivotMatrix350 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix350 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix350 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix350 (0 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix350 (0 : Fin 4) = raw4138 := by apply Matrix.ext; unfold mergeFirst pivotMatrix350 raw4138; decide +kernel
    rw [heq]
    exact (canonical4138 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix350 (1 : Fin 4)) =
      Sparse.eval value100 (momentVector H) := by
    have heq : mergeFirst pivotMatrix350 (1 : Fin 4) = raw581 := by apply Matrix.ext; unfold mergeFirst pivotMatrix350 raw581; decide +kernel
    rw [heq]
    exact (canonical581 hH).trans (sound100 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix350 (2 : Fin 4)) =
      Sparse.eval value97 (momentVector H) := by
    have heq : mergeFirst pivotMatrix350 (2 : Fin 4) = raw555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix350 raw555; decide +kernel
    rw [heq]
    exact (canonical555 hH).trans (sound97 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix350 (3 : Fin 4)) =
      Sparse.eval value96 (momentVector H) := by
    have heq : mergeFirst pivotMatrix350 (3 : Fin 4) = raw547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix350 raw547; decide +kernel
    rw [heq]
    exact (canonical547 hH).trans (sound96 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node350 + (injectiveMoment H (mergeFirst pivotMatrix350 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix350 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix350 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix350 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value350, value100, value212, value96, value97, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation351 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix351 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem sound351 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node351 = Sparse.eval value351 (momentVector H) := by
  have heq : pivotMatrix351 = (fun u v => node351 (pivotPermutation351 u) v) := by apply Matrix.ext; unfold pivotMatrix351 node351 pivotPermutation351; decide +kernel
  have hmoment : injectiveMoment H node351 = injectiveMoment H pivotMatrix351 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix351 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix351 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix351 (0 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix351 (0 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix351 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix351 (1 : Fin 4)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix351 (1 : Fin 4) = raw579 := by apply Matrix.ext; unfold mergeFirst pivotMatrix351 raw579; decide +kernel
    rw [heq]
    exact (canonical579 hH).trans (sound223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix351 (2 : Fin 4)) =
      Sparse.eval value97 (momentVector H) := by
    have heq : mergeFirst pivotMatrix351 (2 : Fin 4) = raw555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix351 raw555; decide +kernel
    rw [heq]
    exact (canonical555 hH).trans (sound97 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix351 (3 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix351 (3 : Fin 4) = raw550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix351 raw550; decide +kernel
    rw [heq]
    exact (canonical550 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node351 + (injectiveMoment H (mergeFirst pivotMatrix351 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix351 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix351 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix351 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value351, value184, value198, value223, value97, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation352 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix352 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]

theorem sound352 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node352 = Sparse.eval value352 (momentVector H) := by
  have heq : pivotMatrix352 = (fun u v => node352 (pivotPermutation352 u) v) := by apply Matrix.ext; unfold pivotMatrix352 node352 pivotPermutation352; decide +kernel
  have hmoment : injectiveMoment H node352 = injectiveMoment H pivotMatrix352 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix352 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix352 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix352 (0 : Fin 4)) =
      Sparse.eval value141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix352 (0 : Fin 4) = raw480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix352 raw480; decide +kernel
    rw [heq]
    exact (canonical480 hH).trans (sound141 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix352 (1 : Fin 4)) =
      Sparse.eval value94 (momentVector H) := by
    have heq : mergeFirst pivotMatrix352 (1 : Fin 4) = raw687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix352 raw687; decide +kernel
    rw [heq]
    exact (canonical687 hH).trans (sound94 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix352 (2 : Fin 4)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix352 (2 : Fin 4) = raw708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix352 raw708; decide +kernel
    rw [heq]
    exact (canonical708 hH).trans (sound102 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix352 (3 : Fin 4)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix352 (3 : Fin 4) = raw711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix352 raw711; decide +kernel
    rw [heq]
    exact (canonical711 hH).trans (sound209 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node352 + (injectiveMoment H (mergeFirst pivotMatrix352 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix352 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix352 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix352 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value352, value102, value141, value209, value94, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation353 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix353 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

theorem sound353 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node353 = Sparse.eval value353 (momentVector H) := by
  have heq : pivotMatrix353 = (fun u v => node353 (pivotPermutation353 u) v) := by apply Matrix.ext; unfold pivotMatrix353 node353 pivotPermutation353; decide +kernel
  have hmoment : injectiveMoment H node353 = injectiveMoment H pivotMatrix353 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix353 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix353 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix353 (0 : Fin 4)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix353 (0 : Fin 4) = raw484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix353 raw484; decide +kernel
    rw [heq]
    exact (canonical484 hH).trans (sound163 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix353 (1 : Fin 4)) =
      Sparse.eval value96 (momentVector H) := by
    have heq : mergeFirst pivotMatrix353 (1 : Fin 4) = raw688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix353 raw688; decide +kernel
    rw [heq]
    exact (canonical688 hH).trans (sound96 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix353 (2 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix353 (2 : Fin 4) = raw713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix353 raw713; decide +kernel
    rw [heq]
    exact (canonical713 hH).trans (sound212 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix353 (3 : Fin 4)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix353 (3 : Fin 4) = raw714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix353 raw714; decide +kernel
    rw [heq]
    exact (canonical714 hH).trans (sound103 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node353 + (injectiveMoment H (mergeFirst pivotMatrix353 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix353 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix353 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix353 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value353, value103, value163, value212, value96, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation354 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix354 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]

theorem sound354 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node354 = Sparse.eval value354 (momentVector H) := by
  have heq : pivotMatrix354 = (fun u v => node354 (pivotPermutation354 u) v) := by apply Matrix.ext; unfold pivotMatrix354 node354 pivotPermutation354; decide +kernel
  have hmoment : injectiveMoment H node354 = injectiveMoment H pivotMatrix354 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix354 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix354 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix354 (0 : Fin 4)) =
      Sparse.eval value105 (momentVector H) := by
    have heq : mergeFirst pivotMatrix354 (0 : Fin 4) = raw828 := by apply Matrix.ext; unfold mergeFirst pivotMatrix354 raw828; decide +kernel
    rw [heq]
    exact (canonical828 hH).trans (sound105 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix354 (1 : Fin 4)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix354 (1 : Fin 4) = raw735 := by apply Matrix.ext; unfold mergeFirst pivotMatrix354 raw735; decide +kernel
    rw [heq]
    exact (canonical735 hH).trans (sound259 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix354 (2 : Fin 4)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix354 (2 : Fin 4) = raw704 := by apply Matrix.ext; unfold mergeFirst pivotMatrix354 raw704; decide +kernel
    rw [heq]
    exact (canonical704 hH).trans (sound101 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix354 (3 : Fin 4)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix354 (3 : Fin 4) = raw699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix354 raw699; decide +kernel
    rw [heq]
    exact (canonical699 hH).trans (sound214 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node354 + (injectiveMoment H (mergeFirst pivotMatrix354 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix354 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix354 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix354 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value354, value101, value105, value214, value259, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation355 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix355 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]

theorem sound355 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node355 = Sparse.eval value355 (momentVector H) := by
  have heq : pivotMatrix355 = (fun u v => node355 (pivotPermutation355 u) v) := by apply Matrix.ext; unfold pivotMatrix355 node355 pivotPermutation355; decide +kernel
  have hmoment : injectiveMoment H node355 = injectiveMoment H pivotMatrix355 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix355 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix355 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix355 (0 : Fin 4)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix355 (0 : Fin 4) = raw830 := by apply Matrix.ext; unfold mergeFirst pivotMatrix355 raw830; decide +kernel
    rw [heq]
    exact (canonical830 hH).trans (sound107 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix355 (1 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix355 (1 : Fin 4) = raw748 := by apply Matrix.ext; unfold mergeFirst pivotMatrix355 raw748; decide +kernel
    rw [heq]
    exact (canonical748 hH).trans (sound263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix355 (2 : Fin 4)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix355 (2 : Fin 4) = raw711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix355 raw711; decide +kernel
    rw [heq]
    exact (canonical711 hH).trans (sound209 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix355 (3 : Fin 4)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix355 (3 : Fin 4) = raw708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix355 raw708; decide +kernel
    rw [heq]
    exact (canonical708 hH).trans (sound102 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node355 + (injectiveMoment H (mergeFirst pivotMatrix355 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix355 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix355 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix355 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value355, value102, value107, value209, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation356 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix356 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

theorem sound356 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node356 = Sparse.eval value356 (momentVector H) := by
  have heq : pivotMatrix356 = (fun u v => node356 (pivotPermutation356 u) v) := by apply Matrix.ext; unfold pivotMatrix356 node356 pivotPermutation356; decide +kernel
  have hmoment : injectiveMoment H node356 = injectiveMoment H pivotMatrix356 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix356 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix356 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix356 (0 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix356 (0 : Fin 4) = raw832 := by apply Matrix.ext; unfold mergeFirst pivotMatrix356 raw832; decide +kernel
    rw [heq]
    exact (canonical832 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix356 (1 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix356 (1 : Fin 4) = raw750 := by apply Matrix.ext; unfold mergeFirst pivotMatrix356 raw750; decide +kernel
    rw [heq]
    exact (canonical750 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix356 (2 : Fin 4)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix356 (2 : Fin 4) = raw714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix356 raw714; decide +kernel
    rw [heq]
    exact (canonical714 hH).trans (sound103 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix356 (3 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix356 (3 : Fin 4) = raw713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix356 raw713; decide +kernel
    rw [heq]
    exact (canonical713 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node356 + (injectiveMoment H (mergeFirst pivotMatrix356 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix356 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix356 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix356 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value356, value103, value111, value212, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation357 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix357 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem sound357 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node357 = Sparse.eval value357 (momentVector H) := by
  have heq : pivotMatrix357 = (fun u v => node357 (pivotPermutation357 u) v) := by apply Matrix.ext; unfold pivotMatrix357 node357 pivotPermutation357; decide +kernel
  have hmoment : injectiveMoment H node357 = injectiveMoment H pivotMatrix357 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix357 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix357 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix357 (0 : Fin 4)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix357 (0 : Fin 4) = raw4034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix357 raw4034; decide +kernel
    rw [heq]
    exact (canonical4034 hH).trans (sound197 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix357 (1 : Fin 4)) =
      Sparse.eval value110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix357 (1 : Fin 4) = raw797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix357 raw797; decide +kernel
    rw [heq]
    exact (canonical797 hH).trans (sound110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix357 (2 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix357 (2 : Fin 4) = raw713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix357 raw713; decide +kernel
    rw [heq]
    exact (canonical713 hH).trans (sound212 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix357 (3 : Fin 4)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix357 (3 : Fin 4) = raw704 := by apply Matrix.ext; unfold mergeFirst pivotMatrix357 raw704; decide +kernel
    rw [heq]
    exact (canonical704 hH).trans (sound101 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node357 + (injectiveMoment H (mergeFirst pivotMatrix357 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix357 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix357 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix357 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value357, value101, value110, value197, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation358 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix358 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem sound358 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node358 = Sparse.eval value358 (momentVector H) := by
  have heq : pivotMatrix358 = (fun u v => node358 (pivotPermutation358 u) v) := by apply Matrix.ext; unfold pivotMatrix358 node358 pivotPermutation358; decide +kernel
  have hmoment : injectiveMoment H node358 = injectiveMoment H pivotMatrix358 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix358 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix358 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix358 (0 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix358 (0 : Fin 4) = raw4918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix358 raw4918; decide +kernel
    rw [heq]
    exact (canonical4918 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix358 (1 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix358 (1 : Fin 4) = raw802 := by apply Matrix.ext; unfold mergeFirst pivotMatrix358 raw802; decide +kernel
    rw [heq]
    exact (canonical802 hH).trans (sound111 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix358 (2 : Fin 4)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix358 (2 : Fin 4) = raw714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix358 raw714; decide +kernel
    rw [heq]
    exact (canonical714 hH).trans (sound103 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix358 (3 : Fin 4)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix358 (3 : Fin 4) = raw704 := by apply Matrix.ext; unfold mergeFirst pivotMatrix358 raw704; decide +kernel
    rw [heq]
    exact (canonical704 hH).trans (sound101 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node358 + (injectiveMoment H (mergeFirst pivotMatrix358 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix358 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix358 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix358 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value358, value101, value103, value111, value224, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation359 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix359 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem sound359 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node359 = Sparse.eval value359 (momentVector H) := by
  have heq : pivotMatrix359 = (fun u v => node359 (pivotPermutation359 u) v) := by apply Matrix.ext; unfold pivotMatrix359 node359 pivotPermutation359; decide +kernel
  have hmoment : injectiveMoment H node359 = injectiveMoment H pivotMatrix359 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix359 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix359 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix359 (0 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix359 (0 : Fin 4) = raw4042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix359 raw4042; decide +kernel
    rw [heq]
    exact (canonical4042 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix359 (1 : Fin 4)) =
      Sparse.eval value113 (momentVector H) := by
    have heq : mergeFirst pivotMatrix359 (1 : Fin 4) = raw798 := by apply Matrix.ext; unfold mergeFirst pivotMatrix359 raw798; decide +kernel
    rw [heq]
    exact (canonical798 hH).trans (sound113 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix359 (2 : Fin 4)) =
      Sparse.eval value104 (momentVector H) := by
    have heq : mergeFirst pivotMatrix359 (2 : Fin 4) = raw716 := by apply Matrix.ext; unfold mergeFirst pivotMatrix359 raw716; decide +kernel
    rw [heq]
    exact (canonical716 hH).trans (sound104 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix359 (3 : Fin 4)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix359 (3 : Fin 4) = raw708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix359 raw708; decide +kernel
    rw [heq]
    exact (canonical708 hH).trans (sound102 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node359 + (injectiveMoment H (mergeFirst pivotMatrix359 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix359 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix359 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix359 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value359, value102, value104, value113, value201, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation360 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix360 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

theorem sound360 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node360 = Sparse.eval value360 (momentVector H) := by
  have heq : pivotMatrix360 = (fun u v => node360 (pivotPermutation360 u) v) := by apply Matrix.ext; unfold pivotMatrix360 node360 pivotPermutation360; decide +kernel
  have hmoment : injectiveMoment H node360 = injectiveMoment H pivotMatrix360 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix360 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix360 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix360 (0 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix360 (0 : Fin 4) = raw4043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix360 raw4043; decide +kernel
    rw [heq]
    exact (canonical4043 hH).trans (sound169 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix360 (1 : Fin 4)) =
      Sparse.eval value108 (momentVector H) := by
    have heq : mergeFirst pivotMatrix360 (1 : Fin 4) = raw799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix360 raw799; decide +kernel
    rw [heq]
    exact (canonical799 hH).trans (sound108 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix360 (2 : Fin 4)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix360 (2 : Fin 4) = raw717 := by apply Matrix.ext; unfold mergeFirst pivotMatrix360 raw717; decide +kernel
    rw [heq]
    exact (canonical717 hH).trans (sound103 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix360 (3 : Fin 4)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix360 (3 : Fin 4) = raw711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix360 raw711; decide +kernel
    rw [heq]
    exact (canonical711 hH).trans (sound209 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node360 + (injectiveMoment H (mergeFirst pivotMatrix360 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix360 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix360 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix360 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value360, value103, value108, value169, value209, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation361 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix361 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem sound361 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node361 = Sparse.eval value361 (momentVector H) := by
  have heq : pivotMatrix361 = (fun u v => node361 (pivotPermutation361 u) v) := by apply Matrix.ext; unfold pivotMatrix361 node361 pivotPermutation361; decide +kernel
  have hmoment : injectiveMoment H node361 = injectiveMoment H pivotMatrix361 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix361 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix361 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix361 (0 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix361 (0 : Fin 4) = raw4044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix361 raw4044; decide +kernel
    rw [heq]
    exact (canonical4044 hH).trans (sound202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix361 (1 : Fin 4)) =
      Sparse.eval value114 (momentVector H) := by
    have heq : mergeFirst pivotMatrix361 (1 : Fin 4) = raw800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix361 raw800; decide +kernel
    rw [heq]
    exact (canonical800 hH).trans (sound114 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix361 (2 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix361 (2 : Fin 4) = raw718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix361 raw718; decide +kernel
    rw [heq]
    exact (canonical718 hH).trans (sound212 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix361 (3 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix361 (3 : Fin 4) = raw713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix361 raw713; decide +kernel
    rw [heq]
    exact (canonical713 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node361 + (injectiveMoment H (mergeFirst pivotMatrix361 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix361 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix361 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix361 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value361, value114, value202, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation362 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix362 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

theorem sound362 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node362 = Sparse.eval value362 (momentVector H) := by
  have heq : pivotMatrix362 = (fun u v => node362 (pivotPermutation362 u) v) := by apply Matrix.ext; unfold pivotMatrix362 node362 pivotPermutation362; decide +kernel
  have hmoment : injectiveMoment H node362 = injectiveMoment H pivotMatrix362 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix362 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix362 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix362 (0 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix362 (0 : Fin 4) = raw505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix362 raw505; decide +kernel
    rw [heq]
    exact (canonical505 hH).trans (sound155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix362 (1 : Fin 4)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix362 (1 : Fin 4) = raw708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix362 raw708; decide +kernel
    rw [heq]
    exact (canonical708 hH).trans (sound102 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix362 (2 : Fin 4)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix362 (2 : Fin 4) = raw744 := by apply Matrix.ext; unfold mergeFirst pivotMatrix362 raw744; decide +kernel
    rw [heq]
    exact (canonical744 hH).trans (sound106 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix362 (3 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix362 (3 : Fin 4) = raw748 := by apply Matrix.ext; unfold mergeFirst pivotMatrix362 raw748; decide +kernel
    rw [heq]
    exact (canonical748 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node362 + (injectiveMoment H (mergeFirst pivotMatrix362 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix362 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix362 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix362 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value362, value102, value106, value155, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation363 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix363 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

theorem sound363 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node363 = Sparse.eval value363 (momentVector H) := by
  have heq : pivotMatrix363 = (fun u v => node363 (pivotPermutation363 u) v) := by apply Matrix.ext; unfold pivotMatrix363 node363 pivotPermutation363; decide +kernel
  have hmoment : injectiveMoment H node363 = injectiveMoment H pivotMatrix363 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix363 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix363 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix363 (0 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix363 (0 : Fin 4) = raw506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix363 raw506; decide +kernel
    rw [heq]
    exact (canonical506 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix363 (1 : Fin 4)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix363 (1 : Fin 4) = raw714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix363 raw714; decide +kernel
    rw [heq]
    exact (canonical714 hH).trans (sound103 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix363 (2 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix363 (2 : Fin 4) = raw750 := by apply Matrix.ext; unfold mergeFirst pivotMatrix363 raw750; decide +kernel
    rw [heq]
    exact (canonical750 hH).trans (sound261 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix363 (3 : Fin 4)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix363 (3 : Fin 4) = raw751 := by apply Matrix.ext; unfold mergeFirst pivotMatrix363 raw751; decide +kernel
    rw [heq]
    exact (canonical751 hH).trans (sound107 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node363 + (injectiveMoment H (mergeFirst pivotMatrix363 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix363 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix363 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix363 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value363, value103, value107, value187, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation364 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix364 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

theorem sound364 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node364 = Sparse.eval value364 (momentVector H) := by
  have heq : pivotMatrix364 = (fun u v => node364 (pivotPermutation364 u) v) := by apply Matrix.ext; unfold pivotMatrix364 node364 pivotPermutation364; decide +kernel
  have hmoment : injectiveMoment H node364 = injectiveMoment H pivotMatrix364 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix364 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix364 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix364 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix364 (0 : Fin 4) = raw522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix364 raw522; decide +kernel
    rw [heq]
    exact (canonical522 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix364 (1 : Fin 4)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix364 (1 : Fin 4) = raw755 := by apply Matrix.ext; unfold mergeFirst pivotMatrix364 raw755; decide +kernel
    rw [heq]
    exact (canonical755 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix364 (2 : Fin 4)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix364 (2 : Fin 4) = raw763 := by apply Matrix.ext; unfold mergeFirst pivotMatrix364 raw763; decide +kernel
    rw [heq]
    exact (canonical763 hH).trans (sound63 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix364 (3 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix364 (3 : Fin 4) = raw771 := by apply Matrix.ext; unfold mergeFirst pivotMatrix364 raw771; decide +kernel
    rw [heq]
    exact (canonical771 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node364 + (injectiveMoment H (mergeFirst pivotMatrix364 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix364 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix364 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix364 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value364, value188, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation365 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix365 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

theorem sound365 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node365 = Sparse.eval value365 (momentVector H) := by
  have heq : pivotMatrix365 = (fun u v => node365 (pivotPermutation365 u) v) := by apply Matrix.ext; unfold pivotMatrix365 node365 pivotPermutation365; decide +kernel
  have hmoment : injectiveMoment H node365 = injectiveMoment H pivotMatrix365 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix365 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix365 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix365 (0 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix365 (0 : Fin 4) = raw532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix365 raw532; decide +kernel
    rw [heq]
    exact (canonical532 hH).trans (sound222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix365 (1 : Fin 4)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix365 (1 : Fin 4) = raw757 := by apply Matrix.ext; unfold mergeFirst pivotMatrix365 raw757; decide +kernel
    rw [heq]
    exact (canonical757 hH).trans (sound43 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix365 (2 : Fin 4)) =
      Sparse.eval value108 (momentVector H) := by
    have heq : mergeFirst pivotMatrix365 (2 : Fin 4) = raw775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix365 raw775; decide +kernel
    rw [heq]
    exact (canonical775 hH).trans (sound108 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix365 (3 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix365 (3 : Fin 4) = raw778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix365 raw778; decide +kernel
    rw [heq]
    exact (canonical778 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node365 + (injectiveMoment H (mergeFirst pivotMatrix365 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix365 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix365 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix365 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value365, value108, value222, value226, value43, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation366 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix366 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

theorem sound366 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node366 = Sparse.eval value366 (momentVector H) := by
  have heq : pivotMatrix366 = (fun u v => node366 (pivotPermutation366 u) v) := by apply Matrix.ext; unfold pivotMatrix366 node366 pivotPermutation366; decide +kernel
  have hmoment : injectiveMoment H node366 = injectiveMoment H pivotMatrix366 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix366 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix366 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix366 (0 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix366 (0 : Fin 4) = raw538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix366 raw538; decide +kernel
    rw [heq]
    exact (canonical538 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix366 (1 : Fin 4)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix366 (1 : Fin 4) = raw759 := by apply Matrix.ext; unfold mergeFirst pivotMatrix366 raw759; decide +kernel
    rw [heq]
    exact (canonical759 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix366 (2 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix366 (2 : Fin 4) = raw782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix366 raw782; decide +kernel
    rw [heq]
    exact (canonical782 hH).trans (sound185 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix366 (3 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix366 (3 : Fin 4) = raw783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix366 raw783; decide +kernel
    rw [heq]
    exact (canonical783 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node366 + (injectiveMoment H (mergeFirst pivotMatrix366 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix366 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix366 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix366 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value366, value109, value185, value215, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation367 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix367 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem sound367 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node367 = Sparse.eval value367 (momentVector H) := by
  have heq : pivotMatrix367 = (fun u v => node367 (pivotPermutation367 u) v) := by apply Matrix.ext; unfold pivotMatrix367 node367 pivotPermutation367; decide +kernel
  have hmoment : injectiveMoment H node367 = injectiveMoment H pivotMatrix367 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix367 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix367 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix367 (0 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix367 (0 : Fin 4) = raw550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix367 raw550; decide +kernel
    rw [heq]
    exact (canonical550 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix367 (1 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix367 (1 : Fin 4) = raw778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix367 raw778; decide +kernel
    rw [heq]
    exact (canonical778 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix367 (2 : Fin 4)) =
      Sparse.eval value110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix367 (2 : Fin 4) = raw786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix367 raw786; decide +kernel
    rw [heq]
    exact (canonical786 hH).trans (sound110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix367 (3 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix367 (3 : Fin 4) = raw789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix367 raw789; decide +kernel
    rw [heq]
    exact (canonical789 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node367 + (injectiveMoment H (mergeFirst pivotMatrix367 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix367 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix367 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix367 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value367, value110, value111, value198, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation368 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix368 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

theorem sound368 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node368 = Sparse.eval value368 (momentVector H) := by
  have heq : pivotMatrix368 = (fun u v => node368 (pivotPermutation368 u) v) := by apply Matrix.ext; unfold pivotMatrix368 node368 pivotPermutation368; decide +kernel
  have hmoment : injectiveMoment H node368 = injectiveMoment H pivotMatrix368 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix368 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix368 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix368 (0 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix368 (0 : Fin 4) = raw552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix368 raw552; decide +kernel
    rw [heq]
    exact (canonical552 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix368 (1 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix368 (1 : Fin 4) = raw781 := by apply Matrix.ext; unfold mergeFirst pivotMatrix368 raw781; decide +kernel
    rw [heq]
    exact (canonical781 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix368 (2 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix368 (2 : Fin 4) = raw789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix368 raw789; decide +kernel
    rw [heq]
    exact (canonical789 hH).trans (sound111 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix368 (3 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix368 (3 : Fin 4) = raw792 := by apply Matrix.ext; unfold mergeFirst pivotMatrix368 raw792; decide +kernel
    rw [heq]
    exact (canonical792 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node368 + (injectiveMoment H (mergeFirst pivotMatrix368 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix368 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix368 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix368 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value368, value111, value177, value181, value215, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation369 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix369 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem sound369 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node369 = Sparse.eval value369 (momentVector H) := by
  have heq : pivotMatrix369 = (fun u v => node369 (pivotPermutation369 u) v) := by apply Matrix.ext; unfold pivotMatrix369 node369 pivotPermutation369; decide +kernel
  have hmoment : injectiveMoment H node369 = injectiveMoment H pivotMatrix369 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix369 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix369 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix369 (0 : Fin 4)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix369 (0 : Fin 4) = raw553 := by apply Matrix.ext; unfold mergeFirst pivotMatrix369 raw553; decide +kernel
    rw [heq]
    exact (canonical553 hH).trans (sound204 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix369 (1 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix369 (1 : Fin 4) = raw782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix369 raw782; decide +kernel
    rw [heq]
    exact (canonical782 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix369 (2 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix369 (2 : Fin 4) = raw792 := by apply Matrix.ext; unfold mergeFirst pivotMatrix369 raw792; decide +kernel
    rw [heq]
    exact (canonical792 hH).trans (sound177 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix369 (3 : Fin 4)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix369 (3 : Fin 4) = raw793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix369 raw793; decide +kernel
    rw [heq]
    exact (canonical793 hH).trans (sound107 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node369 + (injectiveMoment H (mergeFirst pivotMatrix369 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix369 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix369 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix369 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value369, value107, value177, value185, value204, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation370 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix370 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

theorem sound370 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node370 = Sparse.eval value370 (momentVector H) := by
  have heq : pivotMatrix370 = (fun u v => node370 (pivotPermutation370 u) v) := by apply Matrix.ext; unfold pivotMatrix370 node370 pivotPermutation370; decide +kernel
  have hmoment : injectiveMoment H node370 = injectiveMoment H pivotMatrix370 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix370 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix370 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix370 (0 : Fin 4)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix370 (0 : Fin 4) = raw574 := by apply Matrix.ext; unfold mergeFirst pivotMatrix370 raw574; decide +kernel
    rw [heq]
    exact (canonical574 hH).trans (sound87 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix370 (1 : Fin 4)) =
      Sparse.eval value113 (momentVector H) := by
    have heq : mergeFirst pivotMatrix370 (1 : Fin 4) = raw798 := by apply Matrix.ext; unfold mergeFirst pivotMatrix370 raw798; decide +kernel
    rw [heq]
    exact (canonical798 hH).trans (sound113 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix370 (2 : Fin 4)) =
      Sparse.eval value115 (momentVector H) := by
    have heq : mergeFirst pivotMatrix370 (2 : Fin 4) = raw803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix370 raw803; decide +kernel
    rw [heq]
    exact (canonical803 hH).trans (sound115 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix370 (3 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix370 (3 : Fin 4) = raw804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix370 raw804; decide +kernel
    rw [heq]
    exact (canonical804 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node370 + (injectiveMoment H (mergeFirst pivotMatrix370 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix370 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix370 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix370 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value370, value109, value113, value115, value87, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation371 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix371 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

theorem sound371 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node371 = Sparse.eval value371 (momentVector H) := by
  have heq : pivotMatrix371 = (fun u v => node371 (pivotPermutation371 u) v) := by apply Matrix.ext; unfold pivotMatrix371 node371 pivotPermutation371; decide +kernel
  have hmoment : injectiveMoment H node371 = injectiveMoment H pivotMatrix371 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix371 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix371 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix371 (0 : Fin 4)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix371 (0 : Fin 4) = raw575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix371 raw575; decide +kernel
    rw [heq]
    exact (canonical575 hH).trans (sound170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix371 (1 : Fin 4)) =
      Sparse.eval value108 (momentVector H) := by
    have heq : mergeFirst pivotMatrix371 (1 : Fin 4) = raw799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix371 raw799; decide +kernel
    rw [heq]
    exact (canonical799 hH).trans (sound108 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix371 (2 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix371 (2 : Fin 4) = raw804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix371 raw804; decide +kernel
    rw [heq]
    exact (canonical804 hH).trans (sound109 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix371 (3 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix371 (3 : Fin 4) = raw805 := by apply Matrix.ext; unfold mergeFirst pivotMatrix371 raw805; decide +kernel
    rw [heq]
    exact (canonical805 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node371 + (injectiveMoment H (mergeFirst pivotMatrix371 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix371 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix371 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix371 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value371, value108, value109, value170, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation372 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix372 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem sound372 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node372 = Sparse.eval value372 (momentVector H) := by
  have heq : pivotMatrix372 = (fun u v => node372 (pivotPermutation372 u) v) := by apply Matrix.ext; unfold pivotMatrix372 node372 pivotPermutation372; decide +kernel
  have hmoment : injectiveMoment H node372 = injectiveMoment H pivotMatrix372 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix372 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix372 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix372 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix372 (0 : Fin 4) = raw578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix372 raw578; decide +kernel
    rw [heq]
    exact (canonical578 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix372 (1 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix372 (1 : Fin 4) = raw804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix372 raw804; decide +kernel
    rw [heq]
    exact (canonical804 hH).trans (sound109 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix372 (2 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix372 (2 : Fin 4) = raw807 := by apply Matrix.ext; unfold mergeFirst pivotMatrix372 raw807; decide +kernel
    rw [heq]
    exact (canonical807 hH).trans (sound109 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix372 (3 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix372 (3 : Fin 4) = raw808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix372 raw808; decide +kernel
    rw [heq]
    exact (canonical808 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node372 + (injectiveMoment H (mergeFirst pivotMatrix372 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix372 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix372 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix372 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value372, value109, value176, value188, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation373 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix373 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

theorem sound373 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node373 = Sparse.eval value373 (momentVector H) := by
  have heq : pivotMatrix373 = (fun u v => node373 (pivotPermutation373 u) v) := by apply Matrix.ext; unfold pivotMatrix373 node373 pivotPermutation373; decide +kernel
  have hmoment : injectiveMoment H node373 = injectiveMoment H pivotMatrix373 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix373 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix373 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix373 (0 : Fin 4)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix373 (0 : Fin 4) = raw834 := by apply Matrix.ext; unfold mergeFirst pivotMatrix373 raw834; decide +kernel
    rw [heq]
    exact (canonical834 hH).trans (sound107 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix373 (1 : Fin 4)) =
      Sparse.eval value110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix373 (1 : Fin 4) = raw786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix373 raw786; decide +kernel
    rw [heq]
    exact (canonical786 hH).trans (sound110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix373 (2 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix373 (2 : Fin 4) = raw778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix373 raw778; decide +kernel
    rw [heq]
    exact (canonical778 hH).trans (sound226 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix373 (3 : Fin 4)) =
      Sparse.eval value108 (momentVector H) := by
    have heq : mergeFirst pivotMatrix373 (3 : Fin 4) = raw775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix373 raw775; decide +kernel
    rw [heq]
    exact (canonical775 hH).trans (sound108 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node373 + (injectiveMoment H (mergeFirst pivotMatrix373 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix373 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix373 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix373 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value373, value107, value108, value110, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation374 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix374 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem sound374 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node374 = Sparse.eval value374 (momentVector H) := by
  have heq : pivotMatrix374 = (fun u v => node374 (pivotPermutation374 u) v) := by apply Matrix.ext; unfold pivotMatrix374 node374 pivotPermutation374; decide +kernel
  have hmoment : injectiveMoment H node374 = injectiveMoment H pivotMatrix374 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix374 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix374 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix374 (0 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix374 (0 : Fin 4) = raw836 := by apply Matrix.ext; unfold mergeFirst pivotMatrix374 raw836; decide +kernel
    rw [heq]
    exact (canonical836 hH).trans (sound261 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix374 (1 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix374 (1 : Fin 4) = raw789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix374 raw789; decide +kernel
    rw [heq]
    exact (canonical789 hH).trans (sound111 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix374 (2 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix374 (2 : Fin 4) = raw781 := by apply Matrix.ext; unfold mergeFirst pivotMatrix374 raw781; decide +kernel
    rw [heq]
    exact (canonical781 hH).trans (sound181 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix374 (3 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix374 (3 : Fin 4) = raw778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix374 raw778; decide +kernel
    rw [heq]
    exact (canonical778 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node374 + (injectiveMoment H (mergeFirst pivotMatrix374 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix374 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix374 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix374 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value374, value111, value181, value226, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation375 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix375 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

theorem sound375 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node375 = Sparse.eval value375 (momentVector H) := by
  have heq : pivotMatrix375 = (fun u v => node375 (pivotPermutation375 u) v) := by apply Matrix.ext; unfold pivotMatrix375 node375 pivotPermutation375; decide +kernel
  have hmoment : injectiveMoment H node375 = injectiveMoment H pivotMatrix375 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix375 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix375 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix375 (0 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix375 (0 : Fin 4) = raw837 := by apply Matrix.ext; unfold mergeFirst pivotMatrix375 raw837; decide +kernel
    rw [heq]
    exact (canonical837 hH).trans (sound109 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix375 (1 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix375 (1 : Fin 4) = raw805 := by apply Matrix.ext; unfold mergeFirst pivotMatrix375 raw805; decide +kernel
    rw [heq]
    exact (canonical805 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix375 (2 : Fin 4)) =
      Sparse.eval value114 (momentVector H) := by
    have heq : mergeFirst pivotMatrix375 (2 : Fin 4) = raw800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix375 raw800; decide +kernel
    rw [heq]
    exact (canonical800 hH).trans (sound114 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix375 (3 : Fin 4)) =
      Sparse.eval value108 (momentVector H) := by
    have heq : mergeFirst pivotMatrix375 (3 : Fin 4) = raw799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix375 raw799; decide +kernel
    rw [heq]
    exact (canonical799 hH).trans (sound108 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node375 + (injectiveMoment H (mergeFirst pivotMatrix375 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix375 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix375 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix375 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value375, value108, value109, value114, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation376 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix376 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

theorem sound376 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node376 = Sparse.eval value376 (momentVector H) := by
  have heq : pivotMatrix376 = (fun u v => node376 (pivotPermutation376 u) v) := by apply Matrix.ext; unfold pivotMatrix376 node376 pivotPermutation376; decide +kernel
  have hmoment : injectiveMoment H node376 = injectiveMoment H pivotMatrix376 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix376 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix376 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix376 (0 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix376 (0 : Fin 4) = raw839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix376 raw839; decide +kernel
    rw [heq]
    exact (canonical839 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix376 (1 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix376 (1 : Fin 4) = raw808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix376 raw808; decide +kernel
    rw [heq]
    exact (canonical808 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix376 (2 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix376 (2 : Fin 4) = raw805 := by apply Matrix.ext; unfold mergeFirst pivotMatrix376 raw805; decide +kernel
    rw [heq]
    exact (canonical805 hH).trans (sound229 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix376 (3 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix376 (3 : Fin 4) = raw804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix376 raw804; decide +kernel
    rw [heq]
    exact (canonical804 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node376 + (injectiveMoment H (mergeFirst pivotMatrix376 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix376 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix376 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix376 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value376, value109, value176, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation377 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix377 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem sound377 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node377 = Sparse.eval value377 (momentVector H) := by
  have heq : pivotMatrix377 = (fun u v => node377 (pivotPermutation377 u) v) := by apply Matrix.ext; unfold pivotMatrix377 node377 pivotPermutation377; decide +kernel
  have hmoment : injectiveMoment H node377 = injectiveMoment H pivotMatrix377 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix377 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix377 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix377 (0 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix377 (0 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix377 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix377 (1 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix377 (1 : Fin 4) = raw812 := by apply Matrix.ext; unfold mergeFirst pivotMatrix377 raw812; decide +kernel
    rw [heq]
    exact (canonical812 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix377 (2 : Fin 4)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix377 (2 : Fin 4) = raw794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix377 raw794; decide +kernel
    rw [heq]
    exact (canonical794 hH).trans (sound107 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix377 (3 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix377 (3 : Fin 4) = raw789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix377 raw789; decide +kernel
    rw [heq]
    exact (canonical789 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node377 + (injectiveMoment H (mergeFirst pivotMatrix377 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix377 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix377 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix377 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value377, value107, value111, value203, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation378 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix378 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]

theorem sound378 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node378 = Sparse.eval value378 (momentVector H) := by
  have heq : pivotMatrix378 = (fun u v => node378 (pivotPermutation378 u) v) := by apply Matrix.ext; unfold pivotMatrix378 node378 pivotPermutation378; decide +kernel
  have hmoment : injectiveMoment H node378 = injectiveMoment H pivotMatrix378 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix378 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix378 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix378 (0 : Fin 4)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix378 (0 : Fin 4) = raw711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix378 raw711; decide +kernel
    rw [heq]
    exact (canonical711 hH).trans (sound209 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix378 (1 : Fin 4)) =
      Sparse.eval value95 (momentVector H) := by
    have heq : mergeFirst pivotMatrix378 (1 : Fin 4) = raw823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix378 raw823; decide +kernel
    rw [heq]
    exact (canonical823 hH).trans (sound95 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix378 (2 : Fin 4)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix378 (2 : Fin 4) = raw830 := by apply Matrix.ext; unfold mergeFirst pivotMatrix378 raw830; decide +kernel
    rw [heq]
    exact (canonical830 hH).trans (sound107 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix378 (3 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix378 (3 : Fin 4) = raw831 := by apply Matrix.ext; unfold mergeFirst pivotMatrix378 raw831; decide +kernel
    rw [heq]
    exact (canonical831 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node378 + (injectiveMoment H (mergeFirst pivotMatrix378 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix378 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix378 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix378 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value378, value107, value177, value209, value95, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation379 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix379 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

theorem sound379 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node379 = Sparse.eval value379 (momentVector H) := by
  have heq : pivotMatrix379 = (fun u v => node379 (pivotPermutation379 u) v) := by apply Matrix.ext; unfold pivotMatrix379 node379 pivotPermutation379; decide +kernel
  have hmoment : injectiveMoment H node379 = injectiveMoment H pivotMatrix379 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix379 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix379 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix379 (0 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix379 (0 : Fin 4) = raw713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix379 raw713; decide +kernel
    rw [heq]
    exact (canonical713 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix379 (1 : Fin 4)) =
      Sparse.eval value97 (momentVector H) := by
    have heq : mergeFirst pivotMatrix379 (1 : Fin 4) = raw824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix379 raw824; decide +kernel
    rw [heq]
    exact (canonical824 hH).trans (sound97 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix379 (2 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix379 (2 : Fin 4) = raw831 := by apply Matrix.ext; unfold mergeFirst pivotMatrix379 raw831; decide +kernel
    rw [heq]
    exact (canonical831 hH).trans (sound177 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix379 (3 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix379 (3 : Fin 4) = raw832 := by apply Matrix.ext; unfold mergeFirst pivotMatrix379 raw832; decide +kernel
    rw [heq]
    exact (canonical832 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node379 + (injectiveMoment H (mergeFirst pivotMatrix379 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix379 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix379 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix379 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value379, value111, value177, value212, value97, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation380 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix380 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem sound380 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node380 = Sparse.eval value380 (momentVector H) := by
  have heq : pivotMatrix380 = (fun u v => node380 (pivotPermutation380 u) v) := by apply Matrix.ext; unfold pivotMatrix380 node380 pivotPermutation380; decide +kernel
  have hmoment : injectiveMoment H node380 = injectiveMoment H pivotMatrix380 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix380 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix380 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix380 (0 : Fin 5)) =
      Sparse.eval value231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix380 (0 : Fin 5) = raw5110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix380 raw5110; decide +kernel
    rw [heq]
    exact (canonical5110 hH).trans (sound231 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix380 (1 : Fin 5)) =
      Sparse.eval value118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix380 (1 : Fin 5) = raw867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix380 raw867; decide +kernel
    rw [heq]
    exact (canonical867 hH).trans (sound118 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix380 (2 : Fin 5)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix380 (2 : Fin 5) = raw851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix380 raw851; decide +kernel
    rw [heq]
    exact (canonical851 hH).trans (sound117 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix380 (3 : Fin 5)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix380 (3 : Fin 5) = raw849 := by apply Matrix.ext; unfold mergeFirst pivotMatrix380 raw849; decide +kernel
    rw [heq]
    exact (canonical849 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix380 (4 : Fin 5)) =
      Sparse.eval value116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix380 (4 : Fin 5) = raw848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix380 raw848; decide +kernel
    rw [heq]
    exact (canonical848 hH).trans (sound116 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node380 + (injectiveMoment H (mergeFirst pivotMatrix380 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix380 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix380 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix380 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix380 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value380, value116, value117, value118, value231, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation381 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix381 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

theorem sound381 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node381 = Sparse.eval value381 (momentVector H) := by
  have heq : pivotMatrix381 = (fun u v => node381 (pivotPermutation381 u) v) := by apply Matrix.ext; unfold pivotMatrix381 node381 pivotPermutation381; decide +kernel
  have hmoment : injectiveMoment H node381 = injectiveMoment H pivotMatrix381 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix381 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix381 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix381 (0 : Fin 5)) =
      Sparse.eval value67 (momentVector H) := by
    have heq : mergeFirst pivotMatrix381 (0 : Fin 5) = raw188 := by apply Matrix.ext; unfold mergeFirst pivotMatrix381 raw188; decide +kernel
    rw [heq]
    exact (canonical188 hH).trans (sound67 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix381 (1 : Fin 5)) =
      Sparse.eval value116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix381 (1 : Fin 5) = raw848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix381 raw848; decide +kernel
    rw [heq]
    exact (canonical848 hH).trans (sound116 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix381 (2 : Fin 5)) =
      Sparse.eval value24 (momentVector H) := by
    have heq : mergeFirst pivotMatrix381 (2 : Fin 5) = raw860 := by apply Matrix.ext; unfold mergeFirst pivotMatrix381 raw860; decide +kernel
    rw [heq]
    exact (canonical860 hH).trans (sound24 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix381 (3 : Fin 5)) =
      Sparse.eval value24 (momentVector H) := by
    have heq : mergeFirst pivotMatrix381 (3 : Fin 5) = raw864 := by apply Matrix.ext; unfold mergeFirst pivotMatrix381 raw864; decide +kernel
    rw [heq]
    exact (canonical864 hH).trans (sound24 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix381 (4 : Fin 5)) =
      Sparse.eval value118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix381 (4 : Fin 5) = raw867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix381 raw867; decide +kernel
    rw [heq]
    exact (canonical867 hH).trans (sound118 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node381 + (injectiveMoment H (mergeFirst pivotMatrix381 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix381 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix381 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix381 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix381 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value381, value116, value118, value24, value67, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation382 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix382 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

theorem sound382 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node382 = Sparse.eval value382 (momentVector H) := by
  have heq : pivotMatrix382 = (fun u v => node382 (pivotPermutation382 u) v) := by apply Matrix.ext; unfold pivotMatrix382 node382 pivotPermutation382; decide +kernel
  have hmoment : injectiveMoment H node382 = injectiveMoment H pivotMatrix382 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix382 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix382 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix382 (0 : Fin 5)) =
      Sparse.eval value68 (momentVector H) := by
    have heq : mergeFirst pivotMatrix382 (0 : Fin 5) = raw189 := by apply Matrix.ext; unfold mergeFirst pivotMatrix382 raw189; decide +kernel
    rw [heq]
    exact (canonical189 hH).trans (sound68 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix382 (1 : Fin 5)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix382 (1 : Fin 5) = raw849 := by apply Matrix.ext; unfold mergeFirst pivotMatrix382 raw849; decide +kernel
    rw [heq]
    exact (canonical849 hH).trans (sound117 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix382 (2 : Fin 5)) =
      Sparse.eval value25 (momentVector H) := by
    have heq : mergeFirst pivotMatrix382 (2 : Fin 5) = raw861 := by apply Matrix.ext; unfold mergeFirst pivotMatrix382 raw861; decide +kernel
    rw [heq]
    exact (canonical861 hH).trans (sound25 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix382 (3 : Fin 5)) =
      Sparse.eval value118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix382 (3 : Fin 5) = raw867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix382 raw867; decide +kernel
    rw [heq]
    exact (canonical867 hH).trans (sound118 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix382 (4 : Fin 5)) =
      Sparse.eval value118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix382 (4 : Fin 5) = raw868 := by apply Matrix.ext; unfold mergeFirst pivotMatrix382 raw868; decide +kernel
    rw [heq]
    exact (canonical868 hH).trans (sound118 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node382 + (injectiveMoment H (mergeFirst pivotMatrix382 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix382 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix382 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix382 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix382 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value382, value117, value118, value25, value68, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation383 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix383 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem sound383 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node383 = Sparse.eval value383 (momentVector H) := by
  have heq : pivotMatrix383 = (fun u v => node383 (pivotPermutation383 u) v) := by apply Matrix.ext; unfold pivotMatrix383 node383 pivotPermutation383; decide +kernel
  have hmoment : injectiveMoment H node383 = injectiveMoment H pivotMatrix383 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix383 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix383 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix383 (0 : Fin 5)) =
      Sparse.eval value69 (momentVector H) := by
    have heq : mergeFirst pivotMatrix383 (0 : Fin 5) = raw207 := by apply Matrix.ext; unfold mergeFirst pivotMatrix383 raw207; decide +kernel
    rw [heq]
    exact (canonical207 hH).trans (sound69 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix383 (1 : Fin 5)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix383 (1 : Fin 5) = raw893 := by apply Matrix.ext; unfold mergeFirst pivotMatrix383 raw893; decide +kernel
    rw [heq]
    exact (canonical893 hH).trans (sound26 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix383 (2 : Fin 5)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix383 (2 : Fin 5) = raw907 := by apply Matrix.ext; unfold mergeFirst pivotMatrix383 raw907; decide +kernel
    rw [heq]
    exact (canonical907 hH).trans (sound26 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix383 (3 : Fin 5)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix383 (3 : Fin 5) = raw912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix383 raw912; decide +kernel
    rw [heq]
    exact (canonical912 hH).trans (sound26 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix383 (4 : Fin 5)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix383 (4 : Fin 5) = raw915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix383 raw915; decide +kernel
    rw [heq]
    exact (canonical915 hH).trans (sound26 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node383 + (injectiveMoment H (mergeFirst pivotMatrix383 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix383 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix383 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix383 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix383 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value383, value26, value69, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
