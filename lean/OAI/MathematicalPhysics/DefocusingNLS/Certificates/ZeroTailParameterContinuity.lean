import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHomotopyContinuity

namespace OAI

/-! # Joint parameter continuity of the finite zero-tail determinant

At tail parameter zero the matching column is the second column of the finite
backward matrix product. Its continuity therefore holds for all parameters,
without any integral-kernel continuity or nonvanishing hypothesis.
-/

open Matrix

namespace DefocusingNLS

attribute [local irreducible] backwardProduct matchingHomotopyColumn

theorem continuous_backwardMatrix_entry (M : ℂ) (n : ℕ) (i j : Fin 2) :
    Continuous (fun x : ℂ × ℂ => backwardMatrix M x.1 (x.2 + n) i j) := by
  fin_cases i <;> fin_cases j
  · change Continuous (fun x : ℂ × ℂ => x.2 + n - M - x.1)
    fun_prop
  · change Continuous (fun x : ℂ × ℂ => -x.1)
    fun_prop
  · change Continuous (fun x : ℂ × ℂ => x.2 + n)
    fun_prop
  · change Continuous (fun x : ℂ × ℂ => x.2 + n)
    fun_prop

theorem continuous_backwardProduct_entry (M : ℂ) (K : ℕ) (i j : Fin 2) :
    Continuous (fun x : ℂ × ℂ => backwardProduct M x.1 x.2 K i j) := by
  induction K generalizing i j with
  | zero =>
      simp only [backwardProduct]
      exact continuous_const
  | succ K ih =>
      simp only [backwardProduct, Matrix.mul_apply, Fin.sum_univ_two]
      exact ((ih i 0).mul (continuous_backwardMatrix_entry M K 0 j)).add
        ((ih i 1).mul (continuous_backwardMatrix_entry M K 1 j))

theorem matchingHomotopyColumn_zero_entry (M K : ℕ) (s q : ℂ) (i : Fin 2) :
    matchingHomotopyColumn M K s 0 q i = backwardProduct M s q K i 1 := by
  rw [matchingHomotopyColumn_zero]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Coordinates are the real shift, real coupling, and complex spectral value. -/
abbrev ZeroTailParameters := ℝ × ℝ × ℂ

theorem continuous_zeroTail_spectralColumn (ell : ℕ) (h : ℝ) (i : Fin 2) :
    Continuous (fun x : ZeroTailParameters =>
      matchingHomotopyColumn (ell + 5) 8 ((h : ℂ) * Complex.I * x.2.1) 0
        (spectralQ ell h x.1 x.2.2) i) := by
  have hc : Continuous (fun x : ZeroTailParameters =>
      ((h : ℂ) * Complex.I * x.2.1, spectralQ ell h x.1 x.2.2)) := by
    unfold spectralQ
    fun_prop
  have hp := (continuous_backwardProduct_entry (ell + 5) 8 i 1).comp hc
  simpa only [matchingHomotopyColumn_zero_entry, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using hp

theorem continuous_zeroTail_spectralDeterminant (ell : ℕ) :
    Continuous (fun x : ZeroTailParameters =>
      spectralHomotopyDeterminant ell x.1 x.2.1 0 x.2.2) := by
  have hp0 := continuous_zeroTail_spectralColumn ell 1 0
  have hp1 := continuous_zeroTail_spectralColumn ell 1 1
  have hm0 := continuous_zeroTail_spectralColumn ell (-1) 0
  have hm1 := continuous_zeroTail_spectralColumn ell (-1) 1
  have hc := (hp0.mul hm1).sub (hp1.mul hm0)
  unfold spectralHomotopyDeterminant
  convert! hc using 1
  funext x
  simp only [matchingColumnDeterminant, Pi.mul_apply, Pi.sub_apply,
    Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_one_mul]

end DefocusingNLS

end OAI
