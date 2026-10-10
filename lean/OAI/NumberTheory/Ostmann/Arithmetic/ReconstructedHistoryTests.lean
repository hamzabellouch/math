import OAI.NumberTheory.Ostmann.Arithmetic.IntegerHistoryReconstruction
import OAI.NumberTheory.Ostmann.Arithmetic.ClearedPolynomialRanges

namespace OAI

/-! # Original reconstructed-integer tests are literal cleared polynomial tests -/

namespace Ostmann

open scoped Classical

/-- Cast the exact integral numerator equation, avoiding any approximation
of a reconstructed rational value. -/
theorem ClearedHistoryValue.real_value_of_integer {σ : Type*} (F : ClearedHistoryValue σ)
    (x : σ → ℤ) (y : ℤ) (hy : F.eval (fun i => (x i : ℚ)) = y) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) F.numerator /
      (F.denominator : ℝ) = y := by
  have he : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.numerator : ℝ) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) F.numerator := by
    simpa [Int.castRingHom] using
      (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℝ) F.numerator)
  have hint := F.integer_value_cleared x y hy
  have hr := congrArg (fun z : ℤ => (z : ℝ)) hint
  rw [he, Int.cast_mul] at hr
  rw [hr]
  have hd : (F.denominator : ℝ) ≠ 0 := Int.cast_ne_zero.mpr F.denominator_ne_zero
  exact mul_div_cancel_left₀ (y : ℝ) hd

theorem reconstructed_integer_coprimality {σ : Type*} (steps : List (HistoryPivotStep σ))
    (x : σ → ℤ) (hx : ValidIntegerReconstruction steps x) (i : σ)
    (p : ℕ) (hp : p.Prime)
    (hden : ¬p ∣ (integerReconstructionFormulas steps i).cleared.denominator.natAbs) :
    p.Coprime (reconstructIntegers steps x i).natAbs ↔
      ¬p ∣ (MvPolynomial.eval₂Hom (RingHom.id ℤ) x
        (integerReconstructionFormulas steps i).cleared.numerator).natAbs := by
  exact (integerReconstructionFormulas steps i).cleared.prime_coprime_integer_value x p hp hden
    (reconstructIntegers steps x i) (integerReconstructionFormulas_value steps x hx i)

theorem reconstructed_integer_real {σ : Type*} (steps : List (HistoryPivotStep σ))
    (x : σ → ℤ) (hx : ValidIntegerReconstruction steps x) (i : σ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun j => (x j : ℝ))
        (integerReconstructionFormulas steps i).cleared.numerator /
      ((integerReconstructionFormulas steps i).cleared.denominator : ℝ) =
      (reconstructIntegers steps x i : ℝ) :=
  (integerReconstructionFormulas steps i).cleared.real_value_of_integer x
    (reconstructIntegers steps x i) (integerReconstructionFormulas_value steps x hx i)

/-- Every retained pivot or product range is exactly a pair of polynomial
inequalities after fixing all but one of the original independent primes. -/
theorem reconstructed_integer_range {σ : Type*} (steps : List (HistoryPivotStep σ))
    (x : σ → ℤ) (i coord : σ) (lo hi : ℝ) (z : ℤ)
    (hx : ValidIntegerReconstruction steps (Function.update x coord z)) :
    clearedIntervalKeep (polynomialSupportCode
      (clearedIntervalPolynomials
        (specializeHistoryVariable (fun j => (x j : ℝ)) coord
          (integerReconstructionFormulas steps i).cleared.numerator)
        ((integerReconstructionFormulas steps i).cleared.denominator : ℝ) lo hi) z) = true ↔
      (reconstructIntegers steps (Function.update x coord z) i : ℝ) ∈ Set.Icc lo hi := by
  rw [specialized_cleared_interval_test _ _ coord _ lo hi z
    (Int.cast_ne_zero.mpr (integerReconstructionFormulas steps i).cleared.denominator_ne_zero)]
  have hupdate : Function.update (fun j => (x j : ℝ)) coord (z : ℝ) =
      (fun j => (Function.update x coord z j : ℝ)) := by
    funext j
    by_cases hj : j = coord
    · subst j; simp only [Function.update_self]
    · simp only [Function.update_of_ne hj]
  rw [hupdate, reconstructed_integer_real steps _ hx i]

end Ostmann

end OAI
