import OAI.NumberTheory.Ostmann.ZeroDensity.PrimeLogDerivative

namespace OAI

/-! # The real prime series for a real Dirichlet character -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

noncomputable def realPrimeTerm {q : ℕ} (χ : DirichletCharacter ℝ q) (s : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then χ n * Real.log n / (n : ℝ) ^ s else 0

theorem primeLogTerm_ofReal {q : ℕ} (χ : DirichletCharacter ℝ q) (s : ℝ) (n : ℕ) :
    LSeries.term (primeLogCoefficients (χ.ringHomComp Complex.ofRealHom)) (s : ℂ) n =
      (realPrimeTerm χ s n : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [realPrimeTerm]
  · rw [LSeries.term_of_ne_zero hn]
    by_cases hp : n.Prime
    · simp only [primeLogCoefficients, hp, ite_true, realPrimeTerm,
        MulChar.ringHomComp_apply,
        Complex.ofReal_div, Complex.ofReal_mul]
      change (χ n : ℂ) * (Real.log n : ℂ) / (n : ℂ) ^ (s : ℂ) = _
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    · simp [primeLogCoefficients, realPrimeTerm, hp]

/-- The uniform prime-power error is retained for the actual real weighted
prime sum. This result requires no analytic input beyond proved Mathlib. -/
theorem exists_realPrimeSeries_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℝ q) (s : ℝ), 1 < s →
      Summable (realPrimeTerm χ s) ∧
      |(∑' n, realPrimeTerm χ s n) +
        (deriv (DirichletCharacter.LFunction (χ.ringHomComp Complex.ofRealHom)) (s : ℂ) /
          DirichletCharacter.LFunction (χ.ringHomComp Complex.ofRealHom) (s : ℂ)).re| ≤ C := by
  obtain ⟨C, hC, herror⟩ := exists_primeLogDerivative_error
  refine ⟨C, hC, ?_⟩
  intro q hq χ s hs
  obtain ⟨hseries, hbound⟩ := herror q (χ.ringHomComp Complex.ofRealHom) s hs
  have hcast : Summable (fun n => (realPrimeTerm χ s n : ℂ)) :=
    hseries.congr (primeLogTerm_ofReal χ s)
  have hsum : LSeries (primeLogCoefficients (χ.ringHomComp Complex.ofRealHom)) (s : ℂ) =
      (((∑' n, realPrimeTerm χ s n) : ℝ) : ℂ) := by
    calc
      _ = ∑' n, (realPrimeTerm χ s n : ℂ) := tsum_congr (primeLogTerm_ofReal χ s)
      _ = _ := (Complex.ofReal_tsum _).symm
  refine ⟨Complex.summable_ofReal.mp hcast, ?_⟩
  rw [hsum] at hbound
  have hb := (Complex.abs_re_le_norm _).trans hbound
  simpa only [Complex.add_re, Complex.ofReal_re] using hb

end Ostmann

end OAI
