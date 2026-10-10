import Mathlib.NumberTheory.DirichletCharacter.Bounds
import OAI.NumberTheory.SiegelZeros.Characters.PrimeTerms
import OAI.NumberTheory.SiegelZeros.EntireFunctions.AnalyticBridge

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W05

theorem eulerTerm_ofReal_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (c : ℕ → ℝ) (hc : ∀ n : ℕ, χ n = (c n : ℂ)) (s : ℝ) (n : ℕ) :
    (eulerTerm c s n : ℂ) =
      LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) +
        χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) n := by
  rw [LSeries.term_def₀ (by simp)]
  simp only [eulerTerm, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg n),
    Complex.ofReal_natCast, Complex.ofReal_neg, hc n]
  ring

theorem real_eulerTerm_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (c : ℕ → ℝ) (hc : ∀ n : ℕ, χ n = (c n : ℂ)) {s : ℝ} (hs : 1 < s) :
    Summable (eulerTerm c s) := by
  apply Complex.summable_ofReal.mp
  have h := combined_mangoldt_summable χ (s := (s : ℂ)) (by simpa using hs)
  exact Summable.congr h (fun n : ℕ => (eulerTerm_ofReal_eq χ c hc s n).symm)

theorem actual_character_prime_restriction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, χ n = (c n : ℂ)) {X : ℝ} (hX : 1 < X)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ X ∧ c p = 1) :
    2 * Real.exp (-1) * (∑ p ∈ P, Real.log p / p) ≤
      ∑' n, eulerTerm c (1 + 1 / Real.log X) n := by
  apply infinite_prime_restriction hX P hP
  · intro n
    have hnorm := χ.norm_le_one (n : ZMod q)
    rw [hc n, Complex.norm_real, Real.norm_eq_abs] at hnorm
    exact (abs_le.mp hnorm).1
  · apply real_eulerTerm_summable χ c hc
    exact lt_add_of_pos_right 1 (one_div_pos.mpr (Real.log_pos hX))

theorem real_eulerSum_eq_logDerivatives {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (c : ℕ → ℝ) (hc : ∀ n : ℕ, χ n = (c n : ℂ)) {s : ℝ} (hs : 1 < s) :
    (∑' n, eulerTerm c s n) =
      (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) +
        -deriv χ.LFunction (s : ℂ) / χ.LFunction (s : ℂ)).re := by
  have heq : Complex.ofReal (∑' n, eulerTerm c s n) =
      -deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) +
        -deriv χ.LFunction (s : ℂ) / χ.LFunction (s : ℂ) := by
    calc
      _ = ∑' n, (eulerTerm c s n : ℂ) := Complex.ofReal_tsum _
      _ = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) +
          χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) :=
        tsum_congr (fun n : ℕ => eulerTerm_ofReal_eq χ c hc s n)
      _ = _ := combined_mangoldt_eq_logDerivatives χ (by simpa using hs)
  exact congrArg Complex.re heq

theorem prime_mass_le_logDerivatives {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, χ n = (c n : ℂ)) {X : ℝ} (hX : 1 < X)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ X ∧ c p = 1) :
    2 * Real.exp (-1) * (∑ p ∈ P, Real.log p / p) ≤
      (-deriv riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) /
        riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) +
        -deriv χ.LFunction ((1 + 1 / Real.log X : ℝ) : ℂ) /
        χ.LFunction ((1 + 1 / Real.log X : ℝ) : ℂ)).re := by
  rw [← real_eulerSum_eq_logDerivatives χ c hc
    (lt_add_of_pos_right 1 (one_div_pos.mpr (Real.log_pos hX)))]
  exact actual_character_prime_restriction χ c hc hX P hP

theorem real_character_prime_mass_le_logDerivatives {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {X : ℝ} (hX : 1 < X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ X ∧ χ p = 1) :
    2 * Real.exp (-1) * (∑ p ∈ P, Real.log p / p) ≤
      (-deriv riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) /
        riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) +
        -deriv χ.LFunction ((1 + 1 / Real.log X : ℝ) : ℂ) /
        χ.LFunction ((1 + 1 / Real.log X : ℝ) : ℂ)).re := by
  have hc : ∀ n : ℕ, χ n = ((χ n).re : ℂ) := by
    intro n
    apply Complex.ext
    · rfl
    · simpa using hreal (n : ZMod q)
  apply prime_mass_le_logDerivatives χ (fun n : ℕ => (χ n).re) hc hX P
  intro p hp
  obtain ⟨hpp, hpX, hpχ⟩ := hP p hp
  exact ⟨hpp, hpX, by simp [hpχ]⟩

end WeightedTorusJets.W05

end

end SiegelZeros

end OAI
