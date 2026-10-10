import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import OAI.NumberTheory.Ostmann.ZeroDensity.GammaRealLogDerivative
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterGammaRealBound

namespace OAI

/-! # The logarithmic Gamma bound needed in the full-height zero-free region

The positive-strip digamma series gives a concrete logarithmic bound.
-/

namespace Ostmann

open Complex

theorem gammaReal_logarithmic_bound : ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ,
    1 ≤ s.re → s.re ≤ 3 →
      ‖logDeriv Complex.Gammaℝ s‖ ≤ B * Real.log (|s.im| + 2) := by
  obtain ⟨C, hC, hb⟩ := Complex.exists_norm_digamma_div_two_le_log
    (a := 1) (b := 3) (by norm_num)
  let D := |Real.log Real.pi| / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C + D + 1, by positivity, ?_⟩
  intro s hs hs'
  have hregular : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hh := congrArg Complex.re hn
    simp only [div_ofNat_re, neg_re, natCast_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hlog : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hlogpos : 0 < Real.log (|s.im| + 2) := hlog2.trans_le hlog
  have hDlog : |Real.log Real.pi| ≤ D * Real.log (|s.im| + 2) := by
    have hm := mul_le_mul_of_nonneg_left hlog hD
    dsimp [D] at hm
    rwa [div_mul_cancel₀ _ hlog2.ne'] at hm
  have hpi : ‖Complex.log (Real.pi : ℂ)‖ = |Real.log Real.pi| := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs]
  rw [gammaReal_logDeriv s hregular, norm_div, norm_ofNat]
  have hh := (norm_sub_le (Complex.digamma (s / 2)) (Complex.log (Real.pi : ℂ))).trans
    (add_le_add (hb s hs hs') (le_refl _))
  rw [hpi] at hh
  change ‖Complex.digamma (s / 2) - Complex.log (Real.pi : ℂ)‖ / 2 ≤ _
  nlinarith

theorem characterGamma_logarithmic_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 →
      ‖logDeriv (DirichletCharacter.gammaFactor χ.character) s‖ ≤
        B * Real.log (|s.im| + 2) := by
  obtain ⟨B, hB, hb⟩ := gammaReal_logarithmic_bound
  refine ⟨B, hB, ?_⟩
  intro χ s hs hs'
  by_cases he : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    exact hb s hs.le (by linarith)
  · rw [show DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := s)
      (gammaReal_analyticAt_pos (s + 1) (by simp; linarith)).differentiableAt
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa using hb (s + 1) (by simp; linarith) (by simp; linarith)

end Ostmann

end OAI
