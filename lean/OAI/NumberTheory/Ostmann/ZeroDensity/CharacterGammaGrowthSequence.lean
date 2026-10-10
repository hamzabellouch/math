import OAI.NumberTheory.Ostmann.ZeroDensity.GammaLogDerivativeGrowth
import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedRightGrowth

namespace OAI

/-! # An explicit sequence on which the character Gamma logarithmic derivative diverges -/

namespace Ostmann

open Complex Filter
open scoped Topology Classical

noncomputable def characterGammaSample (χ : PrimitiveComplexCharacter) (n : ℕ) : ℂ :=
  if χ.character.Even then 2 * ((n : ℂ) + 1) else 2 * (n : ℂ) + 1

theorem characterGammaSample_re_lower (χ : PrimitiveComplexCharacter) (n : ℕ) :
    2 * (n : ℝ) + 1 ≤ (characterGammaSample χ n).re := by
  unfold characterGammaSample
  split_ifs <;> simp
  linarith

theorem gammaReal_logDeriv_double_nat (n : ℕ) :
    logDeriv Complex.Gammaℝ (2 * ((n : ℂ) + 1)) =
      ((-Real.eulerMascheroniConstant + (harmonic n : ℝ) - Real.log Real.pi) / 2 : ℝ) := by
  have harg : 2 * ((n : ℂ) + 1) / 2 = (n : ℂ) + 1 := by ring
  have hn : ∀ k : ℕ, (n : ℂ) + 1 ≠ -(k : ℂ) := by
    intro k hk
    have hh := congrArg Complex.re hk
    simp only [add_re, natCast_re, one_re, neg_re] at hh
    have := Nat.cast_nonneg (α := ℝ) n
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [gammaReal_logDeriv _ (by rwa [harg]), harg, Complex.digamma_def,
    gamma_logDeriv_nat, ← Complex.ofReal_log Real.pi_pos.le]
  push_cast
  rfl

theorem characterGamma_logDeriv_sample (χ : PrimitiveComplexCharacter) (n : ℕ) :
    logDeriv (DirichletCharacter.gammaFactor χ.character) (characterGammaSample χ n) =
      ((-Real.eulerMascheroniConstant + (harmonic n : ℝ) - Real.log Real.pi) / 2 : ℝ) := by
  by_cases hc : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    simpa [characterGammaSample, hc] using gammaReal_logDeriv_double_nat n
  · have he : DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) := by
      funext u
      simp [DirichletCharacter.gammaFactor, hc]
    rw [he]
    simp only [characterGammaSample, hc, ↓reduceIte]
    have ha : 2 * (n : ℂ) + 1 + 1 = 2 * ((n : ℂ) + 1) := by ring
    have hreg : ∀ k : ℕ, (2 * (n : ℂ) + 1 + 1) / 2 ≠ -(k : ℂ) := by
      intro k hk
      have hh := congrArg Complex.re hk
      norm_num at hh
      have := Nat.cast_nonneg (α := ℝ) n
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := 2 * (n : ℂ) + 1)
      (gammaReal_differentiableAt _ hreg)
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa only [deriv_add_const, deriv_id'', mul_one, ha] using gammaReal_logDeriv_double_nat n

theorem characterGamma_logDeriv_sample_re_tendsto (χ : PrimitiveComplexCharacter) :
    Tendsto (fun n => (logDeriv (DirichletCharacter.gammaFactor χ.character)
      (characterGammaSample χ n)).re) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hh := gamma_logDeriv_nat_re_tendsto.eventually_ge_atTop (2 * b + Real.log Real.pi)
  filter_upwards [hh] with n hn
  rw [characterGamma_logDeriv_sample]
  rw [gamma_logDeriv_nat] at hn
  simp only [add_re, neg_re, ofReal_re] at hn ⊢
  linarith

end Ostmann

end OAI
