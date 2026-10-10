import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterGammaGrowthSequence
import OAI.NumberTheory.Ostmann.Characters.CharacterRightLogDerivativeBound

namespace OAI

/-! # Growth of the completed logarithmic derivative on the positive real axis -/

namespace Ostmann

open Complex Filter Set
open scoped Topology Classical

theorem PrimitiveComplexCharacter.gammaFactor_differentiableAt_pos
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ.character) s := by
  have hreg (z : ℂ) (hz : 0 < z.re) : ∀ k : ℕ, z / 2 ≠ -(k : ℂ) := by
    intro k hk
    have hh := congrArg Complex.re hk
    simp only [div_ofNat_re, neg_re, natCast_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) k]
  by_cases hc : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    exact gammaReal_differentiableAt s (hreg s hs)
  · rw [show DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    exact (gammaReal_differentiableAt (s + 1)
      (hreg _ (by simpa using (show 0 < s.re + 1 by linarith)))).comp
      (f := fun u : ℂ => u + 1) s (differentiableAt_id.add_const (1 : ℂ))

theorem PrimitiveComplexCharacter.completed_logDeriv_eq_add
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 1 ≤ s.re) :
    logDeriv χ.completed s = logDeriv χ.L s +
      logDeriv (DirichletCharacter.gammaFactor χ.character) s := by
  have hspos : 0 < s.re := by linarith
  have hne : DirichletCharacter.gammaFactor χ.character s ≠ 0 := by
    have hh := χ.gammaInverse_ne_zero s hspos
    intro hz
    apply hh
    simp [PrimitiveComplexCharacter.gammaInverse, hz]
  have he : χ.completed =ᶠ[𝓝 s] (fun z => χ.L z * DirichletCharacter.gammaFactor χ.character z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hspos] with z hz
    exact χ.completed_eq_L_mul_gamma z hz
  rw [(logDeriv_congr_nhds he).self_of_nhds]
  exact logDeriv_fun_mul s (χ.L_ne_zero_one_le_re s hs) hne
    (χ.L_analytic s).differentiableAt (χ.gammaFactor_differentiableAt_pos s hspos)

/-- The Gamma term dominates the uniformly bounded absolutely convergent L-series term. -/
theorem completed_logDeriv_sample_re_tendsto (χ : PrimitiveComplexCharacter) :
    Tendsto (fun n => (logDeriv χ.completed (characterGammaSample χ n)).re) atTop atTop := by
  obtain ⟨C, hC, hbound⟩ := character_logDeriv_right_uniform_bound
  apply tendsto_atTop.2
  intro b
  have hh := (characterGamma_logDeriv_sample_re_tendsto χ).eventually_ge_atTop (b + C)
  filter_upwards [hh, eventually_ge_atTop 1] with n hn hn1
  have hs2 : 2 ≤ (characterGammaSample χ n).re := by
    have hb := characterGammaSample_re_lower χ n
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hb := hbound χ (characterGammaSample χ n) hs2
  have hr := (neg_le_abs ((logDeriv χ.L (characterGammaSample χ n)).re)).trans
    (abs_re_le_norm (logDeriv χ.L (characterGammaSample χ n)))
  rw [χ.completed_logDeriv_eq_add _ (by linarith), add_re]
  linarith

end Ostmann

end OAI
