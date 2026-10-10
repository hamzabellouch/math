import OAI.NumberTheory.CubicMoment.Estimates.ScaledPrimeInput

namespace OAI

/-! Uniform rescaled prime sums for the given logarithmic weight family.
Every variation cost is derived from the family's actual derivative bounds. -/
noncomputable section
open Set
namespace CubicFirstMoment

theorem logarithmic_scaled_cubic_prime_bound {γ : Type*}
    (hSW : CubicPrimeSiegelWalfisz) {L : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily L W) (hlo : ∀ r x, x < 1 → W r x = 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ (C X₀ M B : ℝ) (m b : ℕ), 0 < C ∧ 1 < X₀ ∧ 0 ≤ M ∧ 0 ≤ B ∧
      ∀ (r : γ) (Y R : ℝ), X₀ ≤ Y → 1 ≤ R →
      ∀ q₁ q₂ : Eisenstein, primary q₁ → primary q₂ → Squarefree q₁ → Squarefree q₂ →
      IsCoprime q₁ q₂ → MixedCubicNonprincipal q₁ q₂ →
      norm (q₁*q₂) ≤ (Real.log Y)^A → ∀ u : ℝ,
      ‖smoothPrimeCharacterSum R Y (W r) (mixedCubic q₁ q₂) u‖ ≤
        (C*(R*Y)/(Real.log Y)^D)*
          (2*M*(1+Real.log (L r))^m+(R-1)*
            (B*(1+Real.log (L r))^b+M*(1+Real.log (L r))^m*|u|)) := by
  obtain ⟨C,X₀,hC,hX₀,hbound⟩ := scaled_cubic_prime_bound hSW hA hD
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  obtain ⟨B,b,hB,hBb⟩ := hW.radial_deriv_bound
  refine ⟨C,X₀,M,B,m,b,hC,hX₀,hM,hB,?_⟩
  intro r Y R hY hR q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hnon hcon u
  have hn : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg (hW.length_one r)]
  have hh := hbound Y R (M*(1+Real.log (L r))^m) (B*(1+Real.log (L r))^b)
    (W r) hY hR (mul_nonneg hM (pow_nonneg hn _)) (mul_nonneg hB (pow_nonneg hn _))
    (hW.smooth r) (hlo r) (hMb r) (hBb r) q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hnon hcon u
  convert hh using 1; ring

end CubicFirstMoment

end

end OAI
