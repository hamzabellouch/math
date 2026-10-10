import OAI.NumberTheory.CubicMoment.Estimates.TypeILowIntegral
import OAI.NumberTheory.CubicMoment.Estimates.LogPowerSaving

namespace OAI

/-! The complete central Type-I integral is negligible on the first-moment
scale. All arithmetic support conditions refer to the actual selected sums. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem typeI_low_integral_isLittleO
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k Ct : ℕ)
    (w : ℝ → Eisenstein → γ) (S : ℝ → Finset Eisenstein)
    (α : ℝ → Eisenstein → ℂ) (R U H X₀ : ℝ → ℝ)
    (hsetup : ∀ᶠ X : ℝ in atTop,
      2 ≤ X ∧ 1 ≤ Real.log X ∧ B ≤ X ∧ 1 ≤ R X ∧ 1 ≤ U X ∧ R X*U X = X ∧
      R X ≤ X^(51/100:ℝ) ∧
      (∀ r ∈ S X, primary r ∧ R X ≤ norm r ∧ norm r ≤ 2*R X) ∧
      (∀ r ∈ S X, Y (w X r) = X) ∧
      (∀ r ∈ S X, ∀ x : ℝ, B < x → W (w X r) x = 0) ∧
      (∀ r ∈ S X, ‖α X r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k)) :
    (fun X : ℝ => lowTypeIIntegral (w X) (S X) (α X) W ℓ (U X) (H X)
      ((1+Real.log X)^Ct) (X₀ X)) =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := typeI_low_integral_bound hV hW ℓ hGamma hB hA k Ct
  have hb : (fun X : ℝ => lowTypeIIntegral (w X) (S X) (α X) W ℓ (U X) (H X)
      ((1+Real.log X)^Ct) (X₀ X)) =O[atTop]
      (fun X : ℝ => (1+Real.log X)^Ct*X^(5/6-1/100:ℝ)) := by
    apply Asymptotics.IsBigO.of_bound K
    filter_upwards [hsetup] with X hX
    obtain ⟨hX,hlog,hBX,hR,hU,hRU,hRhi,hS,hY,hcut,hα⟩ := hX
    have he := hbound (w X) (S X) (α X) X (R X) (U X) (H X) (X₀ X)
      hX hlog hBX hR hU hRU hRhi hS hY hcut hα
    have hn : 0 ≤ (1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by
      have hL : 0 ≤ 1+Real.log X := by linarith
      positivity
    simpa only [Real.norm_of_nonneg hn,mul_assoc] using he
  exact hb.trans_isLittleO (log_power_powerSaving_isLittleO Ct (by norm_num))

end CubicFirstMoment

end

end OAI
