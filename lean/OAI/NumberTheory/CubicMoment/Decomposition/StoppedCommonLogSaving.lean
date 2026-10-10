import OAI.NumberTheory.CubicMoment.Decomposition.StoppedVarianceRemainder
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonLogScale
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonGeometry

namespace OAI

/-! The three proved common-factor costs give every logarithmic saving
for polynomial coefficient length and the actual logarithmic roughness cutoff. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem bounded_rough_divisor_common_log_saving (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve) {κ : ℝ} (hκ : 0 < κ)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ (K : ℝ) (j : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ) (b A M u R : ℝ)
        (d : Eisenstein), X^κ ≤ b → b ≤ X → b^(3/2:ℝ) ≤ A →
      A ≤ b^2/(Real.log X)^(3*k) → 0 ≤ M →
      (Real.log X)^(6*(j+k)) ≤ R → primary d →
      norm d ≤ b^(1/1000:ℝ) → (norm d)^4 ≤ R →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ b/2 ≤ norm a ∧ norm a ≤ b) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      (∀ a ∈ S, β a ≠ 0 → ∀ p, primaryPrime p → p ∣ a → R ≤ norm p) →
      ‖divisorDispersionVariance d S β u V A-divisorCoprimeDispersionGram d S β u V A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)*M^2/(Real.log X)^k := by
  obtain ⟨K,j,hK,hbound⟩ := bounded_rough_divisor_variance_remainder hpnt hHuxley V hV hV'
  refine ⟨K*((2:ℝ)^j+2),j,by positivity,?_⟩
  filter_upwards [stopped_common_eventual_scales hκ k,
    eventually_ge_atTop (Real.exp 1)] with X hscales hX
  intro S β b A M u R d hbXlow hbX hAlo hAhi hM hR hd hdhi hdR hS hβ hrough
  obtain ⟨hb,hcut,hpow⟩ := hscales b hbXlow
  have hbp : 0 < b := by linarith
  have hL : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hRp : 0 < R := (pow_pos (zero_lt_one.trans_le hL) _).trans_le hR
  have hAp : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le hAlo
  have hbL : Real.log b ≤ Real.log X := Real.log_le_log hbp hbX
  have hbnd := hbound S β b A M u R d hb hAlo hM hRp hd hdhi hdR hcut hS hβ hrough
  exact hbnd.trans (stopped_common_error_scale hAp (by linarith) hL hK.le hbL j k hR hpow hAhi)

end CubicFirstMoment

end

end OAI
