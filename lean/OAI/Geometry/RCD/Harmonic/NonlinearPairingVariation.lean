import OAI.Geometry.RCD.Sobolev.WeightedIntegralPotential

namespace OAI

/-! # Varying L² pairings with a nonlinear scalar factor

Only the original L² paths are differentiated. A bounded frozen weight
and the scalar Taylor remainder justify the nonlinear term.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem inner_compLp_eq_weightedPotential (w f : Lp ℝ 2 μ) (θ : Lp ℝ ∞ μ)
    (hθ : θ =ᵐ[μ] w) {Φ : ℝ → ℝ} {L : ℝ≥0} (hΦ : LipschitzWith L Φ) (hΦ0 : Φ 0=0) :
    inner ℝ w (hΦ.compLp hΦ0 f) = weightedIntegralPotential μ θ Φ f := by
  rw [L2.inner_def]
  unfold weightedIntegralPotential
  apply integral_congr_ae
  filter_upwards [hθ,hΦ.coeFn_compLp hΦ0 f] with x hx hfx
  simp only [Real.inner_apply,hfx,Function.comp_apply,hx]

theorem nonlinear_pairing_hasDerivAt {F W : ℝ → Lp ℝ 2 μ} {F' W' : Lp ℝ 2 μ} {t : ℝ}
    (hF : HasDerivAt F F' t) (hW : HasDerivAt W W' t)
    (θ : Lp ℝ ∞ μ) (B : ℝ≥0) (hB : ∀ᵐ x ∂μ, |θ x| ≤ B) (hθ : θ =ᵐ[μ] W t)
    {Φ φ : ℝ → ℝ} {L C : ℝ≥0} (hΦ : LipschitzWith L Φ) (hΦ0 : Φ 0=0)
    (hd : ∀ a, HasDerivAt Φ (φ a) a) (hφ : LipschitzWith C φ) (hφ0 : φ 0=0) :
    HasDerivAt (fun s => inner ℝ (W s) (hΦ.compLp hΦ0 (F s)))
      (inner ℝ W' (hΦ.compLp hΦ0 (F t)) +
        inner ℝ F' (lpMultiplier μ θ (hφ.compLp hφ0 (F t)))) t := by
  have hfixed := (weightedIntegralPotential_hasFDerivAt μ θ B hB hd hΦ0 hφ hφ0 (F t)).comp_hasDerivAt t hF
  simp only [innerSL_apply_apply] at hfixed
  rw [real_inner_comm] at hfixed
  have he : (fun s => inner ℝ (W t) (hΦ.compLp hΦ0 (F s))) =
      (fun s => weightedIntegralPotential μ θ Φ (F s)) := by
    funext s
    exact inner_compLp_eq_weightedPotential μ (W t) (F s) θ hθ hΦ hΦ0
  apply hasDerivAt_inner_of_frozen hW
    ((hΦ.continuous_compLp hΦ0).continuousAt.comp hF.continuousAt)
  change HasDerivAt (fun s => inner ℝ (W t) (hΦ.compLp hΦ0 (F s))) _ t
  rw [he]
  exact hfixed

end RegularPointCoordinates

end

end OAI
