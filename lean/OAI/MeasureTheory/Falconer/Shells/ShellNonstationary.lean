import OAI.MeasureTheory.Falconer.Angular.AngularPair
import OAI.MeasureTheory.Falconer.Graphs.ParentRetainedEnergy

namespace OAI

/-!
# Integrating angular nonstationarity over the actual radial shell

The frequency lower bound follows from the support of the fixed cutoff.
No frequency assumption is added to the endpoint symbols.
-/

namespace Falconer
open Set MeasureTheory

theorem shell_ae_radius_lower (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) :
    ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ, (2 : ℝ)^v/4 < r := by
  filter_upwards [PlanarFalconer.sourceAngularShellMeasure_ae_nonzero v Ψ hΨ] with r hr
  have hh := (hs _ hr).1
  have hp : 0 < (2 : ℝ)^v := Real.rpow_pos_of_pos (by norm_num) _
  have h := (lt_div_iff₀ hp).mp hh
  linarith

theorem shell_nonstationary_integral_bound (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (F : ℝ → ℂ) (m : ℕ) {C D τ : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hτ : 0 < τ)
    (hF : ∀ r, (2 : ℝ)^v/4 < r → ‖F r‖ ≤ C*(D/(r*τ))^m) :
    ‖∫ r, F r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ‖ ≤
      (C*(4*D/((2 : ℝ)^v*τ))^m)*(4*W) := by
  have hu : ∀ t, 4 < t → Ψ t = 0 := by
    intro t ht
    by_contra hn
    exact (not_lt_of_ge (hs t hn).2.le) ht
  let := PlanarFalconer.sourceAngularShellMeasure_finite v Ψ hW hw hu
  have hp : 0 < (2 : ℝ)^v := Real.rpow_pos_of_pos (by norm_num) _
  have hbound : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖F r‖ ≤ C*(4*D/((2 : ℝ)^v*τ))^m := by
    filter_upwards [shell_ae_radius_lower v Ψ hΨ hs] with r hr
    have hr0 : 0 < r := lt_trans (by positivity) hr
    apply (hF r hr).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_div_of_nonneg_left hD
      (mul_pos (div_pos hp (by norm_num)) hτ)
      (mul_le_mul_of_nonneg_right hr.le hτ.le)).trans_eq
    field_simp
  apply (norm_integral_le_of_norm_le_const hbound).trans
  apply mul_le_mul_of_nonneg_left
    (PlanarFalconer.sourceAngularShellMeasure_real_mass_le v Ψ hW hw hu)
    (by positivity)

end Falconer

end OAI
