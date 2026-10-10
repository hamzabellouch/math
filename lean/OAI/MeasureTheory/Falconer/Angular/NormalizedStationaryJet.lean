import OAI.MeasureTheory.Falconer.Angular.StationaryDifferentialExpr
import OAI.MeasureTheory.Falconer.Angular.AngularDifferentialBounds

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def normalizedStationaryJet (j : ℕ) (f : ℝ → ℂ) (θ Λ : ℝ) : ℂ :=
  ((Λ⁻¹:ℝ):ℂ)^j * directStationaryOperator j f θ

theorem directStationaryOperator_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (j : ℕ) (θ : ℝ)
    (hb : ∀ k ≤ 2*j, ‖iteratedDeriv k f θ‖ ≤ C*D^k) :
    ‖directStationaryOperator j f θ‖ ≤ (directStationaryExpr j).cost*C*D^(2*j) := by
  have hh := (directStationaryExpr j).derivative_bound_of_order_le (directStationaryExpr_order j)
    hf hC hD 0 θ (by simpa only [zero_add] using hb)
  simpa only [iteratedDeriv_zero,zero_add,directStationaryExpr_apply,mul_assoc] using hh

theorem normalizedStationaryJet_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D Λ : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hΛ : 0 < Λ) (hscale : D^2 ≤ Λ)
    (j : ℕ) (θ : ℝ) (hb : ∀ k ≤ 2*j, ‖iteratedDeriv k f θ‖ ≤ C*D^k) :
    ‖normalizedStationaryJet j f θ Λ‖ ≤ (directStationaryExpr j).cost*C := by
  have hp : (D^2/Λ)^j ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hΛ).mpr hscale)
  have hcost := (directStationaryExpr j).cost_nonneg
  calc
    _ = (Λ⁻¹)^j*‖directStationaryOperator j f θ‖ := by
      simp only [normalizedStationaryJet,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hΛ)]
    _ ≤ (Λ⁻¹)^j*((directStationaryExpr j).cost*C*D^(2*j)) :=
      mul_le_mul_of_nonneg_left (directStationaryOperator_bound hf hC hD j θ hb) (by positivity)
    _ = ((directStationaryExpr j).cost*C)*(D^2/Λ)^j := by
      rw [div_pow,pow_mul]
      ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hp (mul_nonneg hcost hC)

end PlanarFalconer

end OAI
