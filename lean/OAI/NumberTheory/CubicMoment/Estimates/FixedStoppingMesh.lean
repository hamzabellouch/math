import OAI.NumberTheory.CubicMoment.Decomposition.StoppingLogBoundary

namespace OAI

/-! A fixed geometric mesh meets the inverse logarithmic width condition
of the stopped analytic estimate for all sufficiently large parameters. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_fixed_stopping_mesh {ρ : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) :
    ∀ᶠ X : ℝ in atTop,
      0 < ρ-1 ∧ ρ-1 ≤ 1 ∧ (Real.log X)^(-(1:ℝ)) ≤ ρ-1 := by
  have hδ : 0 < ρ-1 := by linarith
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1/(ρ-1)),
    eventually_gt_atTop (1:ℝ)] with X hbound hX
  refine ⟨hδ,by linarith,?_⟩
  have hlog : 0 < Real.log X := Real.log_pos hX
  rw [Real.rpow_neg_one]
  rw [←one_div]
  apply (div_le_iff₀ hlog).mpr
  have he := (div_le_iff₀ hδ).mp hbound
  nlinarith

end CubicFirstMoment

end

end OAI
