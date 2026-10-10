import Mathlib

namespace OAI

/-! A derivative comparison obtained from pointwise increments. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

theorem norm_derivative_le_of_increment_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E} {g : ℝ → F} {f' : E} {g' : F} {x L : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (h : ∀ t, ‖f t-f x‖ ≤ L*‖g t-g x‖) : ‖f'‖ ≤ L*‖g'‖ := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope.norm (hg.tendsto_slope.norm.const_mul L)
  apply Eventually.of_forall
  intro t
  simp only [slope_def_module,norm_smul]
  calc
    ‖(t-x)⁻¹‖*‖f t-f x‖ ≤ ‖(t-x)⁻¹‖*(L*‖g t-g x‖) :=
      mul_le_mul_of_nonneg_left (h t) (norm_nonneg _)
    _ = L*(‖(t-x)⁻¹‖*‖g t-g x‖) := by ring

end InvariantIsing

end

end OAI
