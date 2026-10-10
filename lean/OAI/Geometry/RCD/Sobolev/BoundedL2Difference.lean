import OAI.Geometry.RCD.Sobolev.LipschitzL2PointControl

namespace OAI

/-! # L² distance controlled by L¹ distance for uniformly bounded rows -/

open Filter MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem bounded_L2_norm_sub_sq_le_L1 (f g : Lp ℝ 2 μ)
    (hfi : Integrable f μ) (hgi : Integrable g μ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) (hg : ∀ᵐ x ∂μ, |g x| ≤ C) :
    ‖f - g‖ ^ 2 ≤ 2 * C * ∫ x, |f x - g x| ∂μ := by
  have he : (f - g : Lp ℝ 2 μ) =ᵐ[μ] fun x => f x - g x := Lp.coeFn_sub f g
  have hi : Integrable (fun x => (f x - g x)^2) μ :=
    (Lp.memLp (f - g)).integrable_sq.congr (he.fun_comp fun a : ℝ => a^2)
  calc
    _ = ∫ x, (f x - g x)^2 ∂μ := by
      rw [← integral_sq_Lp μ (f - g)]
      exact integral_congr_ae (he.fun_comp fun a : ℝ => a^2)
    _ ≤ ∫ x, (2 * (C : ℝ)) * |f x - g x| ∂μ := by
      apply integral_mono_ae hi ((hfi.sub hgi).abs.const_mul (2 * C))
      filter_upwards [hf, hg] with x hx hy
      change (f x - g x)^2 ≤ 2 * (C : ℝ) * |f x - g x|
      have h := (abs_sub (f x) (g x)).trans (add_le_add hx hy)
      nlinarith [sq_abs (f x - g x), abs_nonneg (f x - g x)]
    _ = _ := integral_const_mul _ _

end RegularPointCoordinates

end

end OAI
