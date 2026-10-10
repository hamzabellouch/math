import OAI.Geometry.RCD.Metric.SupportedL2Continuity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Identifying a Bochner integral with its pointwise representative

Testing against L2 functions and Fubini identifies the actual integral.
The explicit product integrability condition is supplied by compact
support and the uniform bound in the heat application.
-/

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem L2_integral_representative
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (u : Y → Lp ℝ 2 μ) (hu : Integrable u ν) (f : Y → X → ℝ)
    (hr : ∀ᵐ y ∂ν, u y =ᵐ[μ] f y)
    (hf : ∀ ξ : Lp ℝ 2 μ, Integrable (fun q : Y × X => ξ q.2*f q.1 q.2) (ν.prod μ))
    (g : X → ℝ) (hg : MemLp g 2 μ)
    (hgi : g =ᵐ[μ] fun x => ∫ y, f y x ∂ν) :
    (∫ y, u y ∂ν) =ᵐ[μ] g := by
  have he : (∫ y, u y ∂ν) = hg.toLp g := by
    apply ext_inner_left ℝ
    intro ξ
    have hl : inner ℝ ξ (∫ y, u y ∂ν) =
        ∫ y, ∫ x, ξ x*f y x ∂μ ∂ν := by
      change (innerSL ℝ ξ) (∫ y, u y ∂ν) = _
      rw [← (innerSL ℝ ξ).integral_comp_comm hu]
      apply integral_congr_ae
      filter_upwards [hr] with y hy
      change inner ℝ ξ (u y) = _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hy] with x hx
      simp only [Real.inner_apply,hx]
    rw [hl,integral_integral_swap (hf ξ),L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hgi,hg.coeFn_toLp] with x hx hgx
    rw [integral_const_mul]
    simp only [Real.inner_apply,hgx,hx]
  rw [he]
  exact hg.coeFn_toLp

end RegularPointCoordinates

end

end OAI
