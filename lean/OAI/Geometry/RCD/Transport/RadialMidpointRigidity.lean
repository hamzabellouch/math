import OAI.Geometry.RCD.Transport.RadialGeodesic
import OAI.Geometry.RCD.Transport.DiracTransportCost

namespace OAI

/-! # Integral rigidity of a radial midpoint coupling

The quadratic triangle defect is nonnegative. The two marginal moments
and the optimal half-cost force its integral to vanish, so every path
of the replacement plan is still radial almost everywhere.
-/

open Set Filter Metric MeasureTheory

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem radial_midpoint_rigidity_of_moments
    (π : Measure C(Time, X)) (p : X)
    (hD : Integrable (fun γ : C(Time, X) => dist (γ 0) (γ 1) ^ 2) π)
    (h₀ : Integrable (fun γ : C(Time, X) => dist (γ 0) p ^ 2) π)
    (h₁ : Integrable (fun γ : C(Time, X) => dist (γ 1) p ^ 2) π)
    (hcost : (∫ γ, dist (γ 0) (γ 1) ^ 2 ∂π) ≤
      (∫ γ, dist (γ 0) p ^ 2 ∂π) / 4)
    (hhalf : (∫ γ, dist (γ 1) p ^ 2 ∂π) =
      (∫ γ, dist (γ 0) p ^ 2 ∂π) / 4) :
    ∀ᵐ γ ∂π, dist (γ 0) (γ 1) = dist (γ 1) p ∧
      dist (γ 0) p = dist (γ 0) (γ 1) + dist (γ 1) p := by
  let F (γ : C(Time, X)) :=
    2 * dist (γ 0) (γ 1) ^ 2 + 2 * dist (γ 1) p ^ 2 - dist (γ 0) p ^ 2
  have hi : Integrable F π := ((hD.const_mul 2).add (h₁.const_mul 2)).sub h₀
  have hn : ∀ᵐ γ ∂π, 0 ≤ F γ :=
    Eventually.of_forall fun γ => radial_midpoint_defect_nonneg p (γ 0) (γ 1)
  have hz : (∫ γ, F γ ∂π) = 0 := by
    apply le_antisymm _ (integral_nonneg_of_ae hn)
    rw [show (∫ γ, F γ ∂π) =
      2 * (∫ γ, dist (γ 0) (γ 1) ^ 2 ∂π) +
      2 * (∫ γ, dist (γ 1) p ^ 2 ∂π) -
        (∫ γ, dist (γ 0) p ^ 2 ∂π) by
      exact (integral_sub ((hD.const_mul 2).add (h₁.const_mul 2)) h₀).trans
        (by simp only [Pi.add_apply]
            rw [integral_add (hD.const_mul 2) (h₁.const_mul 2),
          integral_const_mul, integral_const_mul])]
    linarith
  have he := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
  filter_upwards [he] with γ hγ
  apply radial_midpoint_of_defect_zero
  exact hγ

end RegularPointCoordinates

end OAI
