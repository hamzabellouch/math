import OAI.Geometry.RCD.Sobolev.ContinuousPathMean

namespace OAI

/-! # Normalized means retain the local coordinate Lipschitz bound -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem normalized_path_mean_lipschitz
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (U : X → ℝ) (hU : ∀ t : Time, Integrable (fun γ => U (γ t)) π)
    {S : Set X} {L D : ℝ≥0} (hLip : LipschitzOnWith L U S)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) (hstay : ∀ᵐ γ ∂π, ∀ t : Time, γ t∈S)
    {r : ℝ} (hr : 0 < r) (hlen : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ (D:ℝ)*r) :
    LipschitzWith (L*D) (fun t : Time => (∫ γ, U (γ t) ∂π)/r) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hb : ∀ᵐ γ ∂π, ‖U (γ s)-U (γ t)‖ ≤ ((L:ℝ)*(D:ℝ)*dist s t)*r := by
    filter_upwards [hgeo,hstay,hlen] with γ hg hs hl
    rw [Real.norm_eq_abs]
    calc
      _ ≤ (L:ℝ)*dist (γ s) (γ t) := by
        simpa only [Real.dist_eq] using hLip.dist_le_mul (γ s) (hs s) (γ t) (hs t)
      _ = (L:ℝ)*(dist s t*dist (γ 0) (γ 1)) := by
        rw [hg s t]
        rfl
      _ ≤ (L:ℝ)*(dist s t*((D:ℝ)*r)) := by gcongr
      _ = _ := by ring
  have hi := norm_integral_le_of_norm_le_const hb
  rw [integral_sub (hU s) (hU t),probReal_univ,mul_one,Real.norm_eq_abs] at hi
  rw [Real.dist_eq,← sub_div,abs_div,abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  exact hi

end RegularPointCoordinates

end

end OAI
