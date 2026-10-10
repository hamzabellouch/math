import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalEvents
import OAI.Analysis.IrrationalRotation.Product.ProductCircleConditioning

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Invariant233.OrderedProductCoupling

theorem circle_right_thresholds_iCondIndepSet (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet (MeasurableSpace.comap circleLeftEndpoint inferInstance)
      circleLeftEndpoint_measurable.comap_le
      (fun i => {ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i}) (law P) :=
  (right_threshold_iCondIndepSet_iff_circle P u).mp
    (right_thresholds_iCondIndepSet P u)

theorem circle_left_thresholds_iCondIndepSet (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet (MeasurableSpace.comap circleRightEndpoint inferInstance)
      circleRightEndpoint_measurable.comap_le
      (fun i => {ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i}) (law P) :=
  (left_threshold_iCondIndepSet_iff_circle P u).mp
    (left_thresholds_iCondIndepSet P u)

theorem circle_right_threshold_condExp_lower (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u i → u i ≤ 1 - w →
      realEndpoint (circleLeftEndpoint ω) i < u i →
      CouplingMarginalBounds.rho (P.κ i) (P.m i) w / 10 ≤
        ((law P)[{ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i}.indicator
          (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap circleLeftEndpoint inferInstance]) ω := by
  have heq := ae_all_iff.mpr (right_threshold_condExp_eq_circle P u)
  filter_upwards [right_threshold_condExp_lower P u, ae_real_circle_endpoints P, heq]
    with ω hω hrep hce i w hw hwu huw hxu
  rw [← hce i]
  apply hω i w hw hwu huw
  simpa only [hrep.1] using hxu

theorem circle_left_threshold_condExp_lower (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u i → u i ≤ 1 - w →
      u i ≤ realEndpoint (circleRightEndpoint ω) i →
      CouplingMarginalBounds.rho (P.κ i) (P.m i) w / 10 ≤
        ((law P)[{ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i}.indicator
          (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap circleRightEndpoint inferInstance]) ω := by
  have heq := ae_all_iff.mpr (left_threshold_condExp_eq_circle P u)
  filter_upwards [left_threshold_condExp_lower P u, ae_real_circle_endpoints P, heq]
    with ω hω hrep hce i w hw hwu huw huy
  rw [← hce i]
  apply hω i w hw hwu huw
  simpa only [hrep.2] using huy

theorem circle_threshold_condExp_lower_countable {T : Type*} [Countable T]
    (P : Parameters) (u : T → ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (t : T) (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u t i → u t i ≤ 1 - w →
      (realEndpoint (circleLeftEndpoint ω) i < u t i →
        CouplingMarginalBounds.rho (P.κ i) (P.m i) w / 10 ≤
          ((law P)[{ω : Sample | u t i ≤ realEndpoint (circleRightEndpoint ω) i}.indicator
            (fun _ => (1 : ℝ)) |
            MeasurableSpace.comap circleLeftEndpoint inferInstance]) ω) ∧
      (u t i ≤ realEndpoint (circleRightEndpoint ω) i →
        CouplingMarginalBounds.rho (P.κ i) (P.m i) w / 10 ≤
          ((law P)[{ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u t i}.indicator
            (fun _ => (1 : ℝ)) |
            MeasurableSpace.comap circleRightEndpoint inferInstance]) ω) := by
  have hleft := ae_all_iff.mpr (fun t => circle_right_threshold_condExp_lower P (u t))
  have hright := ae_all_iff.mpr (fun t => circle_left_threshold_condExp_lower P (u t))
  filter_upwards [hleft, hright] with ω hx hy t i w hw hwu huw
  exact ⟨hx t i w hw hwu huw, hy t i w hw hwu huw⟩

end Invariant233.OrderedProductCoupling

end

end OAI
