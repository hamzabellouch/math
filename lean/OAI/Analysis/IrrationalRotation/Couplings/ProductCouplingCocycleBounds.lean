import OAI.Analysis.IrrationalRotation.Couplings.ProductCouplingCircle
import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalAttenuation

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.OrderedProductCoupling

theorem circleLeftEndpoint_map_absolutelyContinuous (P : Parameters)
    (hsum : Summable (energyBound P)) :
    (law P).map circleLeftEndpoint ≪ ProductModel.baseMeasure := by
  obtain ⟨g, _, _, _, _, hg⟩ :=
    exists_circle_hybrid_density P (fun _ => false) hsum le_rfl
  change (law P).map (circleHybridEndpoint (fun _ => false)) ≪ _
  rw [hg]
  exact withDensity_absolutelyContinuous _ _

theorem circleRightEndpoint_map_absolutelyContinuous (P : Parameters)
    (hsum : Summable (energyBound P)) :
    (law P).map circleRightEndpoint ≪ ProductModel.baseMeasure := by
  obtain ⟨g, _, _, _, _, hg⟩ :=
    exists_circle_hybrid_density P (fun _ => true) hsum le_rfl
  change (law P).map (circleHybridEndpoint (fun _ => true)) ≪ _
  rw [hg]
  exact withDensity_absolutelyContinuous _ _

theorem ae_all_int_cocycle_ratio_bounds (P : Parameters)
    (hsum : Summable (energyBound P))
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) :
    ∀ᵐ ω ∂law P, ∀ k : ℤ,
      0 < ProductCocycle.cocycleVersion θ c k (circleRightEndpoint ω) /
        ProductCocycle.cocycleVersion θ c k (circleLeftEndpoint ω) ∧
      ProductCocycle.cocycleVersion θ c k (circleRightEndpoint ω) /
        ProductCocycle.cocycleVersion θ c k (circleLeftEndpoint ω) ≤ 1 ∧
      ∀ i, (leftEndpoint ω i < 1 - Int.fract ((k : ℝ) * θ i) ∧
        1 - Int.fract ((k : ℝ) * θ i) ≤ rightEndpoint ω i) →
        ProductCocycle.cocycleVersion θ c k (circleRightEndpoint ω) /
          ProductCocycle.cocycleVersion θ c k (circleLeftEndpoint ω) ≤ Real.exp (-c i) := by
  have hbound := ProductCocycle.ae_all_int_ratio_bounds_of_map_ac
    (law P) θ c hθ0 hθ hc circleLeftEndpoint circleRightEndpoint
    circleLeftEndpoint_measurable.aemeasurable circleRightEndpoint_measurable.aemeasurable
    (circleLeftEndpoint_map_absolutelyContinuous P hsum)
    (circleRightEndpoint_map_absolutelyContinuous P hsum)
    (ae_circle_endpoints_ordered P)
  filter_upwards [hbound, ae_real_circle_endpoints P] with ω hω hrep
  intro k
  refine ⟨div_pos (ProductCocycle.cocycleVersion_pos θ c k _)
    (ProductCocycle.cocycleVersion_pos θ c k _), (hω k).1, ?_⟩
  intro i hi
  apply (hω k).2 i
  have hx : ProductCocycle.representative (circleLeftEndpoint ω i) = leftEndpoint ω i :=
    congrFun hrep.1 i
  have hy : ProductCocycle.representative (circleRightEndpoint ω i) = rightEndpoint ω i :=
    congrFun hrep.2 i
  simpa only [hx, hy] using hi

end Invariant233.OrderedProductCoupling

end

end OAI
