import OAI.Geometry.CylinderCovering.Nilpotent.SmoothRateTheorem

namespace OAI

noncomputable section
open Set MeasureTheory

namespace CylinderCovering.NilpotentRate

theorem smoothRate_uniform (D : Set Plane) (G : Plane → Plane) (h : ℝ)
    (hD : IsCompact D) (hG : BoundedSecondNear D G)
    (hnil : ∀ p ∈ D, (fderiv ℝ G p).comp (fderiv ℝ G p) = 0) :
    ∃ M K C δ₀ : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ tag : Index → Plane, ∀ Q : Index → Plane ≃ₗᵢ[ℝ] Plane,
      (∀ i ∈ coarseIndices δ D, tag i ∈ cell δ i ∩ D ∧
        IsShearFrame (fderiv ℝ G (tag i)) (Q i)) →
      (∀ i ∈ coarseIndices δ D, ‖fderiv ℝ G (tag i)‖ ≤ M ∧
        ∀ b ∈ cell δ i, ‖G b - affineVelocity G tag i b‖ ≤ K * δ ^ 2) ∧
      (retainedIndices δ (collarRadius M K δ) D Q).Finite ∧
      RuledApproximation.physicalRuled 1 D G 1 ⊆
        constructionCarrier δ (collarRadius M K δ) D G tag Q ∧
      constructionCost h δ (collarRadius M K δ) D G tag Q ≤
        (∫ b in gridUnion δ D, RuledApproximation.physicalWeight h (G b)) + C * δ ∧
      constructionCost h δ (collarRadius M K δ) D G tag Q ≤
        (∫ b in D, RuledApproximation.physicalWeight h (G b)) +
          volume.real (gridUnion δ D \ D) + C * δ := by
  obtain ⟨B, hB, hbound⟩ := compact_coordinate_bound hD
  obtain ⟨M, K, W, δ₀, hM, hK, hW, hδ₀, hδ₀1, _, hprod⟩ :=
    bounded_second_coarse_data (D := D) (G := G) h hD hG
  refine ⟨M, K, (2*B+4)^2 * (localCostError M K h + W), δ₀,
    hM, hK, mul_nonneg (sq_nonneg _) (add_nonneg (localCostError_nonneg hM hK) hW),
    hδ₀, ?_⟩
  intro δ hδ hsmall tag Q hchoice
  obtain ⟨hint, han⟩ := hprod δ hδ hsmall
  have hdata : ∀ i ∈ coarseIndices δ D, tag i ∈ cell δ i ∩ D ∧
      IsShearFrame (fderiv ℝ G (tag i)) (Q i) ∧ ‖fderiv ℝ G (tag i)‖ ≤ M ∧
      ∀ b ∈ cell δ i, ‖G b - affineVelocity G tag i b‖ ≤ K * δ ^ 2 := by
    intro i hi
    have hc := hchoice i hi
    have ha := han i (tag i) hc.1
    exact ⟨hc.1, hc.2, ha.1, fun b hb => (ha.2 b hb).1⟩
  have hcost := construction_cost_bounds (D := D) (G := G) (tag := tag) (Q := Q)
    hδ (hsmall.le.trans hδ₀1)
    hM hK hB hW hD hbound
    (fun i hi => ⟨(hdata i hi).1.1, (hdata i hi).2.2.1⟩) hint
    (fun i hi b hb => ((han i (tag i) (hchoice i hi).1).2 b hb).2.2)
  exact ⟨fun i hi => (hdata i hi).2.2,
    finite_retainedIndices hδ hD.isBounded _ Q,
    construction_covers_of_bounds hδ hM hK hnil hdata, hcost.1, hcost.2⟩

end CylinderCovering.NilpotentRate

end

end OAI
