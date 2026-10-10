import OAI.Geometry.CylinderCovering.Nilpotent.RateCost
import OAI.Geometry.CylinderCovering.Nilpotent.GridBridge
import OAI.Geometry.CylinderCovering.Nilpotent.GridConvergence
import OAI.Geometry.CylinderCovering.Nilpotent.RetainedArea
import OAI.Geometry.CylinderCovering.Convexity.FiniteLatticeNeighborhood

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace CylinderCovering.NilpotentRate

theorem gridUnion_excess_tendsto {D : Set Plane} (hD : IsCompact D) :
    Tendsto (fun δ : ℝ => volume.real (gridUnion δ D \ D)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨B, hB, hb⟩ := compact_coordinate_bound hD
  apply (NilpotentGrid.coarseUnion_excess_tendsto hD B).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [gridUnion_eq_coarseUnion hδ hb]

theorem construction_cost_bounds {δ M K h B W : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (hK : 0 ≤ K) (hB : 0 ≤ B) (hW : 0 ≤ W)
    {D : Set Plane} {G : Plane → Plane} (hD : IsCompact D)
    {tag : Index → Plane} {Q : Index → Plane ≃ₗᵢ[ℝ] Plane}
    (hbound : ∀ x ∈ D, |x 0| ≤ B ∧ |x 1| ≤ B)
    (hdata : ∀ i ∈ coarseIndices δ D, tag i ∈ cell δ i ∧ ‖fderiv ℝ G (tag i)‖ ≤ M)
    (hint : IntegrableOn (fun b => RuledApproximation.physicalWeight h (G b)) (gridUnion δ D))
    (hosc : ∀ i ∈ coarseIndices δ D, ∀ b ∈ cell δ i,
      |RuledApproximation.physicalWeight h (G b) - RuledApproximation.physicalWeight h (G (tag i))| ≤ W * δ) :
    constructionCost h δ (collarRadius M K δ) D G tag Q ≤
      (∫ b in gridUnion δ D, RuledApproximation.physicalWeight h (G b)) +
        ((2 * B + 4) ^ 2 * (localCostError M K h + W)) * δ ∧
    constructionCost h δ (collarRadius M K δ) D G tag Q ≤
      (∫ b in D, RuledApproximation.physicalWeight h (G b)) +
        volume.real (gridUnion δ D \ D) + ((2 * B + 4) ^ 2 * (localCostError M K h + W)) * δ := by
  have hfin := finite_retainedIndices hδ hD.isBounded (collarRadius M K δ) Q
  have hcost := constructionCost_le_tagged_sum (h := h) hδ hδ1 hM hK hB hbound hfin hdata
    (fun i hi s hs => retained_fine_area_bound hδ (by unfold collarRadius; positivity) (Q i) i s hs)
  have hint' : IntegrableOn (fun b => RuledApproximation.physicalWeight h (G b))
      (NilpotentGrid.coarseUnion δ B D) := by rwa [← gridUnion_eq_coarseUnion hδ hbound]
  have hosc' : ∀ i ∈ NilpotentGrid.coarseIndices δ B D, ∀ b ∈ NilpotentGrid.coarseCell δ i,
      |RuledApproximation.physicalWeight h (G b) - RuledApproximation.physicalWeight h (G (tag i))| ≤ W * δ := by
    intro i hi b hb
    apply hosc i _ b hb
    rw [coarseIndices_eq_finset hδ hbound]
    exact hi
  have hquad := NilpotentGrid.coarseUnion_integral_error_of_oscillation D hδ hδ1 hB hW tag
    (fun b => RuledApproximation.physicalWeight h (G b)) hint' hosc'
  rw [← gridUnion_eq_coarseUnion hδ hbound] at hquad
  have hq := (abs_le.mp hquad).1
  have hu := NilpotentGrid.coarseUnion_integral_le hδ hD.measurableSet hbound
    (fun b => RuledApproximation.physicalWeight h (G b)) hint'
    (fun b hb => RuledApproximation.physicalWeight_le_one h (G b))
  rw [← gridUnion_eq_coarseUnion hδ hbound] at hu
  constructor <;> nlinarith only [hcost, hq, hu]

def LocalAnalyticData (D : Set Plane) (G : Plane → Plane) (h : ℝ) : Prop :=
  ∃ M K W δ₀ : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ 0 ≤ W ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      IntegrableOn (fun b => RuledApproximation.physicalWeight h (G b)) (gridUnion δ D) ∧
      ∀ i : Index, ∀ x ∈ cell δ i ∩ D,
        ‖fderiv ℝ G x‖ ≤ M ∧ ∀ b ∈ cell δ i,
          ‖G b - (G x + fderiv ℝ G x (b - x))‖ ≤ K * δ ^ 2 ∧
          |RuledApproximation.physicalWeight h (G b) -
            RuledApproximation.physicalWeight h (G x)| ≤ W * δ

theorem assemble_smooth_rate
    (hproducer : ∀ (D : Set Plane) (G : Plane → Plane) (h : ℝ),
      IsCompact D → BoundedSecondNear D G → LocalAnalyticData D G h) :
    SmoothRateStatement := by
  intro D G h hD hG hnil hh
  obtain ⟨B, hB, hbound⟩ := compact_coordinate_bound hD
  obtain ⟨M, K, W, δ₀, hM, hK, hW, hδ₀, hδ₀1, hprod⟩ := hproducer D G h hD hG
  refine ⟨gridUnion_excess_tendsto hD, M, K,
    (2 * B + 4) ^ 2 * (localCostError M K h + W), δ₀, hM, hK,
    mul_nonneg (sq_nonneg _) (add_nonneg (localCostError_nonneg hM hK) hW), hδ₀, ?_⟩
  intro δ hδ hδsmall
  obtain ⟨tag, Q, htag⟩ := choose_tags_frames (δ := δ) hnil
  obtain ⟨hint, han⟩ := hprod δ hδ hδsmall
  have hdata : ∀ i ∈ coarseIndices δ D, tag i ∈ cell δ i ∩ D ∧
      IsShearFrame (fderiv ℝ G (tag i)) (Q i) ∧ ‖fderiv ℝ G (tag i)‖ ≤ M ∧
      ∀ b ∈ cell δ i, ‖G b - affineVelocity G tag i b‖ ≤ K * δ ^ 2 := by
    intro i hi
    have ht := htag i hi
    have ha := han i (tag i) ht.1
    exact ⟨ht.1, ht.2, ha.1, fun b hb => (ha.2 b hb).1⟩
  have hcost := construction_cost_bounds (Q := Q) hδ (hδsmall.le.trans hδ₀1) hM hK hB hW hD hbound
    (fun i hi => ⟨(hdata i hi).1.1, (hdata i hi).2.2.1⟩) hint
    (fun i hi b hb => (han i (tag i) (htag i hi).1).2 b hb |>.2)
  exact ⟨tag, Q, hdata, finite_retainedIndices hδ hD.isBounded _ Q,
    construction_covers_of_bounds hδ hM hK hnil hdata, hcost.1, hcost.2⟩

end CylinderCovering.NilpotentRate

end

end OAI
