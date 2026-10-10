import OAI.GroupTheory.PolycyclicRecognition.Algebra.LeftInvariantRiemannianDistance
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ApproximateMidpointProper
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! # Approximate midpoints for the Riemannian distance -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric Manifold
open scoped Manifold ContDiff Topology Bundle

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] (e : E ≃L[ℝ] F)

theorem leftRiemannianMetric_approximateMidpoints :
    letI := leftRiemannianMetric (G := G) e
    HasApproximateMidpoints G := by
  let metric := leftRiemannianMetric (G := G) e
  let bundle := leftRiemannianBundle (G := G) e
  intro x y ε hε
  have hr : riemannianEDist (𝓘(ℝ, E)) x y < ENNReal.ofReal (dist x y + ε) := by
    change edist x y < _
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]
    linarith
  obtain ⟨γ, h₀, h₁, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hcont : ContinuousOn (fun t => dist x (γ t)) (Icc (0 : ℝ) 1) :=
    continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ.continuousOn)
  have hm : dist x y / 2 ∈ Icc (dist x (γ 0)) (dist x (γ 1)) := by
    rw [h₀, h₁, dist_self]
    constructor <;> linarith [dist_nonneg (x := x) (y := y)]
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc zero_le_one hcont hm
  have hleft : ENNReal.ofReal (dist x (γ t)) ≤ pathELength (𝓘(ℝ, E)) γ 0 t := by
    rw [← edist_dist]
    exact riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc le_rfl ht.2)) h₀ rfl ht.1
  have hright : ENNReal.ofReal (dist (γ t) y) ≤ pathELength (𝓘(ℝ, E)) γ t 1 := by
    rw [← edist_dist]
    exact riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc ht.1 le_rfl)) rfl h₁ ht.2
  have hsum : dist x (γ t) + dist (γ t) y < dist x y + ε := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (add_nonneg dist_nonneg dist_nonneg)).mp
    calc
      ENNReal.ofReal (dist x (γ t) + dist (γ t) y) =
          ENNReal.ofReal (dist x (γ t)) + ENNReal.ofReal (dist (γ t) y) :=
        ENNReal.ofReal_add dist_nonneg dist_nonneg
      _ ≤ pathELength (𝓘(ℝ, E)) γ 0 t + pathELength (𝓘(ℝ, E)) γ t 1 :=
        add_le_add hleft hright
      _ = pathELength (𝓘(ℝ, E)) γ 0 1 := pathELength_add ht.1 ht.2
      _ < _ := hlen
  refine ⟨γ t, ?_, ?_⟩ <;> linarith

theorem leftRiemannianMetric_proper [LocallyCompactSpace G] :
    letI := leftRiemannianMetric (G := G) e
    ProperSpace G := by
  let metric := leftRiemannianMetric (G := G) e
  let isometric := leftRiemannianMetric_isometric (G := G) e
  let groupTopology : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  exact properSpace_of_approximateMidpoints (leftRiemannianMetric_approximateMidpoints e)

end PolycyclicRecognition

end

end OAI
