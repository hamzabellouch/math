import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocalRiemannianChart
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! # Smooth maps from the invariant Riemannian metric are locally Lipschitz -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Manifold
open scoped Topology Manifold ContDiff

variable {E F V G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] (e : E ≃L[ℝ] F)

theorem smooth_from_leftRiemannian_locallyLipschitz {f : G → V}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ f) :
    letI := leftRiemannianMetric (G := G) e
    LocallyLipschitz f := by
  let metric := leftRiemannianMetric (G := G) e
  intro x
  obtain ⟨C, U, hU, hχ⟩ := leftRiemannianChart_lipschitz e x
  let χ := extChartAt (𝓘(ℝ, E)) x
  have hs : ContDiffAt ℝ 1 (f ∘ χ.symm) (χ x) := by
    have hm := contMDiffAt_iff_source.mp
      ((hf.contMDiffAt (x := x)).of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
    have hm' : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) 1 (f ∘ χ.symm) (χ x) := by
      have hr : Set.range (𝓘(ℝ, E)) = Set.univ := Set.range_id
      rw [hr, contMDiffWithinAt_univ] at hm
      exact hm
    exact hm'.contDiffAt
  obtain ⟨K, A, hA, hKA⟩ := hs.exists_lipschitzOnWith
  have hpre : χ ⁻¹' A ∈ 𝓝 x := (continuousAt_extChartAt x).preimage_mem_nhds hA
  let W := U ∩ (χ ⁻¹' A ∩ χ.source)
  have hW : W ∈ 𝓝 x := inter_mem hU (inter_mem hpre (extChartAt_source_mem_nhds x))
  refine ⟨K * C, W, hW, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  have hb := hKA.dist_le_mul (x := χ y) (y := χ z) hy.2.1 hz.2.1
  have hcy := χ.left_inv hy.2.2
  have hcz := χ.left_inv hz.2.2
  simp only [Function.comp_apply, hcy, hcz] at hb
  calc
    dist (f y) (f z) ≤ K * dist (χ y) (χ z) := hb
    _ ≤ K * ((C : ℝ) * dist y z) :=
      mul_le_mul_of_nonneg_left (hχ.dist_le_mul (x := y) (y := z) hy.1 hz.1) K.coe_nonneg
    _ = ↑(K * C) * dist y z := by simp only [NNReal.coe_mul, mul_assoc]

end PolycyclicRecognition

end

end OAI
