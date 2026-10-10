import OAI.GroupTheory.PolycyclicRecognition.Algebra.LeftInvariantRiemannianDistance
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GroupIncrementLipschitz
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! # Smooth maps into the invariant Riemannian metric are locally Lipschitz -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Manifold Bundle
open scoped Topology Manifold ContDiff Bundle

variable {E F V G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] (e : E ≃L[ℝ] F)

theorem smooth_into_leftRiemannian_locallyLipschitz {f : V → G}
    (hf : ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ f) :
    letI := leftRiemannianMetric (G := G) e
    LocallyLipschitz f := by
  let metric := leftRiemannianMetric (G := G) e
  let bundle := leftRiemannianBundle (G := G) e
  let continuousBundle : IsContinuousRiemannianBundle E
      (TangentSpace (𝓘(ℝ, E)) : G → Type _) :=
    ⟨⟨(leftInvariantRiemannianMetric (G := G) e).inner,
      (leftInvariantRiemannianMetric (G := G) e).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let groupTopology : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  let isometric := leftRiemannianMetric_isometric (G := G) e
  obtain ⟨C, _, hC⟩ := eventually_riemannianEDist_le_edist_extChartAt (𝓘(ℝ, E)) (1 : G)
  let χ : G → E := extChartAt (𝓘(ℝ, E)) (1 : G)
  let U := {z : G | riemannianEDist (𝓘(ℝ, E)) 1 z ≤ C * edist (χ 1) (χ z)}
  apply locallyLipschitz_of_group_increments f χ hf.continuous C U hC
  · intro z hz
    have hb := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top (χ 1) (χ z))) hz
    change (edist (1 : G) z).toReal ≤ _ at hb
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] using hb
  · intro x
    have hincr : ContMDiff ((𝓘(ℝ, V)).prod (𝓘(ℝ, V))) (𝓘(ℝ, E)) ∞
        (fun p : V × V => (f p.1)⁻¹ * f p.2) :=
      (hf.comp contMDiff_fst).inv.mul (hf.comp contMDiff_snd)
    have hchart : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ χ ((f x)⁻¹ * f x) := by
      simpa only [inv_mul_cancel] using (contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (x := (1 : G)))
    have hc := hchart.comp (x, x) hincr.contMDiffAt
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hc
    exact (hc.contDiffAt.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith

end PolycyclicRecognition

end

end OAI
