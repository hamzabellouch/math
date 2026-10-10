import OAI.Geometry.SurfaceImmersion.Whitney.ClosedArcHalfChart
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapEndpoint

namespace OAI

/-! Prepared crosscaps are genuine boundary points of the compactified
unordered double curve. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem crosscap_half_line_chart {F : M → ProjectionTarget 3}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ c : OpenPartialHomeomorph (compactifiedDoubleCurve F) (Ici (0:ℝ)),
      ∃ hpK : unorderedPair (p,p) ∈ compactifiedDoubleCurve F,
        (⟨unorderedPair (p,p),hpK⟩ : compactifiedDoubleCurve F) ∈ c.source ∧
        c ⟨unorderedPair (p,p),hpK⟩ = ⟨0,by simp⟩ := by
  obtain ⟨δ,hδ,γ,hγ,hγ0,hmem,V,hV,hpV,hsub⟩ :=
    crosscap_half_arc_neighborhood hF p q hp hφ he b t hz hreg
  have hpγ : γ ⟨0,le_rfl,hδ.le⟩ ∈ V := by rwa [hγ0]
  obtain ⟨c,hc,hc0⟩ := closed_arc_half_chart hδ γ hγ.isEmbedding hmem hV hpγ hsub
  have hpK : unorderedPair (p,p) ∈ compactifiedDoubleCurve F := by
    rw [← hγ0]
    exact hmem _
  refine ⟨c,hpK,?_,?_⟩
  · simpa only [hγ0] using hc
  · simpa only [hγ0] using hc0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
