import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapArcNeighborhood

namespace OAI

/-! Each prepared crosscap has a genuine embedded half-interval
neighborhood in the compactified unordered double curve. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem crosscap_half_arc_neighborhood {F : M → ProjectionTarget 3}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ γ : Icc (0 : ℝ) δ → UnorderedSurfacePairs M,
      IsClosedEmbedding γ ∧ γ ⟨0,le_rfl,hδ.le⟩ = unorderedPair (p,p) ∧
      (∀ s, γ s ∈ compactifiedDoubleCurve F) ∧
      ∃ V : Set (UnorderedSurfacePairs M), IsOpen V ∧ unorderedPair (p,p) ∈ V ∧
        compactifiedDoubleCurve F ∩ V ⊆ Set.range γ := by
  obtain ⟨δ,hδ,γ,hγ,hformula,hzero,hmem⟩ :=
    crosscap_compact_half_arc F p q hp hφ he b t hz hreg
  obtain ⟨V,hV,hpV,hsub⟩ :=
    crosscap_arc_contains_neighborhood hF p q hp hφ he b t hz hreg hδ γ hformula
  exact ⟨δ,hδ,γ,hγ,hzero,hmem,V,hV,hpV,hsub⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
