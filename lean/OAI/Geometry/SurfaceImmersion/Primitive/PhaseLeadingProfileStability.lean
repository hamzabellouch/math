import OAI.Geometry.SurfaceImmersion.Primitive.AtlasLeadingProfileStability
import OAI.Geometry.SurfaceImmersion.Geometry.CompactCompositionBound
import OAI.Geometry.SurfaceImmersion.Primitive.LeadingProfileStability
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveProfileStability
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasLowJetNeighborhood

namespace OAI

/-! The global C3 displacement controls all five geometric leading profiles
in a fixed atlas chart, uniformly on compact sets and all periodic phases. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetVelocityCoordinates WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phase_geometricLeadingProfile_stability (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base)))
    (hFO : MapsTo (lowJet (A.jetChartMap i F ∘ T)) S O) {K : Set JetPolynomial.Base}
    (hK : IsCompact K) (hKS : K ⊆ S) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G : M → Space, ∀ hG : ContMDiff planeModel spaceModel ∞ G,
      ∀ hGO : MapsTo (lowJet (A.jetChartMap i G ∘ T)) S O,
      A.WeightedBound 1 3 ρ (G-F) → ∀ p ∈ K, ∀ t : CovarianceCorrector.Period,
      ‖l.geometricLeadingProfile (A.jetChartMap i G ∘ T) ((A.jetChartMap_smooth i hG).comp hT) hGO p t-
        l.geometricLeadingProfile (A.jetChartMap i F ∘ T) ((A.jetChartMap_smooth i hF).comp hT) hFO p t‖ < ε := by
  obtain ⟨δ,hδ,hclose⟩ := l.geometricLeadingProfile_stability
    ((A.jetChartMap_smooth i hF).comp hT) hFO hK hKS ε hε
  obtain ⟨D₀,hD₀,hd⟩ := A.jetChartMap_bound i 3
  obtain ⟨D₁,hD₁,hcomp⟩ := compact_composition_bound (E := JetPolynomial.Space) hT S.isOpen hSc 3
  let ρ := δ/(D₁*D₀+1)
  have hD : 0 ≤ D₁*D₀ := mul_nonneg (by linarith) hD₀
  have hρ : 0 < ρ := div_pos hδ (by positivity)
  refine ⟨ρ,hρ,?_⟩
  intro G hG hGO hb p hp t
  have hbound := hd (G-F) (hG.sub hF) ρ hρ.le hb
  have hc := hcomp (A.jetChartMap i (G-F)) (D₀*ρ)
    (mul_nonneg hD₀ hρ.le) (A.jetChartMap_smooth i (hG.sub hF)) hbound
  rw [A.jetChartMap_sub] at hc
  apply hclose _ ((A.jetChartMap_smooth i hG).comp hT) hGO _ p hp t
  apply hc.mono_const
  have he : ρ*(D₁*D₀+1) = δ := div_mul_cancel₀ δ (by positivity)
  nlinarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
