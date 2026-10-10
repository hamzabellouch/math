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

omit [CompactSpace M] in
lemma jetChartMap_sub (i : A.centers) (F G : M → Space) :
    A.jetChartMap i (G-F) = fun p => A.jetChartMap i G p-A.jetChartMap i F p := by
  unfold jetChartMap
  rw [A.vectorChartRead_sub]
  funext p
  exact map_sub spaceCoordinates _ _

theorem jetChartMap_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ C : ℝ, 0 ≤ C → A.WeightedBound 1 m C F →
      WeightedEstimates.WeightedBound univ 1 m (D*C) (A.jetChartMap i F) := by
  obtain ⟨D,hD,hd⟩ := A.vectorChartRead_bound (V := Space) i m
  refine ⟨‖spaceCoordinates.toContinuousLinearMap‖*D,mul_nonneg (norm_nonneg _) hD,?_⟩
  intro F hF C hC hb
  have hh := (hd F 1 C zero_lt_one le_rfl hC hF hb).linear uniqueDiffOn_univ zero_le_one
    (A.vectorChartRead_smooth i hF).contDiffOn spaceCoordinates.toContinuousLinearMap
  simpa only [jetChartMap,Function.comp_def,mul_assoc,ContinuousLinearEquiv.coe_coe] using hh

theorem geometricLeadingProfile_stability (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hFO : MapsTo (lowJet (A.jetChartMap i F)) S O) {K : Set JetPolynomial.Base}
    (hK : IsCompact K) (hKS : K ⊆ S) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G : M → Space, ∀ hG : ContMDiff planeModel spaceModel ∞ G,
      ∀ hGO : MapsTo (lowJet (A.jetChartMap i G)) S O,
      A.WeightedBound 1 3 ρ (G-F) → ∀ p ∈ K, ∀ t : CovarianceCorrector.Period,
      ‖l.geometricLeadingProfile (A.jetChartMap i G) (A.jetChartMap_smooth i hG) hGO p t-
        l.geometricLeadingProfile (A.jetChartMap i F) (A.jetChartMap_smooth i hF) hFO p t‖ < ε := by
  obtain ⟨δ,hδ,hclose⟩ := l.geometricLeadingProfile_stability
    (A.jetChartMap_smooth i hF) hFO hK hKS ε hε
  obtain ⟨D,hD,hd⟩ := A.jetChartMap_bound i 3
  let ρ := δ/(D+1)
  have hρ : 0 < ρ := div_pos hδ (by positivity)
  refine ⟨ρ,hρ,?_⟩
  intro G hG hGO hb p hp t
  have hbound := hd (G-F) (hG.sub hF) ρ hρ.le hb
  rw [A.jetChartMap_sub] at hbound
  apply hclose _ (A.jetChartMap_smooth i hG) hGO _ p hp t
  apply (hbound.restrict_open S.isOpen).mono_const
  have he : ρ*(D+1) = δ := div_mul_cancel₀ δ (by positivity)
  nlinarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
