import OAI.Geometry.Immersion.ClosedSurface.Main
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseExteriorDomain
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseExteriorPreservation

namespace OAI

/-! Exterior stability on actual compact curves of the surface. All chart
domains and compact parameter neighborhoods are constructed here. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes GeometryPreservation VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem compact_surface_phase_exterior_preservation
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : B.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {C : Set M} (hC : IsCompact C)
    (hCs : C ⊆ ((chart (i : M)).trans e).source)
    (hw : ∀ p ∈ C, B.weight i p ≠ 0)
    (hB : ∀ p ∈ C, realSecondForm (B.phaseRealChartMap i e.symm F) dy dy
      (baseEquiv (e (chart (i : M) p))) ≠ 0)
    (havoid : ∀ p ∈ C, spaceCoordinates (n.vector p) ≠
      -normalize (realSecondForm (B.phaseRealChartMap i e.symm F) dy dy
        (baseEquiv (e (chart (i : M) p))))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ p ∈ C ∩ closure O,
      A.projectedNormalField W n.vector p ≠ 0 ∧
      realSecondForm (B.phaseRealChartMap i e.symm W) dy dy
        (baseEquiv (e (chart (i : M) p))) ≠ 0 ∧
      spaceCoordinates (A.unitProjectedNormalField W n.vector p) ≠
        -normalize (realSecondForm (B.phaseRealChartMap i e.symm W) dy dy
          (baseEquiv (e (chart (i : M) p)))) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let Q : C → JetPolynomial.Base := fun p => e (chart (i : M) p)
  have hQ : Continuous Q := ((chart (i : M)).trans e).continuousOn.comp_continuous
    continuous_subtype_val (fun p => hCs p.property)
  have hK : IsCompact (Set.range Q) := isCompact_range hQ
  obtain ⟨S,hS,hKS,hSc,_⟩ := CollarVelocity.compact_open_thickening hK isOpen_univ (subset_univ _)
  obtain ⟨δ,hδ,hstab⟩ := compact_actual_exterior_avoidance (B.phaseRealChartMap_smooth i hi hF.1)
    (baseEquiv.continuous.comp hQ) (spaceCoordinates.continuous.comp
      (n.smooth.continuous.comp continuous_subtype_val)) continuous_const
    (fun p : C => B.phase_gram_at_source i e he hi hF (hCs p.property) (hw p p.property))
    (fun p : C => hB p p.property) (fun p : C => havoid p p.property)
  obtain ⟨ρ,hρ,hcontrol⟩ := A.cross_phase_exterior_control B hF.1 (IsSmoothIsometricImmersion.mfderiv_injective hF)
    n houter i hi hS hSc hδ
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV O hext p hp
  let P := phaseExteriorDomain (i : M) e O
  have hP := phaseExteriorDomain_properties (i : M) e O
  obtain ⟨hne,hn,hj⟩ := hcontrol G V W hG hV hW b c hb hc hbc hGF hWV O P
    (fun y hy => (hP y hy).1) (fun y hy => (hP y hy).2) hext p hp.2
    (Q ⟨p,hp.1⟩) ⟨phaseExteriorDomain_closure (i : M) e O (hCs hp.1) hp.2,
      hKS (mem_range_self (⟨p,hp.1⟩ : C))⟩
  exact ⟨hne,hstab ⟨p,hp.1⟩ _ (B.phaseRealChartMap_smooth i hi hW) _ hj hn⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
