import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceCurveExterior
import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryNormalMatching
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRegularity

namespace OAI

/-! Strict original boundary geometry gives both positive pairings needed
to glue the exact canonical normal to the exterior projected normal. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes GeometryPreservation VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem compact_surface_boundary_matching
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {C : Set M} (hC : IsCompact C)
    (hCs : C ⊆ ((chart (i : M)).trans e).source)
    (hw : ∀ p ∈ C, A.weight i p ≠ 0)
    (v : SmallModes.Base → SmallModes.Base) (hv : Continuous v)
    (hB : ∀ p ∈ C, realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
      (baseEquiv (e (chart (i : M) p))) ≠ 0)
    (havoid : ∀ p ∈ C, spaceCoordinates (n.vector p) ≠
      -normalize (realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
        (baseEquiv (e (chart (i : M) p)))))
    (hpositive : ∀ p ∈ C,
      let q := baseEquiv (e (chart (i : M) p))
      0 < realSecondForm (A.phaseRealChartMap i e.symm F) (v q) (v q) q ⬝ᵥ
        spaceCoordinates (n.vector p))
    (hcross : ∀ p ∈ C,
      let q := baseEquiv (e (chart (i : M) p))
      let H := A.phaseRealChartMap i e.symm F
      0 < orderedCrossing H dy (v q) q
        (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) q)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ p ∈ C ∩ closure O, ∀ z : ℝ,
      let q := baseEquiv (e (chart (i : M) p))
      let H := A.phaseRealChartMap i e.symm W
      0 < realSecondForm H (v q) (v q) q ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField W n.vector p) ∧
      0 < realSecondForm H (v q) (v q) q ⬝ᵥ profilePreferred (realBoundaryProfile H z q) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let Q : C → JetPolynomial.Base := fun p => e (chart (i : M) p)
  have hQ : Continuous Q := ((chart (i : M)).trans e).continuousOn.comp_continuous
    continuous_subtype_val (fun p => hCs p.property)
  have hK : IsCompact (Set.range Q) := isCompact_range hQ
  obtain ⟨S,hS,hKS,hSc,_⟩ := CollarVelocity.compact_open_thickening hK isOpen_univ (subset_univ _)
  have hD (p : C) := A.phase_gram_at_source i e he hi hF (hCs p.property) (hw p p.property)
  let H := A.phaseRealChartMap i e.symm F
  let κ : C → ℝ := fun p => coordinateGaussianCurvature (realMetric H dx dx)
    (realMetric H dx dy) (realMetric H dy dy) (baseEquiv (Q p))
  obtain ⟨δ,hδ,hstab⟩ := compact_actual_boundary_matching (A.phaseRealChartMap_smooth i hi hF.1)
    (baseEquiv.continuous.comp hQ) (hv.comp (baseEquiv.continuous.comp hQ))
    (spaceCoordinates.continuous.comp (n.smooth.continuous.comp continuous_subtype_val))
    hD (fun p : C => hB p p.property) (fun p : C => havoid p p.property)
    (fun p : C => hpositive p p.property) κ
    (fun p => coordinateGauss_eq_curvature_mul H _ (hD p))
    (fun p : C => hcross p p.property)
  obtain ⟨ρ,hρ,hcontrol⟩ := A.cross_phase_exterior_control A hF.1
    (IsSmoothIsometricImmersion.mfderiv_injective hF) n houter i hi hS hSc hδ
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV O hext p hp z
  let P := phaseExteriorDomain (i : M) e O
  have hP := phaseExteriorDomain_properties (i : M) e O
  obtain ⟨_,hn,hj⟩ := hcontrol G V W hG hV hW b c hb hc hbc hGF hWV O P
    (fun y hy => (hP y hy).1) (fun y hy => (hP y hy).2) hext p hp.2
    (Q ⟨p,hp.1⟩) ⟨phaseExteriorDomain_closure (i : M) e O (hCs hp.1) hp.2,
      hKS (mem_range_self (⟨p,hp.1⟩ : C))⟩
  have hh := hstab (⟨p,hp.1⟩ : C) _ (A.phaseRealChartMap_smooth i hi hW) _ hj hn z
  exact ⟨hh.2.2.1,hh.2.2.2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
