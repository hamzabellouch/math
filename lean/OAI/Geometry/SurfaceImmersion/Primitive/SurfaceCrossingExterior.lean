import OAI.Geometry.SurfaceImmersion.Atlas.PhaseCurvePairGeometry

namespace OAI

/-! Both intrinsic crossing invariants and positive normal pairings survive
on the exterior part of any compact set of mutual curve intersections. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c d : PhaseBoundaryCurve B)

theorem exterior_crossing_preservation (A : SmoothingAtlas M)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {K : Set M} (hK : IsCompact K) (hKc : K ⊆ c.carrier) (hKd : K ⊆ d.carrier)
    (O : Set M) (hKO : K ⊆ closure O)
    (hpositive : ∀ p ∈ K, 0 < c.second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
      0 < d.second F p ⬝ᵥ spaceCoordinates (n.vector p))
    (hcross : ∀ p ∈ K, 0 < c.crossing d F p ∧ 0 < d.crossing c F p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ∀ h : SmoothMetric M, IsSmoothIsometricImmersion M h W →
      ∀ b a : ℝ, 0 ≤ b → 0 ≤ a → b+a < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 a (W-V) →
      (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ p ∈ K,
      (0 < c.second W p ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField W n.vector p) ∧
       0 < d.second W p ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField W n.vector p)) ∧
      0 < c.crossing d W p ∧ 0 < d.crossing c W p := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Q : K → JetPolynomial.Base := fun p => c.phase (chart (c.index : M) p)
  have hQ : Continuous Q := ((chart (c.index : M)).trans c.phase).continuousOn.comp_continuous
    continuous_subtype_val (fun p => c.source (hKc p.property))
  obtain ⟨S,hS,hQS,hSc,_⟩ := CollarVelocity.compact_open_thickening (isCompact_range hQ)
    isOpen_univ (subset_univ _)
  let P := phaseExteriorDomain (c.index : M) c.phase O
  have hP := phaseExteriorDomain_properties (c.index : M) c.phase O
  have hu : Continuous (fun p : K => d.directionIn c p) :=
    (d.directionIn_continuousOn c).comp_continuous continuous_subtype_val
      (fun p => ⟨hKd p.property,hKc p.property⟩)
  have hleft {h : SmoothMetric M} {W : M → Space} (hW : IsSmoothIsometricImmersion M h W)
      (p : K) := c.second_eq W (hKc p.property)
  have hright {h : SmoothMetric M} {W : M → Space} (hW : IsSmoothIsometricImmersion M h W)
      (p : K) := d.second_in_chart c hW (hKd p.property) (hKc p.property)
  have hrev {h : SmoothMetric M} {W : M → Space} (hW : IsSmoothIsometricImmersion M h W)
      (p : K) := d.reverse_crossing_in_chart c hW (hKd p.property) (hKc p.property)
  obtain ⟨ρ,hρ,hpres⟩ := A.compact_phase_exterior_crossing_preservation B hF.1
    (IsSmoothIsometricImmersion.mfderiv_injective hF) n houter c.index c.inverse_smooth hS hSc
    continuous_subtype_val hQ O P (fun y hy => (hP y hy).1) (fun y hy => (hP y hy).2)
    (fun p : K => hKO p.property)
    (fun p : K => ⟨phaseExteriorDomain_closure (c.index : M) c.phase O
      (c.source (hKc p.property)) (hKO p.property),hQS (mem_range_self p)⟩)
    (fun p : K => B.phase_gram_at_source c.index c.phase c.smooth c.inverse_smooth hF
      (c.source (hKc p.property)) (c.active p (hKc p.property)))
    (v := fun _ => dy) (w := fun p : K => d.directionIn c p) continuous_const hu
    (fun p : K => by
      have hh := hpositive p p.property
      rw [hleft hF p,hright hF p] at hh
      exact hh)
    (fun p : K => by
      have hh := hcross p p.property
      rw [hrev hF p] at hh
      exact hh)
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV h hW b a hb ha hba hGF hWV hext p hp
  have hh := hpres G V W hG hV hW.1 b a hb ha hba hGF hWV hext (⟨p,hp⟩ : K)
  rw [hleft hW ⟨p,hp⟩,hright hW ⟨p,hp⟩,hrev hW ⟨p,hp⟩]
  exact hh

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
