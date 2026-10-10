import OAI.Geometry.SurfaceImmersion.Atlas.PhaseBoundaryCurve
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseTransitionVectors

namespace OAI

/-! Smooth direction coefficients for the actual pieces of later curves
inside one fixed primitive disk. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

def inPhase (q : M) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (K : Set M) : Set Base := (surfacePhaseChart q e) '' (c.carrier ∩ K)

omit [CompactSpace M] in
lemma inPhase_compact (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ (surfacePhaseChart q e).source) :
    IsCompact (c.inPhase q e K) :=
  (c.compact.inter hK).image_of_continuousOn
    ((surfacePhaseChart q e).continuousOn.mono (fun _ hp => hKs hp.2))

omit [CompactSpace M] [T2Space M] in
lemma inPhase_transition_target (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set M} (hKs : K ⊆ (surfacePhaseChart q e).source) :
    c.inPhase q e K ⊆ (surfacePhaseTransition (c.index : M) c.phase q e).target := by
  rintro _ ⟨p,hp,rfl⟩
  change surfacePhaseChart q e p ∈
    ((surfacePhaseChart (c.index : M) c.phase).symm.trans (surfacePhaseChart q e)).target
  refine ⟨(surfacePhaseChart q e).map_source (hKs hp.2),?_⟩
  change (surfacePhaseChart q e).symm (surfacePhaseChart q e p) ∈
    (surfacePhaseChart (c.index : M) c.phase).source
  rw [(surfacePhaseChart q e).left_inv (hKs hp.2)]
  exact c.source hp.1

omit [CompactSpace M] [T2Space M] in
lemma coordinate_transition (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {p : M} (hp : p ∈ c.carrier) :
    surfacePhaseTransition (c.index : M) c.phase q e (c.coordinate p) = surfacePhaseChart q e p := by
  change surfacePhaseChart q e ((surfacePhaseChart (c.index : M) c.phase).symm
    ((surfacePhaseChart (c.index : M) c.phase) p)) = _
  rw [(surfacePhaseChart (c.index : M) c.phase).left_inv (c.source hp)]

omit [CompactSpace M] in
theorem inPhase_direction_coefficients (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ (surfacePhaseChart q e).source) :
    ∃ b d : Base → ℝ, ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ d ∧
      (∀ x ∈ c.inPhase q e K, b x ≠ 0 ∨ d x ≠ 0) ∧
      ∀ p ∈ c.carrier ∩ K,
        (b (surfacePhaseChart q e p),d (surfacePhaseChart q e p)) =
          fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase q e) (c.coordinate p) dy := by
  let T := surfacePhaseTransition (c.index : M) c.phase q e
  obtain ⟨v,hv,hspec⟩ := compact_transverse_vector T
    (surfacePhaseTransition_smooth (c.index : M) c.phase c.inverse_smooth q e he)
    (surfacePhaseTransition_smooth q e hi (c.index : M) c.phase c.smooth)
    (c.inPhase_compact q e hK hKs) (c.inPhase_transition_target q e hKs)
  refine ⟨fun x => (v x).1,fun x => (v x).2,hv.fst,hv.snd,?_,?_⟩
  · intro x hx
    by_contra hh
    push Not at hh
    exact (hspec x hx).2 (Prod.ext hh.1 hh.2)
  · intro p hp
    change v (surfacePhaseChart q e p) = _
    have hx : surfacePhaseChart q e p ∈ c.inPhase q e K := mem_image_of_mem _ hp
    rw [(hspec _ hx).1]
    have hxt : c.coordinate p ∈ T.source := by
      refine ⟨(surfacePhaseChart (c.index : M) c.phase).map_source (c.source hp.1),?_⟩
      change (surfacePhaseChart (c.index : M) c.phase).symm
        ((surfacePhaseChart (c.index : M) c.phase) p) ∈ (surfacePhaseChart q e).source
      rw [(surfacePhaseChart (c.index : M) c.phase).left_inv (c.source hp.1)]
      exact hKs hp.2
    rw [← c.coordinate_transition q e hp.1,T.left_inv hxt]

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
