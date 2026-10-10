import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitivePatch
import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhaseCurveVectors

namespace OAI

/-! Actual remaining boundary curves and finite crossing points inside a
constructed primitive patch. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {A B : SmoothingAtlas M} {i : A.centers}
  {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
  {F : M → Space} {amp phi : M → ℝ} {D : Set M}
namespace SupportedPrimitivePatch
variable (d : SupportedPrimitivePatch A i e F amp phi D)

omit [T2Space M] in
lemma coordinate_mem_compact {p : M} (hp : p ∈ closure D) :
    baseEquiv.symm (surfacePhaseChart (i : M) e p) ∈ d.compactSet := by
  change baseEquiv.symm (baseEquiv (e (chart (i : M) p))) ∈ _
  rw [baseEquiv.symm_apply_apply]
  exact d.closed_coordinates p hp

omit [T2Space M] in
lemma coordinate_mem_region {p : M} (hp : p ∈ closure D) :
    surfacePhaseChart (i : M) e p ∈ d.region := by
  apply d.window_region
  refine ⟨baseEquiv.symm (surfacePhaseChart (i : M) e p),?_,baseEquiv.apply_symm_apply _⟩
  exact subset_closure (d.support_window (d.coordinate_mem_compact hp))

def curve (_d : SupportedPrimitivePatch A i e F amp phi D) (c : PhaseBoundaryCurve B) : Set Base := c.inPhase (i : M) e (closure D)

lemma curve_compact (c : PhaseBoundaryCurve B) : IsCompact (d.curve c) :=
  c.inPhase_compact (i : M) e isClosed_closure.isCompact d.source_closed

omit [T2Space M] in
lemma curve_region (c : PhaseBoundaryCurve B) : d.curve c ⊆ d.region := by
  rintro x ⟨p,hp,rfl⟩
  exact d.coordinate_mem_region hp.2

omit [T2Space M] in
lemma curve_compact_coordinates (c : PhaseBoundaryCurve B) :
    ∀ x ∈ d.curve c, baseEquiv.symm x ∈ d.compactSet := by
  rintro x ⟨p,hp,rfl⟩
  exact d.coordinate_mem_compact hp.2

theorem curve_coefficients (c : PhaseBoundaryCurve B) :
    ∃ b k : Base → ℝ, ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ k ∧
      (∀ x ∈ d.curve c, b x ≠ 0 ∨ k x ≠ 0) ∧
      ∀ p ∈ c.carrier ∩ closure D,
        (b (surfacePhaseChart (i : M) e p),k (surfacePhaseChart (i : M) e p)) =
          fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) dy :=
  c.inPhase_direction_coefficients (i : M) e d.phase_smooth d.inverse_smooth
    isClosed_closure.isCompact d.source_closed

def innerCrossings (_d : SupportedPrimitivePatch A i e F amp phi D) (E : Set M) : Set Base := (surfacePhaseChart (i : M) e) '' (E ∩ D)

omit [T2Space M] in
lemma innerCrossings_finite {E : Set M} (hE : E.Finite) : (d.innerCrossings E).Finite :=
  (hE.inter_of_left D).image _

omit [T2Space M] in
lemma innerCrossings_positive (E : Set M) : ∀ x ∈ d.innerCrossings E, 0 < d.amplitude x := by
  rintro x ⟨p,hp,rfl⟩
  exact (d.amplitude_positive _).mpr ⟨p,hp.2,rfl⟩

omit [T2Space M] in
lemma innerCrossings_region (E : Set M) : d.innerCrossings E ⊆ d.region := by
  rintro x ⟨p,hp,rfl⟩
  exact d.coordinate_mem_region (subset_closure hp.2)

omit [T2Space M] in
lemma innerCrossings_compact_coordinates (E : Set M) :
    ∀ x ∈ d.innerCrossings E, baseEquiv.symm x ∈ d.compactSet := by
  rintro x ⟨p,hp,rfl⟩
  exact d.coordinate_mem_compact (subset_closure hp.2)

end SupportedPrimitivePatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
