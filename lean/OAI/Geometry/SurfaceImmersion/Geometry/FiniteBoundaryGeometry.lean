import OAI.Geometry.SurfaceImmersion.Atlas.PhaseCurvePairGeometry

namespace OAI

/-! The finite boundary invariant retained by successive primitive corrections. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {B : SmoothingAtlas M} {ι : Type*}

structure FiniteBoundaryGeometry (curves : ι → PhaseBoundaryCurve B) (E : Set M)
    (F : M → Space) (n : PreferredNormal F) : Prop where
  nonzero : ∀ j p, p ∈ (curves j).carrier → (curves j).second F p ≠ 0
  avoids : ∀ j p, p ∈ (curves j).carrier →
    spaceCoordinates (n.vector p) ≠ -normalize ((curves j).second F p)
  positive : ∀ j k, j ≠ k → ∀ p ∈ E, p ∈ (curves j).carrier → p ∈ (curves k).carrier →
    0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p)
  crossing : ∀ j k, j ≠ k → ∀ p ∈ E, p ∈ (curves j).carrier → p ∈ (curves k).carrier →
    0 < (curves j).crossing (curves k) F p

namespace FiniteBoundaryGeometry

lemma restrict {curves : ι → PhaseBoundaryCurve B} {E : Set M}
    {F : M → Space} {n : PreferredNormal F} (h : FiniteBoundaryGeometry curves E F n)
    {κ : Type*} (f : κ → ι) (hf : Function.Injective f) {E' : Set M} (hE : E' ⊆ E) :
    FiniteBoundaryGeometry (curves ∘ f) E' F n where
  nonzero j p hp := h.nonzero (f j) p hp
  avoids j p hp := h.avoids (f j) p hp
  positive j k hjk p hp hj hk := h.positive (f j) (f k) (fun he => hjk (hf he)) p (hE hp) hj hk
  crossing j k hjk p hp hj hk := h.crossing (f j) (f k) (fun he => hjk (hf he)) p (hE hp) hj hk

lemma pair_conditions {curves : ι → PhaseBoundaryCurve B} {E : Set M}
    {F : M → Space} {n : PreferredNormal F} (h : FiniteBoundaryGeometry curves E F n)
    {j k : ι} (hjk : j ≠ k) {p : M} (hp : p ∈ E)
    (hj : p ∈ (curves j).carrier) (hk : p ∈ (curves k).carrier) :
    0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
    0 < (curves k).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
    0 < (curves j).crossing (curves k) F p ∧
    0 < (curves k).crossing (curves j) F p :=
  ⟨h.positive j k hjk p hp hj hk,h.positive k j hjk.symm p hp hk hj,
    h.crossing j k hjk p hp hj hk,h.crossing k j hjk.symm p hp hk hj⟩

end FiniteBoundaryGeometry
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
