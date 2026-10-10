import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapGermRestriction
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapConnectingArc

namespace OAI

/-! The same embedded connecting arc and exact parameter germs survive
 a regular-locus-preserving change fixed near its singular endpoints. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f g : M → ProjectionTarget 3} {p q : M}

theorem CrosscapConnectingArc.restrict_germs (A : CrosscapConnectingArc f p q)
    (hl : g =ᶠ[𝓝 p] f) (hr : g =ᶠ[𝓝 q] f)
    (hreg : ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) :
    ∃ B : CrosscapConnectingArc g p q, B.arc = A.arc := by
  obtain ⟨L,hL⟩ := A.left.restrict_germ hl
  obtain ⟨R,hR⟩ := A.right.restrict_germ hr
  refine ⟨{
    left := L
    right := R
    arc := A.arc
    source := A.source
    target := A.target
    regular := fun t ht => (hreg _).mpr (A.regular t ht)
    leftParameter := A.leftParameter
    rightParameter := A.rightParameter
    left_smooth := A.left_smooth
    left_inverse_smooth := A.left_inverse_smooth
    right_smooth := A.right_smooth
    right_inverse_smooth := A.right_inverse_smooth
    left_zero := A.left_zero
    right_zero := A.right_zero
    left_germ := ?_
    right_germ := ?_ },rfl⟩
  · rw [hL]
    exact A.left_germ
  · rw [hR]
    exact A.right_germ

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
