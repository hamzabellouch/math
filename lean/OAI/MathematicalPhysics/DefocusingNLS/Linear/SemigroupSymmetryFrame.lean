import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ProjectionCoordinates
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteSymmetryBackward

namespace OAI

/-! The concrete symmetry frame intertwines the actual semigroup and its three diagonal factors. -/

open scoped NNReal
namespace DefocusingNLS
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem semigroup_symmetryFrame_forward
    (S : ℝ≥0 → V →L[ℂ] V) (P : V →L[ℂ] V)
    (hcomm : ∀ t, Commute (S t) P) (hfin : FiniteDimensional ℂ P.range)
    (G : P.range →L[ℂ] P.range)
    (hG : ∀ t, projectionSemigroupRestriction S P hcomm t=NormedSpace.exp ((t : ℝ) • G))
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam)=⊤)
    (hspec : ∀ (lam : ℂ) (w : P.range), w ≠ 0 → G w=lam • w → lam=0 ∨ lam=1 ∨ lam=1/2)
    (t : ℝ≥0) (u : SymmetryCoordinates G) :
    let e := symmetryCoordinateEquiv G hspan hspec
    S t (projectionFrame P e u)=
      projectionFrame P e (symmetryCoordinateEvolution G t u) := by
  let : FiniteDimensional ℂ P.range := hfin
  let : CompleteSpace P.range := FiniteDimensional.complete ℂ P.range
  intro e
  have hh := congrArg (fun L : P.range →L[ℂ] P.range => L (e u)) (hG t)
  change projectionSemigroupRestriction S P hcomm t (symmetryCoordinateSum G u)=
    NormedSpace.exp ((t : ℝ) • G) (symmetryCoordinateSum G u) at hh
  rw [symmetryCoordinateEvolution_intertwines] at hh
  exact congrArg Subtype.val hh

theorem semigroup_symmetryFrame_coordinates
    (S : ℝ≥0 → V →L[ℂ] V) (P : V →L[ℂ] V) (hP : IsIdempotentElem P)
    (hcomm : ∀ t, Commute (S t) P) (hfin : FiniteDimensional ℂ P.range)
    (G : P.range →L[ℂ] P.range)
    (hG : ∀ t, projectionSemigroupRestriction S P hcomm t=NormedSpace.exp ((t : ℝ) • G))
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam)=⊤)
    (hspec : ∀ (lam : ℂ) (w : P.range), w ≠ 0 → G w=lam • w → lam=0 ∨ lam=1 ∨ lam=1/2)
    (t : ℝ≥0) (v : V) :
    let e := symmetryCoordinateEquiv G hspan hspec
    projectionCoordinates P e (S t v)=
      symmetryCoordinateEvolution G t (projectionCoordinates P e v) := by
  intro e
  have hinj : Function.Injective (projectionFrame P e) := by
    intro x y hxy
    have hh := congrArg (projectionCoordinates P e) hxy
    simpa only [projectionCoordinates_frame P hP e] using hh
  apply hinj
  rw [projectionFrame_coordinates]
  rw [← semigroup_symmetryFrame_forward S P hcomm hfin G hG hspan hspec]
  rw [projectionFrame_coordinates]
  exact (congrArg (fun L : V →L[ℂ] V => L v) (hcomm t).eq).symm

end DefocusingNLS

end OAI
