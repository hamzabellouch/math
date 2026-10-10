import Mathlib
import OAI.Analysis.WeakInfiniteness.Hereditary

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology

variable {A : Type*} [NonUnitalCStarAlgebra A]

def IsClosedInner (D : NonUnitalStarSubalgebra ℂ A) : Prop :=
    IsClosed (D : Set A) ∧ ∀ a ∈ D, ∀ b ∈ D, ∀ x : A, a*x*b ∈ D

lemma hereditarySubalgebra_inner (h : A) (hh : IsSelfAdjoint h) :
    IsClosedInner (hereditarySubalgebra h hh) := by
  refine ⟨NonUnitalStarSubalgebra.isClosed_topologicalClosure _,?_⟩
  intro a ha b hb x
  have hc : IsClosed {a : A | a*x*b ∈ hereditarySubalgebra h hh} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage (by fun_prop)
  apply closure_minimal _ hc ha
  rintro _ ⟨u,rfl⟩
  have hc' : IsClosed {b : A | (h*u*h)*x*b ∈ hereditarySubalgebra h hh} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage (by fun_prop)
  apply closure_minimal _ hc' hb
  rintro _ ⟨v,rfl⟩
  have he : (h*u*h)*x*(h*v*h)=h*(u*h*x*h*v)*h := by noncomm_ring
  change (h*u*h)*x*(h*v*h) ∈ hereditarySubalgebra h hh
  rw [he]
  exact sandwich_mem h (u*h*x*h*v) hh

lemma hereditarySubalgebra_le_of_mem {D : NonUnitalStarSubalgebra ℂ A}
    (hD : IsClosedInner D) {h : A} (hh : IsSelfAdjoint h) (hm : h ∈ D) :
    hereditarySubalgebra h hh ≤ D := by
  intro a ha
  apply closure_minimal _ hD.1 ha
  rintro _ ⟨x,rfl⟩
  exact hD.2 h hm h hm x

lemma IsClosedInner.symmetrized_corner_mem {D : NonUnitalStarSubalgebra ℂ A}
    (hD : IsClosedInner D) {p q : A} (hp : p ∈ D) (hq : q ∈ D) (x : A) :
    p*x*q+star (p*x*q) ∈ D :=
  D.add_mem (hD.2 p hp q hq x) (star_mem (s := D) (hD.2 p hp q hq x))

end

end WeakPureInfiniteness
end

end OAI
