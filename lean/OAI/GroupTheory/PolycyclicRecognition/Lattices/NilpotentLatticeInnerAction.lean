import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeLinearAction
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeAutomorphismUnipotent
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OAI

/-! # Unipotent corrections in a nonsplit nilpotent-by-abelian extension

Commutators of quotient lifts need not be trivial. Their induced action on
the nilpotent Lie model is the actual inner action and is unipotent.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement IsMulCommutative

namespace NilpotentLatticeCoordinates
variable {H : Type} [Group H] [Group.IsNilpotent H] (C : NilpotentLatticeCoordinates H)

theorem automorphismLinear_inner_unipotent (t : H) :
    IsNilpotent (C.automorphismLinear (MulAut.conj t) - 1) := by
  let q := C.lattice.subtype.comp C.equiv.toMonoidHom
  apply lattice_automorphism_unipotent C.basis C.parameter C.polynomial C.parameter.surjective q
    (fun z => ⟨orderedWord C.generators z, (C.integer_parameter z).symm⟩)
    (MonoidHom.id H) Function.injective_id (MulAut.conj t) t
  · intro x
    rfl
  · intro x
    change C.automorphismLinear (MulAut.conj t) (C.equiv x) = _
    rw [C.automorphismLinear_apply, C.automorphism_on_lattice]
    rfl

end NilpotentLatticeCoordinates

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]
  (C : NilpotentLatticeCoordinates N)

def nilpotentConjugationLinear : G →* Module.End ℝ C.carrier :=
  C.automorphismLinear.comp (MulAut.conjNormal (H := N))

theorem nilpotentConjugationLinear_inner_unipotent (t : N) :
    IsNilpotent (nilpotentConjugationLinear N C (t : G) - 1) := by
  change IsNilpotent (C.automorphismLinear (MulAut.conjNormal (t : G)) - 1)
  rw [MulAut.conjNormal_val]
  exact C.automorphismLinear_inner_unipotent t

theorem nilpotentConjugationLinear_commutator_unipotent [IsMulCommutative (G ⧸ N)]
    (g h : G) : IsNilpotent (nilpotentConjugationLinear N C ⁅g, h⁆ - 1) := by
  have hN : ⁅g, h⁆ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' N) ⁅g, h⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  exact nilpotentConjugationLinear_inner_unipotent N C ⟨⁅g, h⁆, hN⟩

end PolycyclicRecognition

end

end OAI
