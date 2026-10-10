import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalInductionExact
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RestrictionEquivalence
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OAI

/-! # Lifting a semilinear map to the induced representation

Conjugating the normal subgroup by a chosen lift of the cyclic generator
produces the translation map used in the extension resolution.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

omit [N.Normal] in
@[simp] theorem induction_mk_left_inv (B : Rep k N) (n : N) (g : G) (a : B) :
    IndV.mk N.subtype B.ρ ((n : G)⁻¹ * g) a = IndV.mk N.subtype B.ρ g (B.ρ n a) := by
  simpa using Coinvariants.mk_inv_tmul
    (ρ := (Representation.leftRegular k G).comp N.subtype) (τ := B.ρ)
    (MonoidAlgebra.single g 1) a n

def inducedSemilinearUnit (t : G) (A B : Rep k N)
    (b : A ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom B) :
    A ⟶ Rep.res N.subtype (Rep.ind N.subtype B) :=
  Rep.ofHom ⟨(IndV.mk N.subtype B.ρ t⁻¹).comp b.hom.toLinearMap, fun n => by
    ext a
    change IndV.mk N.subtype B.ρ t⁻¹ (b.hom (A.ρ n a)) =
      Representation.ind N.subtype B.ρ (n : G)
        (IndV.mk N.subtype B.ρ t⁻¹ (b.hom a))
    rw [Rep.hom_comm_apply b, Representation.ind_mk]
    change IndV.mk N.subtype B.ρ t⁻¹
        (B.ρ (MulAut.conjNormal (H := N) t⁻¹ n) (b.hom a)) = _
    rw [← induction_mk_left_inv]
    congr 2
    simp [mul_inv_rev, mul_assoc]⟩

def inducedSemilinearMap (t : G) (A B : Rep k N)
    (b : A ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom B) :
    Rep.ind N.subtype A ⟶ Rep.ind N.subtype B :=
  (Rep.indResHomEquiv N.subtype A (Rep.ind N.subtype B)).symm
    (inducedSemilinearUnit k N t A B b)

@[simp] theorem inducedSemilinearMap_mk (t : G) (A B : Rep k N)
    (b : A ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom B)
    (g : G) (a : A) :
    (inducedSemilinearMap k N t A B b).hom (IndV.mk N.subtype A.ρ g a) =
      IndV.mk N.subtype B.ρ (t⁻¹ * g) (b.hom a) := by
  simp [inducedSemilinearMap, Rep.indResHomEquiv, inducedSemilinearUnit]
  rfl

end PolycyclicRecognition

end

end OAI
