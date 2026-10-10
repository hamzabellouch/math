import OAI.GroupTheory.PolycyclicRecognition.Algebra.AscendingCoinvariantRelations
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubgroupInductionExact

namespace OAI

/-! # A common ambient representation for subgroup induction

All the induced restrictions of a fixed coefficient are quotients of the same
module. The relations increase with the subgroup. The commuting right action
on the group-ring factor gives the actual ambient group action.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (A : Rep.{0} ℤ G)

def inductionAmbientAction : Representation ℤ G (ℤ[G] ⊗[ℤ] A) where
  toFun g := (MonoidAlgebra.mapDomainLinearMap ℤ ℤ (fun x : G => x * g⁻¹)).rTensor A
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_inv_rev, mul_assoc]

abbrev inductionAmbient : Rep ℤ G := Rep.of (inductionAmbientAction A)

abbrev inductionDiagonalAction : Representation ℤ G (ℤ[G] ⊗[ℤ] A) :=
  Representation.tprod (Representation.leftRegular ℤ G) A.ρ

theorem inductionAmbient_diagonal_commute (g h : G) :
    (inductionAmbientAction A g).comp (inductionDiagonalAction A h) =
      (inductionDiagonalAction A h).comp (inductionAmbientAction A g) := by
  ext x a
  simp [inductionAmbientAction, inductionDiagonalAction, mul_assoc]

theorem inductionRelations_invariant (H : Subgroup G) :
    RepresentationInvariant (inductionAmbient A)
      (subgroupCoinvariantRelations (inductionDiagonalAction A) H) := by
  intro g x hx
  change inductionAmbientAction A g x ∈
    subgroupCoinvariantRelations (inductionDiagonalAction A) H
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨h, v⟩, rfl⟩ := hx
    change inductionAmbientAction A g ((inductionDiagonalAction A h.val) v - v) ∈
      subgroupCoinvariantRelations (inductionDiagonalAction A) H
    rw [map_sub]
    have he := LinearMap.congr_fun (inductionAmbient_diagonal_commute A g h.val) v
    change inductionAmbientAction A g (inductionDiagonalAction A h.val v) =
      inductionDiagonalAction A h.val (inductionAmbientAction A g v) at he
    rw [he]
    exact Coinvariants.sub_mem_ker
      (ρ := (inductionDiagonalAction A).comp H.subtype) h (inductionAmbientAction A g v)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    change inductionAmbientAction A g (r • x) ∈
      subgroupCoinvariantRelations (inductionDiagonalAction A) H
    rw [map_smul]
    exact Submodule.smul_mem _ r hx

/-- The quotient action is the induction action, including its inverse convention. -/
def inductionAmbientQuotientIso (H : Subgroup G) :
    Rep.quotient (inductionAmbient A)
      (subgroupCoinvariantRelations (inductionDiagonalAction A) H)
      (inductionRelations_invariant A H) ≅ Rep.ind H.subtype (Rep.res H.subtype A) where
  hom := Rep.ofHom ⟨LinearMap.id, fun g => by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl⟩
  inv := Rep.ofHom ⟨LinearMap.id, fun g => by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl⟩
  hom_inv_id := by apply Rep.hom_ext; rfl
  inv_hom_id := by apply Rep.hom_ext; rfl

end PolycyclicRecognition

end

end OAI
