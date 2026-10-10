import OAI.GroupTheory.PolycyclicRecognition.Algebra.MonoidRingOrbitSpan
import OAI.GroupTheory.PolycyclicRecognition.Algebra.OneSidedOrbitAscendingBase
import Mathlib.RepresentationTheory.Basic

namespace OAI

/-! # A finite monoid module supplies the ascending base

The module action uses the nonnegative iterates of the inverse automorphism.
Thus its finite generation has the required direction, unlike finite
generation over the Laurent group ring.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {M : Type} [AddCommGroup M]

def integralLinearMulAut (α : M ≃ₗ[ℤ] M) : MulAut (Multiplicative M) :=
  α.toAddEquiv.toMultiplicative

theorem integralLinearMulAut_pow (α : M ≃ₗ[ℤ] M) (n : ℕ) (x : M) :
    (integralLinearMulAut α ^ n) (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd ((α.toLinearMap ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, pow_succ', Module.End.mul_apply]
    rfl

def inverseIterateRepresentation (α : M ≃ₗ[ℤ] M) :
    Representation ℤ (Multiplicative ℕ) M where
  toFun n := α.symm.toLinearMap ^ n.toAdd
  map_one' := pow_zero _
  map_mul' _ _ := pow_add _ _ _

theorem monoidModule_ascendingBase (α : M ≃ₗ[ℤ] M)
    [Module.Finite ℤ[Multiplicative ℕ] (inverseIterateRepresentation α).asModule] :
    HasFinitelyGeneratedAscendingBase (integralLinearMulAut α) := by
  classical
  let ρ := inverseIterateRepresentation α
  obtain ⟨s, hs⟩ := exists_finite_monoidOrbitSpan (Q := Multiplicative ℕ) (M := ρ.asModule)
  let ψ : ρ.asModule → Multiplicative M := fun x => Multiplicative.ofAdd (ρ.asModuleEquiv x)
  let t := s.image ψ
  let C : Subgroup (Multiplicative M) := Subgroup.closure (t : Set (Multiplicative M))
  have hC : C.FG := ⟨t, rfl⟩
  let β := integralLinearMulAut α
  let D := positiveOrbitSubgroup β⁻¹ C
  let W : Submodule ℤ ρ.asModule :=
    D.toAddSubgroup.toIntSubmodule.comap ρ.asModuleEquiv.toLinearMap
  have ho : monoidOrbitSet (Q := Multiplicative ℕ) (s : Set ρ.asModule) ⊆ W := by
    rintro y ⟨n, x, hx, rfl⟩
    change Multiplicative.ofAdd (ρ.asModuleEquiv (MonoidAlgebra.of ℤ (Multiplicative ℕ) n • x)) ∈ D
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
    change Multiplicative.ofAdd ((α.symm.toLinearMap ^ n.toAdd) (ρ.asModuleEquiv x)) ∈ D
    rw [← integralLinearMulAut_pow]
    apply (le_iSup (fun k : ℕ => C.map ((β⁻¹) ^ k).toMonoidHom) n.toAdd)
    exact ⟨ψ x, Subgroup.subset_closure (Finset.mem_image_of_mem ψ hx), rfl⟩
  have hW : (⊤ : Submodule ℤ ρ.asModule) ≤ W := by
    rw [← hs]
    exact Submodule.span_le.mpr ho
  have hD : D = ⊤ := by
    apply top_unique
    intro x _
    exact hW (x := ρ.asModuleEquiv.symm x.toAdd) Submodule.mem_top
  exact ascendingBase_of_oneSided_orbit β C hC hD

end PolycyclicRecognition

end

end OAI
