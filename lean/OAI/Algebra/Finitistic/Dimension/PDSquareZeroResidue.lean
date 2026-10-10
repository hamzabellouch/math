import OAI.Algebra.Finitistic.Dimension.PDSquareZero
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Semiprimary

namespace OAI
noncomputable section
namespace LittleFinitistic.PDSquareZero
universe u
variable {A D : Type u} [Ring A] [Ring D]

/-- The radical quotient is unchanged by a square-zero kernel. -/
def residueQuotientEquiv (f : A →+* D) (hf : Function.Surjective f)
    (hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a*b=0) :
    A ⧸ Ring.jacobson A ≃+* D ⧸ Ring.jacobson D := by
  let g := (Ideal.Quotient.mk (Ring.jacobson D)).comp f
  have hk : RingHom.ker g = Ring.jacobson A := by
    ext a
    change Ideal.Quotient.mk (Ring.jacobson D) (f a) = 0 ↔ a ∈ Ring.jacobson A
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change a ∈ Ideal.comap f (Ring.jacobson D) ↔ _
    rw [comap_jacobson f hf hsq]
  exact (Ideal.quotEquivOfEq hk.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := g) (Ideal.Quotient.mk_surjective.comp hf))

@[simp] theorem residueQuotientEquiv_mk (f : A →+* D) (hf : Function.Surjective f)
    (hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a*b=0) (a : A) :
    residueQuotientEquiv f hf hsq (Ideal.Quotient.mk (Ring.jacobson A) a) =
      Ideal.Quotient.mk (Ring.jacobson D) (f a) := by
  simp [residueQuotientEquiv]

/-- The nilpotent ideal annihilates every actual simple left A-module. -/
theorem kernel_annihilates_simple (f : A →+* D)
    (hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a*b=0)
    (S : Type u) [AddCommGroup S] [Module A S] [IsSimpleModule A S]
    (a : A) (ha : a ∈ RingHom.ker f) (s : S) : a • s=0 :=
  Module.mem_annihilator.mp
    (IsSemisimpleModule.jacobson_le_annihilator A S
      (squareZero_le_jacobson (RingHom.ker f) hsq ha)) s

variable {k : Type u} [Field k] [Algebra k D]
variable (X : Type u) [AddCommGroup X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [Module k X]
  [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The exact quotient-ring isomorphism S in Section 6. -/
def squareZeroResidueEquiv :
    TrivSqZeroExt D X ⧸ Ring.jacobson (TrivSqZeroExt D X) ≃+* D ⧸ Ring.jacobson D :=
  residueQuotientEquiv (TrivSqZeroExt.fstHom k D X).toRingHom
    (fun d => ⟨TrivSqZeroExt.inl d, rfl⟩)
    (fun a ha b hb => kernel_square_zero X a b ha hb)

@[simp] theorem squareZeroResidueEquiv_mk (a : TrivSqZeroExt D X) :
    squareZeroResidueEquiv (k := k) X (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk (Ring.jacobson D) a.fst := residueQuotientEquiv_mk _ _ _ _
end LittleFinitistic.PDSquareZero

end

end OAI
