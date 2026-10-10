import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators MonoidAlgebra Classical

namespace BinaryCoordinateSweeps.Irrep
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

def subrepresentationCongr (e : H ≃* G) (ρ : Representation ℂ G V) :
    Subrepresentation ρ ≃o Subrepresentation (ρ.comp e.toMonoidHom) where
  toFun U := ⟨U.toSubmodule, fun h _ hv => U.apply_mem_toSubmodule (e h) hv⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (e.symm g) hv
    change ρ (e (e.symm g)) v ∈ U.toSubmodule at h
    rwa [e.apply_symm_apply] at h⟩
  left_inv U := by rfl
  right_inv U := by rfl
  map_rel_iff' := Iff.rfl

lemma irreducible_comp_equiv (e : H ≃* G) (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Representation.IsIrreducible (k := ℂ) (G := H) (V := V) (ρ.comp e.toMonoidHom) :=
  (subrepresentationCongr e ρ).isSimpleOrder_iff.mp inferInstance

variable [Fintype G] [FiniteDimensional ℂ V]

def classCharacter (ρ : Representation ℂ G V) : ConjClasses G → ℂ :=
  Quotient.lift ρ.character (fun g h hgh => by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hgh
    exact (ρ.char_conj g c).symm)

omit [Fintype G] [FiniteDimensional ℂ V] in
@[simp] lemma classCharacter_mk (ρ : Representation ℂ G V) (g : G) :
    classCharacter ρ (ConjClasses.mk g) = ρ.character g := rfl

def classPairRight (f : ConjClasses G → ℂ) : (ConjClasses G → ℂ) →ₗ[ℂ] ℂ where
  toFun h := (Nat.card G : ℂ)⁻¹ * ∑ g, h (ConjClasses.mk g) * f (ConjClasses.mk g⁻¹)
  map_add' h k := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
  map_smul' a h := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show (∑ g : G, a * h (ConjClasses.mk g) * f (ConjClasses.mk g⁻¹)) =
      a * ∑ g : G, h (ConjClasses.mk g) * f (ConjClasses.mk g⁻¹) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
    ring

lemma classPair_character_self (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    classPairRight (classCharacter ρ) (classCharacter ρ) = 1 := by
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  have he : Nonempty (Representation.Equiv ρ ρ) := ⟨Representation.Equiv.refl ρ⟩
  simpa [classPairRight, he] using Representation.char_orthonormal ρ ρ

lemma classPair_characters {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    classPairRight (classCharacter σ) (classCharacter ρ) =
      if Nonempty (Representation.Equiv σ ρ) then 1 else 0 := by
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  exact Representation.char_orthonormal ρ σ

end BinaryCoordinateSweeps.Irrep

end

end OAI
