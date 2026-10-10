import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.Algebra.TrivSqZeroExt.Basic

namespace OAI
noncomputable section
namespace LittleFinitistic.PDSquareZero
open Submodule
universe u
variable {A D : Type u} [Ring A] [Ring D]

/-- A square-zero ideal lies in the actual noncommutative Jacobson radical. -/
theorem squareZero_le_jacobson (I : Ideal A)
    (hI : ∀ a ∈ I, ∀ b ∈ I, a*b=0) : I ≤ Ring.jacobson A := by
  apply le_sInf
  intro L hL
  by_contra hn
  have hlt : L < L ⊔ I := lt_of_le_of_ne le_sup_left (fun he => hn (he ▸ le_sup_right))
  have htop : L ⊔ I = ⊤ := hL.2 _ hlt
  have hone : (1 : A) ∈ L ⊔ I := htop.symm ▸ mem_top
  obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.mp hone
  have hxx : x*x=0 := hI x hx x hx
  have hleq : l=1-x := eq_sub_iff_add_eq.mpr hlx
  have heq : (1+x)*l=1 := by
    simp [hleq, mul_sub, add_mul, hxx]
  have h1 : (1 : A) ∈ L := heq ▸ L.smul_mem (1+x) hl
  exact hL.1 (Ideal.eq_top_of_isUnit_mem L h1 isUnit_one)

/-- A surjection with square-zero kernel pulls back the ring radical exactly. -/
theorem comap_jacobson (f : A →+* D) (hf : Function.Surjective f)
    (hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a*b=0) :
    Ideal.comap f (Ring.jacobson D) = Ring.jacobson A := by
  let : RingHomSurjective f := ⟨hf⟩
  exact Module.comap_jacobson_of_ker_le (f := f.toSemilinearMap) hf
    (squareZero_le_jacobson (RingHom.ker f) hsq)

variable {k : Type u} [Field k] [Algebra k D]
variable (X : Type u) [AddCommGroup X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [Module k X]
  [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The manuscript's actual split square-zero projection has square-zero kernel. -/
theorem kernel_square_zero (a b : TrivSqZeroExt D X)
    (ha : a ∈ RingHom.ker (TrivSqZeroExt.fstHom k D X).toRingHom)
    (hb : b ∈ RingHom.ker (TrivSqZeroExt.fstHom k D X).toRingHom) : a*b=0 := by
  have ha0 : a.fst=0 := ha
  have hb0 : b.fst=0 := hb
  apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ha0, hb0]

/-- rad(D ⋉ X) is the preimage of rad(D), hence consists precisely of pairs
whose D coordinate is in rad(D). The X coordinate is unrestricted. -/
theorem radical_eq_comap :
    Ring.jacobson (TrivSqZeroExt D X) =
      Ideal.comap (TrivSqZeroExt.fstHom k D X).toRingHom (Ring.jacobson D) := by
  symm
  apply comap_jacobson
  · intro d; exact ⟨TrivSqZeroExt.inl d, rfl⟩
  · exact fun a ha b hb => kernel_square_zero X a b ha hb

/-- Every simple A-module is annihilated by the square-zero ideal, as used
when identifying the simple modules with those over D. -/
theorem square_zero_ideal_le_radical :
    RingHom.ker (TrivSqZeroExt.fstHom k D X).toRingHom ≤ Ring.jacobson (TrivSqZeroExt D X) :=
  squareZero_le_jacobson _ (fun a ha b hb => kernel_square_zero X a b ha hb)
end LittleFinitistic.PDSquareZero

end

end OAI
