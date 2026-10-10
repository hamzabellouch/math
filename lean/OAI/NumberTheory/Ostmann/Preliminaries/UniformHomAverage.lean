import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp

namespace OAI

/-! # Uniform finite group samples push forward uniformly through a homomorphism -/

namespace Ostmann
open scoped Classical BigOperators

theorem uniform_hom_average {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f) (F : B → ℂ) :
    (Fintype.card A : ℂ)⁻¹ * (∑ a, F (f a)) =
      (Fintype.card B : ℂ)⁻¹ * ∑ b, F b := by
  have hcard (b : B) : Fintype.card {a : A // f a = b} = Fintype.card f.ker :=
    Fintype.card_congr (f.fiberEquivKerOfSurjective hf b)
  have htotal : Fintype.card A = Fintype.card B * Fintype.card f.ker := by
    calc
      _ = Fintype.card (Σ b : B, {a : A // f a = b}) :=
        (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
      _ = _ := by simp only [Fintype.card_sigma, hcard, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.cast_id]
  have hsum : (∑ a, F (f a)) = (Fintype.card f.ker : ℂ) * ∑ b, F b := by
    rw [← Fintype.sum_fiberwise f (fun a => F (f a))]
    simp only [show ∀ b (a : {a : A // f a = b}), F (f a.val) = F b from
      fun _ a => congrArg F a.property, Finset.sum_const, Finset.card_univ,
      hcard, nsmul_eq_mul, ← Finset.mul_sum]
  rw [hsum, htotal, Nat.cast_mul]
  have hK : (Fintype.card f.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

end Ostmann

end OAI
