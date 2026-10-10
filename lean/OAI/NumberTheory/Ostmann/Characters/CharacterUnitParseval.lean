import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import OAI.NumberTheory.Ostmann.Characters.PrimitiveCharacterSieve

namespace OAI

/-! # Parseval on the full group of Dirichlet characters

The complete unit-group orthogonality is needed before restricting to primitive
characters; applying Cauchy--Schwarz separately would lose the conductor.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

 theorem character_unit_gram {q : ℕ} [NeZero q] (u v : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q, χ u * star (χ v)) =
      if u = v then (q.totient : ℂ) else 0 := by
  have hs (χ : DirichletCharacter ℂ q) : star (χ (v : ZMod q)) = χ ((v : ZMod q)⁻¹) := by
    rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]
    rw [ZMod.inv_coe_unit]
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, χ ((v : ZMod q)⁻¹) * χ u := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [hs χ, mul_comm]
    _ = _ := by
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ v.isUnit]
      congr 1
      exact propext ⟨fun h => (Units.val_injective h).symm,
        fun h => congrArg Units.val h.symm⟩

 theorem character_unit_parseval {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2) =
      (q.totient : ℝ) * ∑ u : (ZMod q)ˣ, ‖f u‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (b := ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
    f u * star (f v) * (∑ χ : DirichletCharacter ℂ q, χ u * star (χ v)))
  · apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    simp only [starRingEnd_apply]
    ring
  · simp_rw [character_unit_gram]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    apply Finset.sum_congr rfl
    intro u _
    simp only [starRingEnd_apply]
    ring

end Ostmann

end OAI
