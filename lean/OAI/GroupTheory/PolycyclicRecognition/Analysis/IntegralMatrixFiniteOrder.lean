import OAI.GroupTheory.PolycyclicRecognition.Algebra.ThreeCongruenceMatrix
import Mathlib.GroupTheory.OrderOfElement

namespace OAI

/-! # Reduction modulo three is faithful on finite integral matrix groups -/
noncomputable section
namespace PolycyclicRecognition
open Matrix
variable {I : Type} [Fintype I] [DecidableEq I]

theorem matrixMod_eq_one_iff (m : ℕ) (A : Matrix I I ℤ) :
    matrixMod m A = 1 ↔ ∀ i j, (m : ℤ) ∣ (A - 1) i j := by
  have h : matrixMod m A = 1 ↔ matrixMod m (A - 1) = 0 := by
    rw [map_sub, map_one, sub_eq_zero]
  rw [h]
  constructor
  · intro hz i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
    exact congrArg (fun M : Matrix I I (ZMod m) => M i j) hz
  · intro hz
    ext i j
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr (hz i j)

theorem integerMatrix_eq_one_of_finite_order_three_congruence
    (A : Matrix I I ℤ) (hfin : IsOfFinOrder A)
    (h3 : ∀ i j, (3 : ℤ) ∣ (A - 1) i j) : A = 1 := by
  by_contra hne
  have hon : orderOf A ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hon
  let B := A ^ (orderOf A / p)
  have ho : orderOf B = p := orderOf_pow_orderOf_div (ne_of_gt hfin.orderOf_pos) hpd
  have hpw : B ^ p = 1 := by rw [← ho]; exact pow_orderOf_eq_one B
  have hm : matrixMod 3 B = 1 := by
    dsimp only [B]
    rw [map_pow, (matrixMod_eq_one_iff 3 A).mpr h3, one_pow]
  have he := integerMatrix_eq_one_of_prime_order_three_congruence B p hp hpw
    ((matrixMod_eq_one_iff 3 B).mp hm)
  have hbad : p = 1 := by rw [← ho, he, orderOf_one]
  exact hp.ne_one hbad

theorem finite_integral_matrix_representation_card_le
    {G : Type} [Group G] [Finite G] (ρ : G →* Matrix I I ℤ)
    (hρ : Function.Injective ρ) : Nat.card G ≤ 3 ^ (Fintype.card I * Fintype.card I) := by
  let f : G →* Matrix I I (ZMod 3) := (matrixMod 3).toMonoidHom.comp ρ
  have hf : Function.Injective f := by
    intro x y hxy
    have hz : f (x⁻¹ * y) = 1 := by
      rw [map_mul, ← hxy, ← map_mul, inv_mul_cancel, map_one]
    have hfin : IsOfFinOrder (ρ (x⁻¹ * y)) :=
      (isOfFinOrder_of_finite (x⁻¹ * y)).mono (orderOf_map_dvd ρ (x⁻¹ * y))
    have he : ρ (x⁻¹ * y) = 1 :=
      integerMatrix_eq_one_of_finite_order_three_congruence _ hfin
        ((matrixMod_eq_one_iff 3 _).mp hz)
    have hg : x⁻¹ * y = 1 := hρ (he.trans ρ.map_one.symm)
    exact inv_mul_eq_one.mp hg
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Matrix, Fintype.card_fun, ZMod.card, ← pow_mul] using hc

end PolycyclicRecognition

end

end OAI
