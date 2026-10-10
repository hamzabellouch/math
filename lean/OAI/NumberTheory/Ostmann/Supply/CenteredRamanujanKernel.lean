import OAI.NumberTheory.Ostmann.Quadratic.KernelCoordinateIdentity

namespace OAI

/-! # The local Ramanujan identity for the centered-coordinate budget -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem centeredPoint_pairing {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ S) :
    (∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
      centeredSupportProjection S (residuePointVector b) x) =
        (if a = b then 1 else 0) - (S.card : ℂ)⁻¹ := by
  rw [centeredSupportProjection_pairing_range]
  simp [centeredSupportProjection, residuePointVector, finiteSupportMean, ha, hb, eq_comm]

theorem nonzero_character_difference_sum {p : ℕ} [NeZero p] (a b : ZMod p) :
    (∑ h ∈ Finset.univ.erase 0, ZMod.stdAddChar (h * (a - b))) =
      (if a = b then (p : ℂ) else 0) - 1 := by
  have he := Finset.sum_erase_add Finset.univ (fun h => ZMod.stdAddChar (h * (a - b)))
    (Finset.mem_univ (0 : ZMod p))
  rw [AddChar.sum_mulShift (a - b) (ZMod.isPrimitive_stdAddChar p)] at he
  simp only [zero_mul, AddChar.map_zero_eq_one, ZMod.card, sub_eq_zero] at he
  by_cases hab : a = b <;> simpa only [hab, ite_true, ite_false, Nat.cast_zero] using
    eq_sub_of_add_eq he

theorem centeredRamanujanKernel {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ S) :
    (∑ h ∈ Finset.univ.erase 0, ZMod.stdAddChar (h * (a - b))) =
      ((p : ℂ) / S.card - 1) + p *
        ∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
          centeredSupportProjection S (residuePointVector b) x := by
  rw [nonzero_character_difference_sum, centeredPoint_pairing S a b ha hb]
  split_ifs <;> ring

end Ostmann

end OAI
