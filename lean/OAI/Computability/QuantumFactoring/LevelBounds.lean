import Mathlib
import OAI.Computability.QuantumFactoring.LevelCounts

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma div_lower_power_two {r v t : ℕ} (hdiv : 2^v ∣ r) (ht : t ≤ v) :
    r / 2^(v-t) = 2^t * (r / 2^v) := by
  have hpow : 2^(v-t) * 2^t = 2^v := by rw [← pow_add, Nat.sub_add_cancel ht]
  calc
    r / 2^(v-t) = (2^(v-t) * (2^t * (r / 2^v))) / 2^(v-t) := by
      rw [← mul_assoc, hpow, Nat.mul_div_cancel' hdiv]
    _ = 2^t * (r / 2^v) := Nat.mul_div_right _ (by positivity)

/-- The traditional cyclic-group level law u, u, 2u, 4u, ... . -/
theorem levelCount_closed (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    levelCount G t = if t = 0 then Fintype.card G / 2^padicValNat 2 (Fintype.card G)
      else if t ≤ padicValNat 2 (Fintype.card G) then
        2^(t-1) * (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) else 0 := by
  have hr : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hd : 2^padicValNat 2 (Fintype.card G) ∣ Fintype.card G :=
    (padicValNat_dvd_iff_le hr).mpr le_rfl
  rw [levelCount_cyclic]
  by_cases ht : t = 0
  · simp [ht]
  · simp only [ht, ↓reduceIte]
    by_cases htv : t ≤ padicValNat 2 (Fintype.card G)
    · rw [ite_eq_left htv, div_lower_power_two hd htv,
        div_lower_power_two hd (by omega : t-1 ≤ padicValNat 2 (Fintype.card G))]
      have he : t = (t-1)+1 := by omega
      nth_rw 1 [he]
      rw [pow_succ]
      have heq : 2 ^ (t-1) * 2 * (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) =
          2 * (2^(t-1) * (Fintype.card G / 2^padicValNat 2 (Fintype.card G))) := by ring
      rw [heq]
      omega
    · have hv : padicValNat 2 (Fintype.card G) ≤ t-1 := by omega
      simp [htv, Nat.sub_eq_zero_of_le hv, Nat.sub_eq_zero_of_le (by omega :
        padicValNat 2 (Fintype.card G) ≤ t)]

/-- No particular level has more than half the elements of a cyclic group of
even order, including the lowest level and the unique top level. -/
theorem two_mul_levelCount_le (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G]
    (heven : 2 ∣ Fintype.card G) (t : ℕ) : 2 * levelCount G t ≤ Fintype.card G := by
  have hr : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hv : 1 ≤ padicValNat 2 (Fintype.card G) := by
    apply (padicValNat_dvd_iff_le hr).mp
    simpa using heven
  have hd : 2^padicValNat 2 (Fintype.card G) ∣ Fintype.card G :=
    (padicValNat_dvd_iff_le hr).mpr le_rfl
  have hrw : 2^padicValNat 2 (Fintype.card G) *
      (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) = Fintype.card G :=
    Nat.mul_div_cancel' hd
  rw [levelCount_closed]
  by_cases ht : t = 0
  · rw [ite_eq_left ht]
    calc
      _ ≤ 2^padicValNat 2 (Fintype.card G) *
          (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) :=
        Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hv)
      _ = _ := hrw
  · rw [ite_eq_right ht]
    by_cases htv : t ≤ padicValNat 2 (Fintype.card G)
    · rw [ite_eq_left htv, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ t)]
      calc
        _ ≤ 2^padicValNat 2 (Fintype.card G) *
            (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega : 0 < 2) htv)
        _ = _ := hrw
    · simp [htv]

end ExactQuantumFactoring


end

end OAI
