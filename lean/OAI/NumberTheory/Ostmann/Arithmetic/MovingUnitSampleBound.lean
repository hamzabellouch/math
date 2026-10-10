import OAI.NumberTheory.Ostmann.Arithmetic.MovingUnitPeriodBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSmallFrequencyUnits

namespace OAI

/-! # The actual sampled regular lists in the full unit-period estimate -/

namespace Ostmann
open scoped Classical

def MovingSlotData.RegularLengthLE {σ : Type*} (D : ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, T@(.leaf _ _) => T.regularSlots.length ≤ D
  | _, T@(.node _ _ _ _ left right) =>
      T.regularSlots.length ≤ D ∧ left.RegularLengthLE D ∧ right.RegularLengthLE D

theorem MovingSlotData.RegularLengthLE.mono {σ : Type*} {n D E : ℕ}
    {T : MovingSlotData σ n} (h : T.RegularLengthLE D) (hDE : D ≤ E) :
    T.RegularLengthLE E := by
  induction T with
  | leaf => exact h.trans hDE
  | node s CL CR U left right ihL ihR =>
    exact ⟨h.1.trans hDE, ihL h.2.1, ihR h.2.2⟩

theorem buildMovingSlotData_regular_length {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n)
    (A B : ℕ) (hsmall : MovingLeafLengthLE n small A) (hbulk : MovingLeafLengthLE n bulk B) :
    (buildMovingSlotData n t small bulk samples).RegularLengthLE (2 ^ n * (A + B + 4 * n)) := by
  induction samples generalizing A B with
  | leaf =>
    simpa only [buildMovingSlotData, MovingSlotData.RegularLengthLE, MovingSlotData.regularSlots,
      flattenMovingSlots, List.length_append, pow_zero, Nat.mul_zero, Nat.add_zero, one_mul] using
      Nat.add_le_add hsmall hbulk
  | @node n samples left right ihL ihR =>
    have hleft := ihL t.2.1 (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.1)
      bulk.1 (4 + A) B (moving_append_length_le n _ _ 4 A
        (moving_compensation_length n samples) hsmall.1) hbulk.1
    have hright := ihR t.2.2 (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.2)
      bulk.2 (4 + A) B (moving_append_length_le n _ _ 4 A
        (moving_compensation_length n samples) hsmall.2) hbulk.2
    have hD : 2 ^ n * (4 + A + B + 4 * n) ≤ 2 ^ (n + 1) * (A + B + 4 * (n + 1)) := by
      rw [show 4 + A + B + 4 * n = A + B + 4 * (n + 1) by omega]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨?_, hleft.mono hD, hright.mono hD⟩
    have hp := (buildMovingSlotData_regular_perm (n + 1) t small bulk (.node samples left right)).length_eq
    change (buildMovingSlotData (n + 1) t small bulk (.node samples left right)).regularSlots.length ≤ _
    rw [hp, List.length_append]
    have hs := moving_flatten_length_le (n + 1) small A hsmall
    have hb := moving_flatten_length_le (n + 1) bulk B hbulk
    exact (Nat.add_le_add hs hb).trans (by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (by omega))

theorem MovingSlotData.RegularLengthLE.product_bound {σ : Type*} {n D : ℕ}
    (T : MovingSlotData σ n) (hT : T.RegularLengthLE D) (value : σ → ℕ)
    (P : ℕ) (hP : 1 ≤ P) (hvalue : ∀ i, value i ≤ P) :
    T.RegularBound value (P ^ D) := by
  induction T with
  | leaf s regular =>
    exact (movingNaturalProduct_le_pow value P hvalue regular).trans (Nat.pow_le_pow_right hP hT)
  | node s CL CR U left right ihL ihR =>
    exact ⟨(movingNaturalProduct_le_pow value P hvalue (CL ++ CR)).trans
      (Nat.pow_le_pow_right hP hT.1), ihL hT.2.1, ihR hT.2.2⟩

theorem MovingSlotData.RegularBound.mono {σ : Type*} {n B C : ℕ}
    (T : MovingSlotData σ n) (value : σ → ℕ) (h : T.RegularBound value B) (hBC : B ≤ C) :
    T.RegularBound value C := by
  induction T with
  | leaf => exact h.trans hBC
  | node s CL CR U left right ihL ihR => exact ⟨h.1.trans hBC, ihL h.2.1, ihR h.2.2⟩

/-- A concrete upper bound retaining the number of original small and bulk
slots. Compensation contributes exactly four labels per bottom leaf per level. -/
theorem movingSample_unitPeriod_bound {σ : Type*} (value : σ → ℕ)
    (P V : ℕ) (hP : 1 ≤ P) (hV : 1 ≤ V) (hvalue : ∀ i, value i ≤ P)
    (outside : List ℕ) (hout : 1 ≤ outside.prod)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (A B : ℕ)
    (hsmall : MovingLeafLengthLE n small A) (hbulk : MovingLeafLengthLE n bulk B)
    (hfreq : (buildMovingSlotData n t small bulk samples).Frequencies (fun s => s.natAbs ≤ V)) :
    (movingGiantUnitPeriod value outside (buildMovingSlotData n t small bulk samples)).natAbs ≤
      (V * P ^ (2 ^ n * (A + B + 4 * n) + 4 * 2 ^ n) * outside.prod) ^ movingGiantUnitExponent n := by
  let D := 2 ^ n * (A + B + 4 * n)
  let K := V * P ^ (D + 4 * 2 ^ n) * outside.prod
  have hp : 1 ≤ P ^ (D + 4 * 2 ^ n) := Nat.one_le_pow _ _ hP
  have hvK : V ≤ K := by
    change V ≤ V * P ^ (D + 4 * 2 ^ n) * outside.prod
    calc
      V = V * 1 * 1 := by simp
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left V hp) hout
  have hpK : P ^ (D + 4 * 2 ^ n) ≤ K := by
    change P ^ (D + 4 * 2 ^ n) ≤ V * P ^ (D + 4 * 2 ^ n) * outside.prod
    calc
      _ = 1 * P ^ (D + 4 * 2 ^ n) * 1 := by simp
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hV) hout
  have hoK : outside.prod ≤ K := by
    change outside.prod ≤ V * P ^ (D + 4 * 2 ^ n) * outside.prod
    calc
      _ = (1 * 1) * outside.prod := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul hV hp)
  have hD : P ^ D ≤ K := (Nat.pow_le_pow_right hP (Nat.le_add_right _ _)).trans hpK
  have hc : P ^ (4 * 2 ^ n) ≤ K :=
    (Nat.pow_le_pow_right hP (Nat.le_add_left _ _)).trans hpK
  exact movingGiantUnitPeriod_bound value outside _ K
    (hfreq.mono (fun _ hs => hs.trans hvK))
    ((buildMovingSlotData_compensation_bound value P hP hvalue n t small bulk samples).mono value hc)
    (MovingSlotData.RegularBound.mono _ value
      (MovingSlotData.RegularLengthLE.product_bound _
        (buildMovingSlotData_regular_length n t small bulk samples A B hsmall hbulk) value P hP hvalue) hD) hoK

end Ostmann

end OAI
