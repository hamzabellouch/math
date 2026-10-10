import OAI.NumberTheory.Ostmann.Arithmetic.MovingPeriodBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleSizes

namespace OAI

/-! # The residue period for actual four-slot samples -/

namespace Ostmann
open scoped Classical

theorem movingNaturalProduct_le_pow {σ : Type*} (value : σ → ℕ) (P : ℕ)
    (hvalue : ∀ i, value i ≤ P) (slots : List σ) :
    MovingSlotReversal.naturalProduct value slots ≤ P ^ slots.length := by
  induction slots with
  | nil => simp [MovingSlotReversal.naturalProduct]
  | cons i slots ih =>
    simpa only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons,
      List.length_cons, pow_succ, mul_comm] using Nat.mul_le_mul (hvalue i) ih

theorem MovingSlotData.CompensationBound.mono {σ : Type*} {n B C : ℕ}
    {T : MovingSlotData σ n} (value : σ → ℕ) (h : T.CompensationBound value B)
    (hBC : B ≤ C) : T.CompensationBound value C := by
  induction T with
  | leaf => trivial
  | node s CL CR u left right ihL ihR =>
    exact ⟨h.1.trans hBC, ihL h.2.1, ihR h.2.2⟩

/-- Only the four compensation samples at each leaf enter the denominator.
The lengths of the bulk and initial small-prime lists do not enter this bound. -/
theorem buildMovingSlotData_compensation_bound {σ : Type*} (value : σ → ℕ)
    (P : ℕ) (hP : 1 ≤ P) (hvalue : ∀ i, value i ≤ P)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).CompensationBound value (P ^ (4 * 2 ^ n)) := by
  induction samples with
  | leaf => trivial
  | @node n samples left right ihL ihR =>
    have he : 4 * 2 ^ n ≤ 4 * 2 ^ (n + 1) := by rw [pow_succ]; omega
    have hp := Nat.pow_le_pow_right hP he
    refine ⟨?_, (ihL _ _ _).mono value hp, (ihR _ _ _).mono value hp⟩
    apply (movingNaturalProduct_le_pow value P hvalue _).trans
    apply Nat.pow_le_pow_right hP
    have hl := moving_flatten_length_le n (movingCompensationSlots n samples) 4
      (moving_compensation_length n samples)
    exact hl.trans (by rw [pow_succ]; omega)

/-- The concrete common modulus is controlled by the frequency cutoff and
compensation-prime cutoff alone, uniformly in both top giants. -/
theorem movingSample_topPeriod_bound {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (P V : ℕ) (hP : 1 ≤ P) (hV : 1 ≤ V)
    (hvalueP : ∀ i, value i ≤ P) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n)
    (hf : (buildMovingSlotData n t small bulk samples).Frequencies (· ≠ 0))
    (hfreq : (buildMovingSlotData n t small bulk samples).Frequencies (fun s => s.natAbs ≤ V)) :
    movingTopPeriod value hvalue childBound pivotBound
      (buildMovingSlotData n t small bulk samples) hf ≤
        (V * P ^ (4 * 2 ^ n)) ^ (4 * (4 ^ n - 1)) := by
  have hp : 1 ≤ P ^ (4 * 2 ^ n) := Nat.one_le_pow _ _ hP
  have hVB : V ≤ V * P ^ (4 * 2 ^ n) := by nlinarith
  have hPB : P ^ (4 * 2 ^ n) ≤ V * P ^ (4 * 2 ^ n) := by nlinarith
  apply movingTopPeriod_bound value hvalue childBound pivotBound _ hf _ (hV.trans hVB)
  · have hmap {r : ℕ} (T : MovingSlotData σ r)
        (h : T.Frequencies (fun s => s.natAbs ≤ V)) :
        T.Frequencies (fun s => s.natAbs ≤ V * P ^ (4 * 2 ^ n)) := by
      induction T with
      | leaf => exact h.trans hVB
      | node s CL CR u left right ihL ihR => exact ⟨h.1.trans hVB, ihL h.2.1, ihR h.2.2⟩
    exact hmap _ hfreq
  · exact (buildMovingSlotData_compensation_bound value P hP hvalueP n t small bulk samples).mono value hPB

end Ostmann

end OAI
