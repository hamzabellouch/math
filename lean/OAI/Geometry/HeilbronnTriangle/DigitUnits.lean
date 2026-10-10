import Mathlib

namespace OAI


namespace Problem355.DigitUnits

open scoped BigOperators

def baseValue (B k : ℕ) (digit : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, digit i * B ^ i

lemma baseValue_succ (B k : ℕ) (digit : ℕ → ℕ) :
    baseValue B (k + 1) digit =
      digit 0 + B * baseValue B k (fun i => digit (i + 1)) := by
  unfold baseValue
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one, pow_succ, Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma baseValue_mod (B k : ℕ) (digit : ℕ → ℕ) (hk : 0 < k) :
    baseValue B k digit % B = digit 0 % B := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [baseValue_succ]
  simp

theorem baseValue_isUnit {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : ℕ → ℕ) (hzero : 0 < digit 0) (hsmall : digit 0 < B) :
    IsUnit (baseValue B k digit : ZMod (B ^ k)) := by
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hB hk).2
  intro hdiv
  have hm := Nat.mod_eq_zero_of_dvd hdiv
  rw [baseValue_mod B k digit hk, Nat.mod_eq_of_lt hsmall] at hm
  omega

theorem baseValue_isUnit_of_digit_bounds {B k L : ℕ} (hB : B.Prime)
    (hk : 0 < k) (hLB : L < B) (digit : ℕ → ℕ)
    (hdigit : ∀ i < k, 1 ≤ digit i ∧ digit i ≤ L) :
    IsUnit (baseValue B k digit : ZMod (B ^ k)) := by
  exact baseValue_isUnit hB hk digit (hdigit 0 hk).1
    (lt_of_le_of_lt (hdigit 0 hk).2 hLB)

lemma count_mod_period {r a : ℕ} (ha : a < r) :
    Nat.count (fun n => n % r = a) r = 1 := by
  rw [Nat.count_eq_card_filter_range]
  have hset : (Finset.range r).filter (fun n => n % r = a) = {a} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, he⟩
      simpa [Nat.mod_eq_of_lt hn] using he
    · rintro rfl
      exact ⟨ha, Nat.mod_eq_of_lt ha⟩
  rw [hset]
  simp

lemma count_mod_mul {r a : ℕ} (ha : a < r) (m : ℕ) :
    Nat.count (fun n => n % r = a) (r * m) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Nat.count_add, ih]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    rw [count_mod_period ha]

theorem card_positive_residue_fiber {r a : ℕ} (ha : a < r) (m : ℕ) :
    ((Finset.Icc 1 (r * m)).filter (fun n => n % r = a)).card = m := by
  have hperiod : Function.Periodic (fun n : ℕ => n % r = a) (r * m) := by
    intro n
    simp [Nat.add_mod]
  have hinterval : Finset.Icc 1 (r * m) = Finset.Ico 1 (1 + r * m) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hinterval, Nat.filter_Ico_card_eq_of_periodic 1 (r * m)
    (fun n => n % r = a) hperiod, count_mod_mul ha]

theorem card_positive_residue_fiber_pow {r a : ℕ} (ha : a < r) :
    ((Finset.Icc 1 (r ^ 10)).filter (fun n => n % r = a)).card = r ^ 9 := by
  rw [show r ^ 10 = r * r ^ 9 by ring]
  exact card_positive_residue_fiber ha (r ^ 9)

theorem card_positive_zmod_fiber {r : ℕ} [NeZero r] (a : ZMod r) (m : ℕ) :
    ((Finset.Icc 1 (r * m)).filter (fun n : ℕ => (n : ZMod r) = a)).card = m := by
  have heq (n : ℕ) : (n : ZMod r) = a ↔ n % r = a.val := by
    constructor
    · intro h
      simpa using congrArg ZMod.val h
    · intro h
      apply ZMod.val_injective r
      simpa using h
  simp_rw [heq]
  exact card_positive_residue_fiber a.val_lt m

def digitFiber (r m : ℕ) (a : ZMod r) : Finset ℕ :=
  (Finset.Icc 1 (r * m)).filter (fun n : ℕ => (n : ZMod r) = a)

noncomputable def digitFiberEquiv {r : ℕ} [NeZero r] (a : ZMod r) (m : ℕ) :
    Fin m ≃ ↥(digitFiber r m a) :=
  (Fintype.equivFinOfCardEq (by
    exact (Fintype.card_coe (digitFiber r m a)).trans (card_positive_zmod_fiber a m))).symm

lemma digitFiberEquiv_bounds {r : ℕ} [NeZero r] (a : ZMod r) (m : ℕ) (i : Fin m) :
    1 ≤ (digitFiberEquiv a m i).val ∧ (digitFiberEquiv a m i).val ≤ r * m ∧
      ((digitFiberEquiv a m i).val : ZMod r) = a := by
  have h := (digitFiberEquiv a m i).property
  simpa only [digitFiber, Finset.mem_filter, Finset.mem_Icc, and_assoc] using h

end Problem355.DigitUnits

end OAI
