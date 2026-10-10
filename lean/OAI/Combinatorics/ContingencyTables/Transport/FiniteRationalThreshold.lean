import OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits
import OAI.Combinatorics.ContingencyTables.Machines.FairBits
import OAI.Combinatorics.MatroidCounting.CommonBases

namespace OAI

/-! # A bounded dyadic comparison with a rational acceptance probability -/

namespace ContingencyTables.FairBits

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

def rationalThreshold (k : ℕ) (q : ℚ) : ℕ := ⌊(2:ℚ)^k*q⌋₊

def rationalThresholdMass (k : ℕ) (q : ℚ) : ℚ := rationalThreshold k q/(2:ℚ)^k

abbrev rationalThresholdAccept (k : ℕ) (q : ℚ) (bits : Fin k → Bool) : Prop :=
  (binaryWordEquiv k bits).val < rationalThreshold k q

lemma rationalThreshold_le (k : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    rationalThreshold k q ≤ 2^k := by
  have h := Nat.floor_le (mul_nonneg (by positivity : (0:ℚ) ≤ 2^k) hq0)
  have h' : (rationalThreshold k q:ℚ) ≤ (2:ℚ)^k := by
    change (⌊(2:ℚ)^k*q⌋₊:ℚ) ≤ (2:ℚ)^k
    exact h.trans (by nlinarith [pow_pos (by norm_num : (0:ℚ)<2) k])
  exact_mod_cast h'

lemma rationalThreshold_count (k : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (Finset.univ.filter (fun z : Fin (2^k) => z.val < rationalThreshold k q)).card=
      rationalThreshold k q := by
  rw [Fin.card_filter_val_lt,min_eq_right (rationalThreshold_le k q hq0 hq1)]

/-- The finite coin always rounds downward and loses less than one
code word, including the exact endpoint probabilities zero and one. -/
theorem rationalThreshold_error (k : ℕ) (q : ℚ) (hq : 0 ≤ q) :
    0 ≤ rationalThresholdMass k q ∧ rationalThresholdMass k q ≤ q ∧
      q-rationalThresholdMass k q < 1/(2:ℚ)^k := by
  have hp : (0:ℚ)<2^k := by positivity
  have hlo := Nat.floor_le (mul_nonneg hp.le hq)
  have hhi := Nat.lt_floor_add_one ((2:ℚ)^k*q)
  change 0 ≤ (⌊(2:ℚ)^k*q⌋₊:ℚ)/(2:ℚ)^k ∧
    (⌊(2:ℚ)^k*q⌋₊:ℚ)/(2:ℚ)^k ≤ q ∧
    q-(⌊(2:ℚ)^k*q⌋₊:ℚ)/(2:ℚ)^k < 1/(2:ℚ)^k
  refine ⟨by positivity,?_,?_⟩
  · exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hlo)
  · rw [sub_div' hp.ne',div_lt_div_iff_of_pos_right hp]
    nlinarith

/-- An actual k-bit input realizes the stated rounded probability. -/
theorem rationalThreshold_expectation (k : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    uniformAverage (fun bits : Fin k → Bool =>
      if rationalThresholdAccept k q bits then (1:ℝ) else 0)=
        (rationalThresholdMass k q:ℝ) := by
  have he := uniformAverage_equiv (binaryWordEquiv k)
    (fun z : Fin (2^k) => if z.val < rationalThreshold k q then (1:ℝ) else 0)
  simp only [rationalThresholdAccept]
  rw [he]
  unfold uniformAverage
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,rationalThreshold_count k q hq0 hq1,
    Fintype.card_fin,rationalThresholdMass,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,
    Nat.cast_pow,Nat.cast_ofNat]

end

end ContingencyTables.FairBits

end OAI
