import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

namespace EulerPrimeLaw

noncomputable def incrementProbability (p : ℝ) : ℝ := 1 / (p - 1) ^ 2
noncomputable def geometricMass (p : ℝ) (j : ℕ) : ℝ := (1 - 1 / p) * (1 / p) ^ j
noncomputable def bernoulliMass (p : ℝ) (b : Bool) : ℝ :=
  if b then incrementProbability p else 1 - incrementProbability p
noncomputable def eulerMass (p : ℝ) : ℕ → ℝ
  | 0 => (p - 2) / (p - 1)
  | j + 1 => (1 / p) ^ (j + 1)

abbrev Sample := Bool × ℕ
noncomputable def jointMass (p : ℝ) (s : Sample) : ℝ :=
  bernoulliMass p s.1 * geometricMass p s.2
def lowerExponent (s : Sample) : ℕ := s.2
def upperExponent (s : Sample) : ℕ := s.2 + if s.1 then 1 else 0

variable {p : ℝ} (hp : 2 ≤ p)
include hp

lemma reciprocal_nonneg : 0 ≤ 1 / p := by positivity
lemma reciprocal_lt_one : 1 / p < 1 := (div_lt_one (by linarith)).2 (by linarith)
omit hp in
lemma incrementProbability_nonneg : 0 ≤ incrementProbability p := by
  unfold incrementProbability
  positivity
lemma incrementProbability_le_one : incrementProbability p ≤ 1 := by
  have h : 1 ≤ (p - 1) ^ 2 := by nlinarith
  exact (div_le_one (by positivity : 0 < (p - 1) ^ 2)).2 h

lemma geometricMass_nonneg (j : ℕ) : 0 ≤ geometricMass p j :=
  mul_nonneg (sub_nonneg.mpr (reciprocal_lt_one hp).le)
    (pow_nonneg (reciprocal_nonneg hp) j)
lemma bernoulliMass_nonneg (b : Bool) : 0 ≤ bernoulliMass p b := by
  cases b <;> simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr (incrementProbability_le_one hp)
  · exact incrementProbability_nonneg (p := p)
lemma jointMass_nonneg (s : Sample) : 0 ≤ jointMass p s :=
  mul_nonneg (bernoulliMass_nonneg hp s.1) (geometricMass_nonneg hp s.2)
lemma eulerMass_nonneg (j : ℕ) : 0 ≤ eulerMass p j := by
  cases j with
  | zero => exact div_nonneg (by linarith) (by linarith)
  | succ j => exact pow_nonneg (reciprocal_nonneg hp) _

theorem geometricMass_hasSum : HasSum (geometricMass p) 1 := by
  have h := (hasSum_geometric_of_lt_one (reciprocal_nonneg hp)
    (reciprocal_lt_one hp)).mul_left (1 - 1 / p)
  change HasSum (fun j : ℕ => (1 - 1 / p) * (1 / p) ^ j) 1
  convert! h using 1
  exact (mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr (reciprocal_lt_one hp)))).symm

omit hp in
lemma bernoulliMass_hasSum : HasSum (bernoulliMass p) 1 := by
  convert hasSum_fintype (bernoulliMass p) using 1
  simp [bernoulliMass]

lemma jointMass_summable : Summable (jointMass p) :=
  (bernoulliMass_hasSum (p := p)).summable.mul_of_nonneg
    (geometricMass_hasSum hp).summable (bernoulliMass_nonneg hp) (geometricMass_nonneg hp)

theorem jointMass_hasSum : HasSum (jointMass p) 1 := by
  apply (jointMass_summable hp).hasSum_iff.mpr
  rw [(jointMass_summable hp).tsum_prod]
  simp only [jointMass, tsum_mul_left, (geometricMass_hasSum hp).tsum_eq, mul_one]
  exact (bernoulliMass_hasSum (p := p)).tsum_eq

lemma event_summable (A : Sample → Prop) [DecidablePred A] :
    Summable (fun s => if A s then jointMass p s else 0) := by
  apply (jointMass_summable hp).of_nonneg_of_le
  · intro s; split_ifs <;> simp_all only [le_refl, jointMass_nonneg hp]
  · intro s; split_ifs <;> simp_all only [le_refl, jointMass_nonneg hp]

theorem lowerExponent_marginal (j : ℕ) :
    (∑' s : Sample, if lowerExponent s = j then jointMass p s else 0) =
      geometricMass p j := by
  rw [(event_summable hp (fun s => lowerExponent s = j)).tsum_prod]
  simp only [lowerExponent, jointMass, tsum_ite_eq, tsum_fintype, Fintype.sum_bool,
    bernoulliMass, Bool.false_eq_true, ↓reduceIte]
  ring

lemma zero_convolution : bernoulliMass p false * geometricMass p 0 = eulerMass p 0 := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte, incrementProbability,
    geometricMass, pow_zero, mul_one, eulerMass]
  field_simp
  ring

lemma succ_convolution (j : ℕ) :
    bernoulliMass p false * geometricMass p (j + 1) +
      bernoulliMass p true * geometricMass p j = eulerMass p (j + 1) := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte, incrementProbability,
    geometricMass, eulerMass, pow_succ]
  field_simp
  ring

theorem upperExponent_marginal (j : ℕ) :
    (∑' s : Sample, if upperExponent s = j then jointMass p s else 0) = eulerMass p j := by
  rw [(event_summable hp (fun s => upperExponent s = j)).tsum_prod]
  simp only [tsum_fintype, Fintype.sum_bool, upperExponent, jointMass, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero]
  cases j with
  | zero =>
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        tsum_zero, zero_add, tsum_ite_eq]
      exact zero_convolution hp
  | succ j =>
      simp only [Nat.add_left_inj, tsum_ite_eq]
      simpa only [add_comm] using succ_convolution hp j

theorem eulerMass_hasSum : HasSum (eulerMass p) 1 := by
  have ht : HasSum (fun j : ℕ => eulerMass p (j + 1))
      ((1 - 1 / p)⁻¹ * (1 / p)) := by
    simpa only [eulerMass, pow_succ] using
      (hasSum_geometric_of_lt_one (reciprocal_nonneg hp)
        (reciprocal_lt_one hp)).mul_right (1 / p)
  have h := (hasSum_nat_add_iff 1).mp ht
  convert! h using 1
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  simp only [Finset.sum_range_one, eulerMass]
  field_simp
  ring

theorem bernoulli_marginal (b : Bool) :
    (∑' s : Sample, if s.1 = b then jointMass p s else 0) = bernoulliMass p b := by
  rw [(event_summable hp (fun s => s.1 = b)).tsum_prod]
  have hi (a : Bool) :
      (∑' j : ℕ, if a = b then jointMass p (a, j) else 0) =
        if a = b then bernoulliMass p a else 0 := by
    split_ifs with h
    · simp only [jointMass, tsum_mul_left, (geometricMass_hasSum hp).tsum_eq, mul_one]
    · simp only [tsum_zero]
  simp only [hi, tsum_ite_eq]

omit hp in

lemma weighted_log_excess (s : Sample) :
    jointMass p s * ((upperExponent s - lowerExponent s : ℕ) : ℝ) * Real.log p =
      (bernoulliMass p s.1 * (if s.1 then Real.log p else 0)) * geometricMass p s.2 := by
  rcases s with ⟨b, j⟩
  cases b <;> simp [jointMass, upperExponent, lowerExponent, mul_comm, mul_assoc]

lemma log_excess_summable : Summable (fun s : Sample =>
    jointMass p s * ((upperExponent s - lowerExponent s : ℕ) : ℝ) * Real.log p) := by
  have hb : ∀ b : Bool, 0 ≤ bernoulliMass p b * (if b then Real.log p else 0) := by
    intro b
    apply mul_nonneg (bernoulliMass_nonneg hp b)
    split_ifs
    · exact Real.log_nonneg (by linarith)
    · rfl
  have h := (hasSum_fintype (fun b : Bool =>
    bernoulliMass p b * (if b then Real.log p else 0))).summable.mul_of_nonneg
      (geometricMass_hasSum hp).summable hb (geometricMass_nonneg hp)
  exact h.congr (fun s => (weighted_log_excess s).symm)

theorem expected_log_excess :
    (∑' s : Sample, jointMass p s *
      ((upperExponent s - lowerExponent s : ℕ) : ℝ) * Real.log p) =
        Real.log p / (p - 1) ^ 2 := by
  rw [(log_excess_summable hp).tsum_prod]
  simp only [weighted_log_excess, tsum_mul_left, (geometricMass_hasSum hp).tsum_eq,
    mul_one, tsum_fintype, Fintype.sum_bool, bernoulliMass, Bool.false_eq_true,
    ↓reduceIte, mul_zero, add_zero, incrementProbability]
  ring

omit hp in

theorem lowerExponent_le_upperExponent (s : Sample) : lowerExponent s ≤ upperExponent s := by
  exact Nat.le_add_right _ _

omit hp in

theorem at_two : eulerMass 2 0 = 0 ∧ bernoulliMass 2 false = 0 ∧ bernoulliMass 2 true = 1 := by
  norm_num [eulerMass, bernoulliMass, incrementProbability]

end EulerPrimeLaw

end

end Erdos970

end OAI
