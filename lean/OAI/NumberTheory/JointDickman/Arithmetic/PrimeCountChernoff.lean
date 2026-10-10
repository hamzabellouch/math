import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSetWeights
import OAI.NumberTheory.JointDickman.Amplification.LogProductBounds

namespace OAI

/-! # Exponential bounds for counts in a selected prime subset -/

namespace JointDickman

open Finset

/-- The exact generating function for the count in Q. -/
theorem bernoulliSubsetMass_restricted_count_exp (P Q : Finset ℕ) (q : ℕ → ℝ) (s : ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S * Real.exp (s * (S ∩ Q).card)) =
      ∏ p ∈ P ∩ Q, (1 - q p + q p * Real.exp s) := by
  classical
  have hv (S : Finset ℕ) : (∏ p ∈ S, if p ∈ Q then Real.exp s else 1) =
      Real.exp (s * (S ∩ Q).card) := by
    rw [← prod_filter, prod_const, ← Real.exp_nat_mul]
    have hf : S.filter (fun p => p ∈ Q) = S ∩ Q := by ext p; simp
    rw [hf]
    congr 1
    ring
  have h := bernoulliSubsetMass_tilt P q (fun p => if p ∈ Q then Real.exp s else 1)
  simp_rw [hv] at h
  rw [h]
  have heq (p : ℕ) : 1 - q p + q p * (if p ∈ Q then Real.exp s else 1) =
      if p ∈ Q then 1 - q p + q p * Real.exp s else 1 := by
    by_cases hp : p ∈ Q <;> simp [hp]
  simp_rw [heq]
  rw [← prod_filter]
  congr 1

theorem bernoulliSubsetMass_restricted_count_exp_bound (P Q : Finset ℕ)
    (q : ℕ → ℝ) (s : ℝ) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S * Real.exp (s * (S ∩ Q).card)) ≤
      Real.exp ((Real.exp s - 1) * ∑ p ∈ P ∩ Q, q p) := by
  rw [bernoulliSubsetMass_restricted_count_exp]
  calc
    _ ≤ ∏ p ∈ P ∩ Q, Real.exp ((Real.exp s - 1) * q p) := by
      apply prod_le_prod₀
      · intro p hp
        have hpP := (mem_inter.mp hp).1
        exact add_nonneg (sub_nonneg.mpr (hq p hpP).2)
          (mul_nonneg (hq p hpP).1 (Real.exp_pos _).le)
      · intro p _
        have h := Real.add_one_le_exp ((Real.exp s - 1) * q p)
        nlinarith
    _ = _ := by rw [← Real.exp_sum, ← mul_sum]

/-- Both upper and lower tails are covered by the signed threshold
`s*r ≤ s*count`; no asymptotic or distributional premise is hidden here. -/
theorem bernoulliSubsetMass_restricted_count_tail (P Q : Finset ℕ)
    (q : ℕ → ℝ) (s r : ℝ) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    (∑ S ∈ P.powerset, if s * r ≤ s * (S ∩ Q).card then bernoulliSubsetMass P q S else 0) ≤
      Real.exp (-s * r + (Real.exp s - 1) * ∑ p ∈ P ∩ Q, q p) := by
  classical
  have hmark : Real.exp (s * r) *
      (∑ S ∈ P.powerset, if s * r ≤ s * (S ∩ Q).card then bernoulliSubsetMass P q S else 0) ≤
        ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * Real.exp (s * (S ∩ Q).card) := by
    rw [mul_sum]
    apply sum_le_sum
    intro S hS
    have hmass := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
    split_ifs with h
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) hmass
    · simpa only [mul_zero] using mul_nonneg hmass (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_left
    (hmark.trans (bernoulliSubsetMass_restricted_count_exp_bound P Q q s hq)) (Real.exp_pos (-s * r)).le
  have he : Real.exp (-s * r) * Real.exp (s * r) = 1 := by
    rw [← Real.exp_add]
    rw [show -s * r + s * r = 0 by ring, Real.exp_zero]
  simpa only [← mul_assoc, he, one_mul, ← Real.exp_add] using h

end JointDickman

end OAI
