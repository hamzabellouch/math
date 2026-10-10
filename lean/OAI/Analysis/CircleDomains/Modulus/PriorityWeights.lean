import OAI.Analysis.CircleDomains.Selection.PriorityInterpolation
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace OAI

/-! Countable priority weights form a subprobability distribution. The
remaining mass belongs to the original horizontal coordinate. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def priorityRemainder (χ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (1-χ i)

 def priorityWeight (χ : ℕ → ℝ) (n : ℕ) : ℝ := χ n*priorityRemainder χ n

 theorem priorityRemainder_succ (χ : ℕ → ℝ) (n : ℕ) :
    priorityRemainder χ (n+1) = priorityRemainder χ n*(1-χ n) := by
  simp only [priorityRemainder, Finset.prod_range_succ]

 theorem priorityRemainder_mem_unit {χ : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    priorityRemainder χ n ∈ Icc (0 : ℝ) 1 := by
  induction n with
  | zero => simp [priorityRemainder]
  | succ n ih =>
    rw [priorityRemainder_succ]
    have h0 : 0 ≤ 1-χ n := by linarith [(hχ n).2]
    exact ⟨mul_nonneg ih.1 h0,
      (mul_le_mul ih.2 (by linarith [(hχ n).1] : 1-χ n ≤ 1) h0 zero_le_one).trans_eq (one_mul 1)⟩

 theorem priorityWeight_nonneg {χ : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    0 ≤ priorityWeight χ n := mul_nonneg (hχ n).1 (priorityRemainder_mem_unit hχ n).1

 theorem priorityWeight_sum (χ : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, priorityWeight χ i = 1-priorityRemainder χ n := by
  induction n with
  | zero => simp [priorityRemainder]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, priorityRemainder_succ]
    dsimp only [priorityWeight]
    ring

 theorem priorityWeight_summable {χ : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1) :
    Summable (priorityWeight χ) := by
  apply summable_of_sum_range_le (c := 1) (priorityWeight_nonneg hχ)
  intro n
  rw [priorityWeight_sum]
  linarith [(priorityRemainder_mem_unit hχ n).1]

 theorem priorityWeight_tsum_mem_unit {χ : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1) :
    (∑' n, priorityWeight χ n) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨tsum_nonneg (priorityWeight_nonneg hχ), ?_⟩
  apply Real.tsum_le_of_sum_range_le (priorityWeight_nonneg hχ)
  intro n
  rw [priorityWeight_sum]
  linarith [(priorityRemainder_mem_unit hχ n).1]

 theorem priorityWeighted_summable {χ c : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1)
    {B : ℝ} (hc : ∀ n, ‖c n‖ ≤ B) : Summable (fun n => priorityWeight χ n*c n) := by
  apply Summable.of_norm_bounded ((priorityWeight_summable hχ).mul_right B)
  intro n
  rw [norm_mul, Real.norm_eq_abs (priorityWeight χ n), abs_of_nonneg (priorityWeight_nonneg hχ n)]
  exact mul_le_mul_of_nonneg_left (hc n) (priorityWeight_nonneg hχ n)

 def priorityInfiniteValue (χ c : ℕ → ℝ) (x : ℝ) : ℝ :=
  (1-∑' n, priorityWeight χ n)*x + ∑' n, priorityWeight χ n*c n

 theorem priorityInfiniteValue_norm_le {χ c : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1)
    {B x : ℝ} (hc : ∀ n, ‖c n‖ ≤ B) (hx : ‖x‖ ≤ B) :
    ‖priorityInfiniteValue χ c x‖ ≤ B := by
  have hw := priorityWeight_tsum_mem_unit hχ
  have hrem : 0 ≤ 1-∑' n, priorityWeight χ n := by linarith [hw.2]
  have hsum : ‖∑' n, priorityWeight χ n*c n‖ ≤ (∑' n, priorityWeight χ n)*B := by
    have h := tsum_of_norm_bounded (f := fun n => priorityWeight χ n*c n)
      ((priorityWeight_summable hχ).mul_right B).hasSum (fun n => by
      rw [norm_mul, Real.norm_eq_abs (priorityWeight χ n), abs_of_nonneg (priorityWeight_nonneg hχ n)]
      exact mul_le_mul_of_nonneg_left (hc n) (priorityWeight_nonneg hχ n))
    simpa only [(priorityWeight_summable hχ).tsum_mul_right] using h
  calc
    ‖priorityInfiniteValue χ c x‖ ≤ ‖(1-∑' n, priorityWeight χ n)*x‖ +
      ‖∑' n, priorityWeight χ n*c n‖ := norm_add_le _ _
    _ ≤ (1-∑' n, priorityWeight χ n)*B+(∑' n, priorityWeight χ n)*B := by
      rw [norm_mul, Real.norm_eq_abs (1-∑' n, priorityWeight χ n), abs_of_nonneg hrem]
      exact add_le_add (mul_le_mul_of_nonneg_left hx hrem) hsum
    _ = B := by ring

end CircleDomainRigidity

end

end OAI
