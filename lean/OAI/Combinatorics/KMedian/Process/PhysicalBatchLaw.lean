import Mathlib
import OAI.Combinatorics.KMedian.Probability.BernoulliBatches
import OAI.Combinatorics.KMedian.Probability.FiniteKernels

namespace OAI

namespace MetricKMedian.FiniteLaw

theorem prob_false {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) :
    μ.prob (fun _ => False)=0 := by
  simp only [prob, ite_false, expect_const]

theorem prob_true {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) :
    μ.prob (fun _ => True)=1 := by
  simp only [prob, ite_true, expect_const]

end MetricKMedian.FiniteLaw

namespace MetricKMedian.PhysicalBatchLaw
open Finset
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def balanced (Z : Finset E) (C : E → Finset E) (ω : E → Bool) : Finset E :=
  FiniteLaw.selected C ω ∩ Z
noncomputable def unbalanced (Z : Finset E) (ω : E → Bool) : Finset E :=
  univ.filter (fun e => ω e=true ∧ e ∉ Z)

noncomputable def law (Z : Finset E) (C : E → Finset E)
    (p : ℝ) (q : E → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) : FiniteLaw (Finset E) :=
  FiniteLaw.mix (1/2) (by norm_num) (by norm_num)
    ((FiniteLaw.bernoulli (fun _ : E => p) (fun _ => hp0) (fun _ => hp1)).map (balanced Z C))
    ((FiniteLaw.bernoulli q hq0 hq1).map (unbalanced Z))

theorem prob_eq (Z : Finset E) (C : E → Finset E)
    (p : ℝ) (q : E → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (R : Finset E → Prop) [DecidablePred R] :
    (law Z C p q hp0 hp1 hq0 hq1).prob R =
      (1/2)*(FiniteLaw.bernoulli (fun _ : E => p) (fun _ => hp0) (fun _ => hp1)).prob
        (fun ω => R (balanced Z C ω))+
      (1/2)*(FiniteLaw.bernoulli q hq0 hq1).prob (fun ω => R (unbalanced Z ω)) := by
  unfold law FiniteLaw.prob
  rw [FiniteLaw.expect_mix, FiniteLaw.expect_map, FiniteLaw.expect_map]
  norm_num

theorem marginal (Z : Finset E) (C : E → Finset E)
    (p : ℝ) (q : E → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (e : E) (hself : e ∉ C e) :
    (law Z C p q hp0 hp1 hq0 hq1).prob (fun A => e ∈ A)=
      if e ∈ Z then (1/2)*p*(1-p)^(C e).card else (1/2)*q e := by
  rw [prob_eq]
  by_cases h : e ∈ Z
  · simp only [balanced, unbalanced, mem_inter, mem_filter, mem_univ,
      h, and_true, not_true_eq_false, and_false, ite_true, FiniteLaw.prob_false,
      FiniteLaw.filtered_marginal p hp0 hp1 C e hself, mul_zero, add_zero]
    ring
  · simp only [balanced, unbalanced, mem_inter, mem_filter, mem_univ, true_and,
      h, and_false, not_false_eq_true, and_true, ite_false, FiniteLaw.prob_false,
      FiniteLaw.bernoulli_marginal, mul_zero, zero_add]

theorem pair_le (Z : Finset E) (C : E → Finset E)
    (p : ℝ) (q : E → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    {e f : E} (hef : e ≠ f) :
    (law Z C p q hp0 hp1 hq0 hq1).prob (fun A => e ∈ A ∧ f ∈ A) ≤
      (p^2+q e*q f)/2 := by
  rw [prob_eq]
  have hb : (FiniteLaw.bernoulli (fun _ : E => p) (fun _ => hp0) (fun _ => hp1)).prob
      (fun ω => e ∈ balanced Z C ω ∧ f ∈ balanced Z C ω) ≤ p^2 := by
    apply (FiniteLaw.prob_mono _ (E := fun ω => e ∈ balanced Z C ω ∧ f ∈ balanced Z C ω)
      (F := fun ω => e ∈ FiniteLaw.selected C ω ∧ f ∈ FiniteLaw.selected C ω) ?_).trans
      (FiniteLaw.filtered_pair_le p hp0 hp1 C hef)
    intro ω h
    exact ⟨(mem_inter.mp h.1).1, (mem_inter.mp h.2).1⟩
  have hu : (FiniteLaw.bernoulli q hq0 hq1).prob
      (fun ω => e ∈ unbalanced Z ω ∧ f ∈ unbalanced Z ω) ≤ q e*q f := by
    rw [← FiniteLaw.bernoulli_pair q hq0 hq1 hef]
    apply FiniteLaw.prob_mono
    intro ω h
    exact ⟨(mem_filter.mp h.1).2.1, (mem_filter.mp h.2).2.1⟩
  linarith only [hb, hu]

theorem marginal_error (Z : Finset E) (C : E → Finset E)
    (p : ℝ) (q : E → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    {φ : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hq : ∀ e, p ≤ q e ∧ q e ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e) (e : E) :
    |(law Z C p q hp0 hp1 hq0 hq1).prob (fun A => e ∈ A)-p/2| ≤
      (N:ℝ)*p^2/2+φ*p/2 := by
  rw [marginal Z C p q hp0 hp1 hq0 hq1 e (hself e)]
  have hnonneg := mul_nonneg hφ hp0
  have hN0 : 0 ≤ (N:ℝ)*p^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg p)
  by_cases he : e ∈ Z
  · rw [ite_eq_left he]
    have herror := FiniteLaw.filtered_marginal_error p hp0 hp1 C e (hself e)
    rw [FiniteLaw.filtered_marginal p hp0 hp1 C e (hself e)] at herror
    have hN : (C e).card*p^2 ≤ (N:ℝ)*p^2 :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hC e)) (sq_nonneg p)
    have heq : (1/2)*p*(1-p)^(C e).card-p/2 = (p*(1-p)^(C e).card-p)/2 := by ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [herror, hN, hnonneg]
  · rw [ite_eq_right he, abs_of_nonneg (by linarith only [(hq e).1])]
    nlinarith only [(hq e).2, hN0]

end MetricKMedian.PhysicalBatchLaw

end OAI
