import OAI.NumberTheory.TwoPoint.Circuits.CircuitGateSwitching
import OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionComposition

namespace OAI

/-! Iterate switching through arbitrary AND/OR circuits. Each gate pays
one switching error, so the total loss is bounded by circuit size. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem FiniteLaw.average_probability_le_union {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (E : α → β → Prop)
    (bad : ι → α → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ x, (∀ i, ¬ bad i x) → ν.probability (E x) ≤ δ) :
    μ.average (fun x => ν.probability (E x)) ≤
      (∑ i, μ.probability (bad i)) + δ := by
  calc
    _ ≤ μ.average (fun x => (if ∃ i, bad i x then 1 else 0) + δ) := by
      apply μ.average_mono
      intro x
      by_cases hx : ∃ i, bad i x
      · simpa only [ite_eq_left hx] using
          (ν.probability_le_one (E x)).trans (by linarith)
      · simpa only [ite_eq_right hx, zero_add] using
          hgood x (fun i hi => hx ⟨i, hi⟩)
    _ = μ.probability (fun x => ∃ i, bad i x) + δ := by
      simp only [FiniteLaw.probability, FiniteLaw.average, mul_add,
        sum_add_distrib, ← sum_mul, μ.total, one_mul]
      congr 1
      apply sum_congr rfl
      intro x _
      by_cases hx : ∃ i, bad i x <;> simp [hx]
    _ ≤ _ := add_le_add (μ.probability_exists_le bad) le_rfl

namespace AC0Circuit

theorem restriction_shallow {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (r : ℕ) (hr : 1 ≤ r)
    (hq : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2)
    (d : ℕ) (c : AC0Circuit n) (hc : c.depth ≤ d) :
    (restrictionLaw n (p ^ d) (pow_nonneg hp _) (pow_le_one₀ hp hp1.le)).probability
      (fun ρ => ¬ HasSmallDecisionTree (fun x => c.eval (ρ.apply x)) r) ≤
      (c.size : ℝ) *
        (2 * (((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (r + 1)) := by
  let δ := 2 * (((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (r + 1)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  induction d generalizing c with
  | zero =>
    cases c with
    | literal i b =>
      have he (ρ : PartialAssignment n) :
          ¬ (¬ HasSmallDecisionTree (fun x => (literal i b).eval (ρ.apply x)) r) :=
        not_not.mpr (literal_hasSmallDecisionTree i b hr ρ)
      simpa only [FiniteLaw.probability, he, ite_false, FiniteLaw.average_const,
        size, Nat.cast_one, one_mul] using hδ
    | andGate children => simp [depth] at hc
    | orGate children => simp [depth] at hc
  | succ d ih =>
    let μ := restrictionLaw n (p ^ d) (pow_nonneg hp _) (pow_le_one₀ hp hp1.le)
    let ν := restrictionLaw n p hp hp1.le
    have hcompose (E : PartialAssignment n → Prop) :
        (restrictionLaw n (p ^ (d + 1)) (pow_nonneg hp _)
          (pow_le_one₀ hp hp1.le)).probability E =
        μ.average (fun ρ => ν.probability (fun τ => E (composeRestriction ρ τ))) := by
      unfold FiniteLaw.probability
      exact (restrictionLaw_compose (p ^ d) p (pow_nonneg hp _)
        (pow_le_one₀ hp hp1.le) hp hp1.le (fun ρ => if E ρ then 1 else 0)).symm
    cases c with
    | literal i b =>
      have he (ρ : PartialAssignment n) :
          ¬ (¬ HasSmallDecisionTree (fun x => (literal i b).eval (ρ.apply x)) r) :=
        not_not.mpr (literal_hasSmallDecisionTree i b hr ρ)
      simpa only [FiniteLaw.probability, he, ite_false, FiniteLaw.average_const,
        size, Nat.cast_one, one_mul] using hδ
    | andGate children =>
      have hchild (i) : (children i).depth ≤ d := by
        have hi := Finset.le_sup (f := fun i => (children i).depth) (mem_univ i)
        simp only [depth] at hc
        omega
      rw [hcompose]
      apply (FiniteLaw.average_probability_le_union μ ν _
        (fun i ρ => ¬ HasSmallDecisionTree (fun x => (children i).eval (ρ.apply x)) r)
        δ hδ ?_).trans
      · calc
          _ ≤ (∑ i, ((children i).size : ℝ) * δ) + δ := by
            exact add_le_add (sum_le_sum (fun i _ => ih (children i) (hchild i))) le_rfl
          _ = _ := by simp only [size, Nat.cast_add, Nat.cast_one, Nat.cast_sum]; rw [← sum_mul]; ring
      · intro ρ hρ
        have hh := conjunction_restriction_switching
          (fun i x => (children i).eval (ρ.apply x)) (fun i => not_not.mp (hρ i))
          p hp hp1 hq
        simpa only [eval, composeRestriction_apply] using hh
    | orGate children =>
      have hchild (i) : (children i).depth ≤ d := by
        have hi := Finset.le_sup (f := fun i => (children i).depth) (mem_univ i)
        simp only [depth] at hc
        omega
      rw [hcompose]
      apply (FiniteLaw.average_probability_le_union μ ν _
        (fun i ρ => ¬ HasSmallDecisionTree (fun x => (children i).eval (ρ.apply x)) r)
        δ hδ ?_).trans
      · calc
          _ ≤ (∑ i, ((children i).size : ℝ) * δ) + δ := by
            exact add_le_add (sum_le_sum (fun i _ => ih (children i) (hchild i))) le_rfl
          _ = _ := by simp only [size, Nat.cast_add, Nat.cast_one, Nat.cast_sum]; rw [← sum_mul]; ring
      · intro ρ hρ
        have hh := disjunction_restriction_switching
          (fun i x => (children i).eval (ρ.apply x)) (fun i => not_not.mp (hρ i))
          p hp hp1 hq
        simpa only [eval, composeRestriction_apply] using hh


end AC0Circuit

end TwoPointCorrelations

end OAI
