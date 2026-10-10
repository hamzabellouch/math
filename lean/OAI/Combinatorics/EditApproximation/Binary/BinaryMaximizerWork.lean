import OAI.Combinatorics.EditApproximation.Binary.BinaryGradientWork

namespace OAI

/-! Counted stored-score maximization for Boolean fraction coordinates. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem scoredArgmaxWithWork_score_width {α : Type*} (score : α → BinaryFraction × ℕ)
    (values : List α) (W : ℕ) (hw : ∀ a ∈ values, (score a).1.width ≤ W)
    (best : α × BinaryFraction) (hbest : (scoredArgmaxWithWork score values).1 = some best) :
    best.2.width ≤ W := by
  rw [scoredArgmaxWithWork_value] at hbest
  cases h : values.argmax (fun a => (score a).1.value) with
  | none => simp only [h, Option.map_none] at hbest; contradiction
  | some a =>
    have ha : a ∈ values := List.argmax_mem (by rw [h]; simp)
    simp only [h, Option.map_some, Option.some.injEq] at hbest
    rw [← hbest]
    exact hw a ha

theorem scoredArgmaxWithWork_cost {α : Type*} (score : α → BinaryFraction × ℕ)
    (values : List α) (C W : ℕ) (hc : ∀ a ∈ values, (score a).2 ≤ C)
    (hw : ∀ a ∈ values, (score a).1.width ≤ W) :
    (scoredArgmaxWithWork score values).2 ≤ values.length * (C + 1000 * (W + 1) ^ 2 + 2) := by
  induction values with
  | nil => simp [scoredArgmaxWithWork]
  | cons a rest ih =>
    have ht := ih (fun b hb => hc b (List.mem_cons_of_mem _ hb))
      (fun b hb => hw b (List.mem_cons_of_mem _ hb))
    have ha := hc a List.mem_cons_self
    have haw := hw a List.mem_cons_self
    cases hbest : (scoredArgmaxWithWork score rest).1 with
    | none =>
      simp only [scoredArgmaxWithWork, hbest, List.length_cons]
      nlinarith only [ht, ha]
    | some best =>
      have hbw := scoredArgmaxWithWork_score_width score rest W
        (fun b hb => hw b (List.mem_cons_of_mem _ hb)) best hbest
      have hcmp := ltWithWork_cost (score a).1 best.2 W haw hbw
      simp only [scoredArgmaxWithWork, hbest, List.length_cons]
      nlinarith only [ht, ha, hcmp]

def maximizerWordBudget (d B V : ℕ) : ℕ := dotWordBudget d B V

def maximizerBitBudget (d v B V : ℕ) : ℕ :=
  let W := maximizerWordBudget d B V
  v * (1 + d * (100000 * (W + 1) ^ 2) + 1000 * (W + 1) ^ 2 + 2) + d + 1

theorem maximizerWithWork_cost {d : ℕ} (gradient : Vector BinaryFraction d)
    (vertices : List (Vector BinaryFraction d)) (B V : ℕ)
    (hgw : ∀ i, (gradient.get i).width ≤ B)
    (hgv : ∀ i, |(gradient.get i).value| ≤ V)
    (hvw : ∀ v ∈ vertices, ∀ i, (v.get i).width ≤ B)
    (hvv : ∀ v ∈ vertices, ∀ i, |(v.get i).value| ≤ V) :
    (maximizerWithWork gradient vertices).2 ≤ maximizerBitBudget d vertices.length B V := by
  let W := maximizerWordBudget d B V
  have hc : ∀ v ∈ vertices, (dotWithWork gradient v).2 ≤ 1 + d * (100000 * (W + 1) ^ 2) := by
    intro v hv
    simpa only [dotWithWork, W, maximizerWordBudget, List.length_finRange] using
      dotListWithWork_cost_in gradient v (List.finRange d) d B V (by simp)
        (fun i _ => hgw i) (fun i _ => hvw v hv i) (fun i _ => hgv i) (fun i _ => hvv v hv i)
  have hw : ∀ v ∈ vertices, (dotWithWork gradient v).1.width ≤ W := by
    intro v hv
    exact dotListWithWork_width_in gradient v (List.finRange d) d B V (by simp)
      (fun i _ => hgw i) (fun i _ => hvw v hv i) (fun i _ => hgv i) (fun i _ => hvv v hv i)
  have h := scoredArgmaxWithWork_cost (dotWithWork gradient) vertices
    (1 + d * (100000 * (W + 1) ^ 2)) W hc hw
  change (scoredArgmaxWithWork (dotWithWork gradient) vertices).2 + d + 1 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add_right h d) 1

end BinaryFraction
end EditApproximation

end OAI
