import OAI.Combinatorics.Ryser.Incidence.FourAnchorsCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

noncomputable section

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

attribute [local instance] Classical.propDecidable

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

theorem sum_trace_card_eq_sum_selected_degree (R : Pt → Ln → Prop)
    (N : Finset Pt) (L : Finset Ln) :
    (∑ l ∈ L, ((N.filter fun p => R p l).card : ℝ)) =
      ∑ p ∈ N, ((L.filter fun l => R p l).card : ℝ) := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  have h : (∑ l ∈ L, (N.filter fun p => R p l).card) =
      ∑ p ∈ N, (L.filter fun l => R p l).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  exact_mod_cast h

theorem sum_trace_card_ge_min_degree (R : Pt → Ln → Prop)
    (N : Finset Pt) (L : Finset Ln) (d : ℝ)
    (hdegree : ∀ p ∈ N, d ≤ ((L.filter fun l => R p l).card : ℝ)) :
    d * (N.card : ℝ) ≤ ∑ l ∈ L, ((N.filter fun p => R p l).card : ℝ) := by
  rw [sum_trace_card_eq_sum_selected_degree]
  calc
    d * (N.card : ℝ) = ∑ _p ∈ N, d := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum hdegree

theorem sum_high_trace_ge_min_degree (R : Pt → Ln → Prop)
    (N : Finset Pt) (L : Finset Ln) (d : ℝ)
    (hdegree : ∀ p ∈ N, d ≤ ((L.filter fun l => R p l).card : ℝ)) :
    d * (N.card : ℝ) - 2 * (L.card : ℝ) ≤
      ∑ l ∈ L, if 3 ≤ (N.filter fun p => R p l).card then
        ((N.filter fun p => R p l).card : ℝ) else 0 := by
  let f : Ln → ℝ := fun l =>
    if 3 ≤ (N.filter fun p => R p l).card then
      ((N.filter fun p => R p l).card : ℝ) else 0
  have hpoint (l : Ln) : ((N.filter fun p => R p l).card : ℝ) ≤ f l + 2 := by
    dsimp only [f]
    split_ifs with h
    · linarith
    · have hsmall : (N.filter fun p => R p l).card ≤ 2 := by omega
      have hsmall' : ((N.filter fun p => R p l).card : ℝ) ≤ 2 := by
        exact_mod_cast hsmall
      simpa only [zero_add] using hsmall'
  have hsum := (sum_trace_card_ge_min_degree R N L d hdegree).trans
    (Finset.sum_le_sum fun l _ => hpoint l)
  have hadd : (∑ l ∈ L, (f l + 2)) =
      (∑ l ∈ L, f l) + 2 * (L.card : ℝ) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hadd] at hsum
  change d * (N.card : ℝ) - 2 * (L.card : ℝ) ≤ ∑ l ∈ L, f l
  linarith

theorem triple_sum_lower_bound (R : Pt → Ln → Prop)
    (N : Finset Pt) (L : Finset Ln) (d : ℝ)
    (hdegree : ∀ p ∈ N, d ≤ ((L.filter fun l => R p l).card : ℝ))
    (hbase : 0 ≤ d * (N.card : ℝ) - 2 * (L.card : ℝ)) :
    (2 / 9 : ℝ) * (d * (N.card : ℝ) - 2 * (L.card : ℝ)) ^ 3 ≤
      (L.card : ℝ) ^ 2 *
        ∑ l ∈ L, ((orderedTriples (N.filter fun p => R p l)).card : ℝ) := by
  let f : Ln → ℝ := fun l =>
    if 3 ≤ (N.filter fun p => R p l).card then
      ((N.filter fun p => R p l).card : ℝ) else 0
  have hf : ∀ l ∈ L, 0 ≤ f l := by
    intro l _
    dsimp only [f]
    split_ifs <;> positivity
  have hhigh : d * (N.card : ℝ) - 2 * (L.card : ℝ) ≤ ∑ l ∈ L, f l :=
    sum_high_trace_ge_min_degree R N L d hdegree
  have hcube := pow_le_pow_left₀ hbase hhigh 3
  have hmean := sum_cube_card_sq L f hf
  have hpoint : ∀ l ∈ L,
      (2 / 9 : ℝ) * f l ^ 3 ≤
        ((orderedTriples (N.filter fun p => R p l)).card : ℝ) := by
    intro l _
    dsimp only [f]
    split_ifs with h
    · exact two_ninths_cube_le_orderedTriples _ h
    · simp only [zero_pow (by decide : 3 ≠ 0), mul_zero]
      exact Nat.cast_nonneg _
  have hsum : (2 / 9 : ℝ) * (∑ l ∈ L, f l ^ 3) ≤
      ∑ l ∈ L, ((orderedTriples (N.filter fun p => R p l)).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpoint
  calc
    (2 / 9 : ℝ) * (d * (N.card : ℝ) - 2 * (L.card : ℝ)) ^ 3 ≤
        (2 / 9 : ℝ) * (∑ l ∈ L, f l) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    _ ≤ (2 / 9 : ℝ) * ((L.card : ℝ) ^ 2 * ∑ l ∈ L, f l ^ 3) :=
      mul_le_mul_of_nonneg_left hmean (by norm_num)
    _ = (L.card : ℝ) ^ 2 * ((2 / 9 : ℝ) * ∑ l ∈ L, f l ^ 3) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)

theorem anchorConfigurations_card_lower (R : Pt → Ln → Prop)
    (N : Finset Pt) (L : Finset Ln) (extra : ℝ) (hextra : 0 ≤ extra)
    (hoff : ∀ l ∈ L, extra ≤ ((N.filter fun p => ¬ R p l).card : ℝ)) :
    extra * (∑ l ∈ L, ((orderedTriples (N.filter fun p => R p l)).card : ℝ)) ≤
      ((anchorConfigurations R N L).card : ℝ) := by
  let _ := hextra
  simp only [card_anchorConfigurations, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  calc
    extra * ((orderedTriples (N.filter fun p => R p l)).card : ℝ) =
        ((orderedTriples (N.filter fun p => R p l)).card : ℝ) * extra := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hoff l hl) (Nat.cast_nonneg _)

private theorem card_orderedTriples_le_card_cube (P : Finset Pt) :
    (orderedTriples P).card ≤ P.card ^ 3 := by
  rw [card_orderedTriples]
  calc
    P.card * (P.card - 1) * (P.card - 2) ≤ P.card * P.card * P.card :=
      Nat.mul_le_mul (Nat.mul_le_mul_left P.card (Nat.sub_le P.card 1))
        (Nat.sub_le P.card 2)
    _ = P.card ^ 3 := by ring

theorem anchorConfigurations_card_upper (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln) (H : ℝ) (hH : 0 ≤ H)
    (hcap : ∀ l ∈ L, ((P.filter fun p => R p l).card : ℝ) ≤ H) :
    ((anchorConfigurations R P L).card : ℝ) ≤
      (L.card : ℝ) * H ^ 3 * (P.card : ℝ) := by
  have hterm (l : Ln) (hl : l ∈ L) :
      ((orderedTriples (P.filter fun p => R p l)).card : ℝ) *
        ((P.filter fun p => ¬ R p l).card : ℝ) ≤ H ^ 3 * (P.card : ℝ) := by
    have ht : ((orderedTriples (P.filter fun p => R p l)).card : ℝ) ≤
        ((P.filter fun p => R p l).card : ℝ) ^ 3 := by
      exact_mod_cast card_orderedTriples_le_card_cube (P.filter fun p => R p l)
    have htH : ((orderedTriples (P.filter fun p => R p l)).card : ℝ) ≤ H ^ 3 :=
      ht.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (hcap l hl) 3)
    have hoff : ((P.filter fun p => ¬ R p l).card : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun p => ¬ R p l) P)
    exact mul_le_mul htH hoff (Nat.cast_nonneg _) (pow_nonneg hH 3)
  calc
    ((anchorConfigurations R P L).card : ℝ) =
        ∑ l ∈ L, ((orderedTriples (P.filter fun p => R p l)).card : ℝ) *
          ((P.filter fun p => ¬ R p l).card : ℝ) := by
      simp only [card_anchorConfigurations, Nat.cast_sum, Nat.cast_mul]
    _ ≤ ∑ _l ∈ L, H ^ 3 * (P.card : ℝ) := Finset.sum_le_sum hterm
    _ = (L.card : ℝ) * H ^ 3 * (P.card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.Incidence

end

end OAI
