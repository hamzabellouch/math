import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {P Λ : Type*} [instDecidableEqP : DecidableEq P] [instDecidableEqΛ : DecidableEq Λ]

def multiplicity (I : P → Λ → Prop) (L : Finset Λ) (x : P) : ℕ :=
  (L.filter (I x)).card

def coveredPoints (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) : Finset P :=
  X.filter fun x => 0 < multiplicity I L x

def overlapExcess (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) : ℕ :=
  ∑ x ∈ X, (multiplicity I L x - 1)

def orderedPairMass (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) : ℕ :=
  ∑ x ∈ X, multiplicity I L x * (multiplicity I L x - 1)

def heavyPoints (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) (T : ℝ) :
    Finset P := X.filter fun x => T ≤ (multiplicity I L x : ℝ)

theorem incidence_double_count (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (∑ l ∈ L, (X.filter fun x => I x l).card) =
      ∑ x ∈ X, multiplicity I L x := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  simp only [multiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem sum_multiplicity_eq_covered_add_excess
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (∑ x ∈ X, multiplicity I L x) =
      (coveredPoints I X L).card + overlapExcess I X L := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  calc
    _ = ∑ x ∈ X, ((if 0 < multiplicity I L x then 1 else 0) +
        (multiplicity I L x - 1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      cases h : multiplicity I L x with
      | zero => simp
      | succ n => simp [Nat.add_comm]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_boole]
      rfl

theorem incidence_eq_covered_add_excess
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (∑ l ∈ L, (X.filter fun x => I x l).card) =
      (coveredPoints I X L).card + overlapExcess I X L := by
  rw [incidence_double_count, sum_multiplicity_eq_covered_add_excess]

theorem covered_add_uncovered_card
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (coveredPoints I X L).card + (X \ coveredPoints I X L).card = X.card := let _ := instDecidableEqΛ; by
  rw [Nat.add_comm]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)

theorem cover_count_bounds
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ)
    (d q e0 e1 b δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ d) (hq : 0 < q) (he1 : 0 ≤ e1)
    (hsize : d * q ^ 2 - e0 ≤ (X.card : ℝ))
    (hline : ∀ l ∈ L, ((X.filter fun x => I x l).card : ℝ) ≤ d * q + e1)
    (huncovered : ((X \ coveredPoints I X L).card : ℝ) ≤ b)
    (hcard : (L.card : ℝ) ≤ q) :
    (overlapExcess I X L : ℝ) ≤ e0 + q * e1 + b ∧
      q - (L.card : ℝ) ≤ (e0 + q * e1 + b) / (δ * q) := by
  let N : ℝ := X.card
  let M : ℝ := L.card
  let C : ℝ := (coveredPoints I X L).card
  let U : ℝ := (X \ coveredPoints I X L).card
  let E : ℝ := overlapExcess I X L
  let J : ℝ := ∑ l ∈ L, ((X.filter fun x => I x l).card : ℝ)
  have hcount : J = C + E := by
    dsimp [J, C, E]
    exact_mod_cast incidence_eq_covered_add_excess I X L
  have hpartition : C + U = N := by
    dsimp [C, U, N]
    exact_mod_cast covered_add_uncovered_card I X L
  have hupper : J ≤ M * (d * q + e1) := by
    calc
      J ≤ ∑ _l ∈ L, (d * q + e1) := Finset.sum_le_sum hline
      _ = _ := by simp [M]
  have hcap : 0 ≤ d * q + e1 :=
    add_nonneg (mul_nonneg (hδ.le.trans hd) hq.le) he1
  have hupperQ := hupper.trans (mul_le_mul_of_nonneg_right hcard hcap)
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  have hmerr : M * e1 ≤ q * e1 := mul_le_mul_of_nonneg_right hcard he1
  have hN : d * q ^ 2 - e0 ≤ N := hsize
  have hU : U ≤ b := huncovered
  have hM : M ≤ q := hcard
  have hEbound : E ≤ e0 + q * e1 + b := by
    nlinarith [hupperQ, hcount, hpartition, hN, hU]
  have hgap : d * q * (q - M) ≤ e0 + q * e1 + b := by
    nlinarith [hupper, hcount, hpartition, hN, hU, hE0, hmerr]
  have hscale : δ * q * (q - M) ≤ d * q * (q - M) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hq.le)
      (sub_nonneg.mpr hM)
  refine ⟨hEbound, ?_⟩
  apply (le_div_iff₀ (mul_pos hδ hq)).2
  simpa only [mul_comm] using hscale.trans hgap

theorem heavyPoints_card_mul_le_excess
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) (T : ℝ) (hT : 1 < T) :
    ((heavyPoints I X L T).card : ℝ) * (T - 1) ≤ (overlapExcess I X L : ℝ) := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  have hsum : (∑ x ∈ X, ((multiplicity I L x - 1 : ℕ) : ℝ)) =
      (overlapExcess I X L : ℝ) := by simp only [overlapExcess, Nat.cast_sum]
  rw [← hsum]
  calc
    _ = ∑ _x ∈ heavyPoints I X L T, (T - 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ heavyPoints I X L T, ((multiplicity I L x - 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxT : T ≤ (multiplicity I L x : ℝ) := (Finset.mem_filter.mp hx).2
      have hnR : (1 : ℝ) ≤ multiplicity I L x := hT.le.trans hxT
      have hn : 1 ≤ multiplicity I L x := by exact_mod_cast hnR
      rw [Nat.cast_sub hn, Nat.cast_one]
      exact sub_le_sub_right hxT 1
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro x hx hxnot; exact Nat.cast_nonneg _)

theorem orderedPairMass_le_light_add_heavy
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) (T R : ℝ)
    (hT : 0 ≤ T) (hR : ∀ x ∈ X, (multiplicity I L x : ℝ) ≤ R) :
    (orderedPairMass I X L : ℝ) ≤ T * (overlapExcess I X L : ℝ) +
      R * ∑ x ∈ heavyPoints I X L T, (multiplicity I L x : ℝ) := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  have hpoint (x : P) (hx : x ∈ X) :
      (multiplicity I L x : ℝ) * ((multiplicity I L x - 1 : ℕ) : ℝ) ≤
        T * ((multiplicity I L x - 1 : ℕ) : ℝ) +
          if T ≤ (multiplicity I L x : ℝ) then R * (multiplicity I L x : ℝ) else 0 := by
    have ha0 : 0 ≤ ((multiplicity I L x - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn0 : 0 ≤ (multiplicity I L x : ℝ) := Nat.cast_nonneg _
    have haN : ((multiplicity I L x - 1 : ℕ) : ℝ) ≤ (multiplicity I L x : ℝ) := by
      exact_mod_cast Nat.sub_le (multiplicity I L x) 1
    by_cases hh : T ≤ (multiplicity I L x : ℝ)
    · simp only [ite_eq_left hh]
      have hp := mul_le_mul_of_nonneg_left (haN.trans (hR x hx)) hn0
      nlinarith [mul_nonneg hT ha0]
    · simpa only [ite_eq_right hh, add_zero] using
        mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hh)) ha0
  have hsum := Finset.sum_le_sum hpoint
  simpa only [orderedPairMass, overlapExcess, heavyPoints, Nat.cast_sum,
    Nat.cast_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_filter,
    mul_ite, mul_zero] using hsum

end RyserCoveringCounterexample.LineCover

end

end OAI
