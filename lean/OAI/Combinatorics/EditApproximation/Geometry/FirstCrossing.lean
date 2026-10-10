import OAI.Combinatorics.EditApproximation.Geometry.Cones
import OAI.Combinatorics.EditApproximation.Geometry.BandRegret

namespace OAI

/-!
# The actual first crossing of a finite action band

The crossing index is computed from the fixed child tables for analysis.
It is independent of parent sampling. The lemmas separate the prefixPayoff,
the single crossing, and the nonpositive later clipped regrets.
-/

namespace EditApproximation

open Finset

noncomputable def firstCrossing {α : Type*} (band : Finset α)
    (S : ℕ) (actionCost : ℕ → α → ℝ) (c : ℝ) : ℕ :=
  if h : ∃ t, t < S ∧ ∃ action ∈ band, actionCost t action < c then Nat.find h else S

theorem firstCrossing_le {α : Type*} (band : Finset α)
    (S : ℕ) (actionCost : ℕ → α → ℝ) (c : ℝ) :
    firstCrossing band S actionCost c ≤ S := by
  unfold firstCrossing
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · rfl

theorem before_firstCrossing {α : Type*} (band : Finset α)
    (S : ℕ) (actionCost : ℕ → α → ℝ) (c : ℝ)
    {t : ℕ} (ht : t < firstCrossing band S actionCost c)
    {action : α} (ha : action ∈ band) : c ≤ actionCost t action := by
  by_contra hnot
  have htS : t < S := ht.trans_le (firstCrossing_le band S actionCost c)
  have hex : ∃ t, t < S ∧ ∃ action ∈ band, actionCost t action < c :=
    ⟨t, htS, action, ha, lt_of_not_ge hnot⟩
  have hfind : firstCrossing band S actionCost c ≤ t := by
    rw [firstCrossing, dite_eq_left hex]
    exact Nat.find_min' hex ⟨htS, action, ha, lt_of_not_ge hnot⟩
  omega

theorem at_firstCrossing {α : Type*} (band : Finset α)
    (S : ℕ) (actionCost : ℕ → α → ℝ) (c : ℝ)
    (ht : firstCrossing band S actionCost c < S) :
    ∃ action ∈ band, actionCost (firstCrossing band S actionCost c) action < c := by
  by_cases h : ∃ t, t < S ∧ ∃ action ∈ band, actionCost t action < c
  · simpa only [firstCrossing, dite_eq_left h] using (Nat.find_spec h).2
  · have heq : firstCrossing band S actionCost c = S := by
      rw [firstCrossing, dite_eq_right h]
    omega

/-- At every later time, the previous-index Bellman option uses the
same crossing action. Child-table monotonicity keeps its cost below `c`. -/
theorem after_firstCrossing_parent {α : Type*} (band : Finset α)
    (S : ℕ) (actionCost : ℕ → α → ℝ) (c : ℝ) (parent : ℕ → ℝ)
    (hmono : ∀ action ∈ band, Antitone (fun t => actionCost t action))
    (hbellman : ∀ t < S, ∀ action ∈ band, parent (t + 1) ≤ actionCost t action)
    {t : ℕ} (hafter : firstCrossing band S actionCost c < t) (ht : t < S) :
    max c (parent t) = c := by
  obtain ⟨action, ha, hcross⟩ := at_firstCrossing band S actionCost c
    (hafter.trans ht)
  have hpred : firstCrossing band S actionCost c ≤ t - 1 := by omega
  have hcost := (hmono action ha hpred).trans_lt hcross
  have hparent := hbellman (t - 1) (by omega) action ha
  have hindex : t - 1 + 1 = t := by omega
  rw [hindex] at hparent
  exact max_eq_left (hparent.trans hcost.le)

/-- A finite first-crossing partition charges the crossing only once.
All failure indicators may be correlated with the sampled actions. -/
theorem firstCrossing_sum_bound (S crossing : ℕ) (regret prefixPayoff failure : ℕ → ℝ)
    (crossingCharge failureCharge : ℝ) (hcrossing : crossing ≤ S)
    (hcharge : 0 ≤ crossingCharge) (hfailureCharge : 0 ≤ failureCharge)
    (hfailure : ∀ t < S, 0 ≤ failure t)
    (hprefixPayoff : ∀ t < crossing, regret t ≤ prefixPayoff t + failureCharge * failure t)
    (hcross : crossing < S → regret crossing ≤ crossingCharge + failureCharge * failure crossing)
    (hafter : ∀ t < S, crossing < t → regret t ≤ 0) :
    (∑ t ∈ range S, regret t) ≤
      (∑ t ∈ range crossing, prefixPayoff t) + crossingCharge +
        failureCharge * ∑ t ∈ range S, failure t := by
  have hpoint (t : ℕ) (ht : t ∈ range S) :
      regret t ≤ (if t < crossing then prefixPayoff t else 0) +
        (if t = crossing then crossingCharge else 0) + failureCharge * failure t := by
    have htS := mem_range.mp ht
    by_cases hbefore : t < crossing
    · simp only [hbefore, ite_true, show t ≠ crossing by omega, ite_false, add_zero]
      exact hprefixPayoff t hbefore
    · by_cases heq : t = crossing
      · subst t
        simpa only [lt_self_iff_false, ite_false, ite_true, zero_add] using hcross htS
      · simp only [hbefore, ite_false, heq, zero_add]
        exact (hafter t htS (by omega)).trans (mul_nonneg hfailureCharge (hfailure t htS))
  have hsum := sum_le_sum hpoint
  have hpre : (∑ t ∈ range S, if t < crossing then prefixPayoff t else 0) =
      ∑ t ∈ range crossing, prefixPayoff t := by
    rw [← sum_filter]
    congr 1
    ext t
    simp only [mem_filter, mem_range]
    omega
  have hcrossSum : (∑ t ∈ range S, if t = crossing then crossingCharge else 0) ≤ crossingCharge := by
    rw [sum_ite_eq']
    split_ifs
    · rfl
    · exact hcharge
  simp only [sum_add_distrib, ← mul_sum] at hsum
  rw [hpre] at hsum
  linarith

end EditApproximation

end OAI
