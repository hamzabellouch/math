import OAI.NumberTheory.JointDickman.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-!
# The deterministic moving-threshold sandwich

This is the comparison used in the last part of `distribution.tex`. It does
not assume any joint limit: it bounds the actual finite counts at the two
sets of thresholds, with the discarded initial segment explicitly counted.
-/

namespace JointDickman

open Filter
open scoped Topology

theorem eventually_power_lower {δ a c : ℝ} (hδ : 0 < δ) (hca : c < a) :
    ∀ᶠ x : ℝ in atTop, x ^ c ≤ (δ * x) ^ a := by
  have ht : Tendsto (fun x : ℝ => x ^ (c - a)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hca)
  have hp : 0 < δ ^ a := Real.rpow_pos_of_pos hδ _
  filter_upwards [ht.eventually (gt_mem_nhds hp), eventually_gt_atTop (0 : ℝ)]
    with x hx hxpos
  rw [Real.rpow_sub hxpos] at hx
  have hx' := (div_lt_iff₀ (Real.rpow_pos_of_pos hxpos a)).mp hx
  rw [Real.mul_rpow hδ.le hxpos.le]
  exact hx'.le

theorem movingEvent_implies_fixed {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a ≤ c) (hbd : b ≤ d) {N n : ℕ}
    (hn : n ∈ Finset.Icc 2 N) :
    movingEvent a b n → fixedScaleEvent c d N n := by
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by have := (Finset.mem_Icc.mp hn); omega)
  rintro ⟨h₁, h₂⟩
  constructor
  · exact h₁.trans ((Real.rpow_le_rpow hn0 hnN ha).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hac))
  · exact h₂.trans ((Real.rpow_le_rpow hn0 hnN hb).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hbd))

theorem fixedEvent_implies_moving_away_from_zero {δ a b c d : ℝ}
    (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hca : c < a) (hdb : d < b) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, δ * (N : ℝ) ≤ n →
      fixedScaleEvent c d N n → movingEvent a b n := by
  have hc := (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
    (eventually_power_lower hδ hca)
  have hd := (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
    (eventually_power_lower hδ hdb)
  filter_upwards [hc, hd] with N hN₁ hN₂ n hn hf
  constructor
  · exact hf.1.trans (hN₁.trans (Real.rpow_le_rpow
      (mul_nonneg hδ.le (Nat.cast_nonneg N)) hn ha))
  · exact hf.2.trans (hN₂.trans (Real.rpow_le_rpow
      (mul_nonneg hδ.le (Nat.cast_nonneg N)) hn hb))

private theorem count_le_count_add_bad {P Q B : ℕ → Prop} {N : ℕ}
    (h : ∀ n ∈ Finset.Icc 2 N, P n → Q n ∨ B n) :
    empiricalCount P N ≤ empiricalCount Q N + empiricalCount B N := by
  classical
  unfold empiricalCount
  calc
    _ ≤ (((Finset.Icc 2 N).filter Q) ∪ ((Finset.Icc 2 N).filter B)).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hnmem, hnP⟩ := Finset.mem_filter.mp hn
      rcases h n hnmem hnP with hnQ | hnB
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnmem, hnQ⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnmem, hnB⟩)
    _ ≤ _ := Finset.card_union_le _ _

theorem smallPrefix_count_le (δ : ℝ) (N : ℕ) :
    empiricalCount (fun n => (n : ℝ) < δ * N) N ≤ ⌊δ * N⌋₊ := by
  classical
  unfold empiricalCount
  have hsubset : (Finset.Icc 2 N).filter (fun n : ℕ => (n : ℝ) < δ * N) ⊆
      Finset.Icc 1 ⌊δ * N⌋₊ := by
    intro n hn
    obtain ⟨hnmem, hnlt⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hnmem).1; omega,
      Nat.le_floor hnlt.le⟩
  simpa using Finset.card_le_card hsubset

/-- The cost of changing fixed lower thresholds to moving thresholds is at
most the discarded initial segment. This is a finite-count estimate. -/
theorem fixedCount_le_moving_add_prefix {δ a b c d : ℝ}
    (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hca : c < a) (hdb : d < b) :
    ∀ᶠ N : ℕ in atTop,
      empiricalCount (fixedScaleEvent c d N) N ≤
        empiricalCount (movingEvent a b) N + ⌊δ * (N : ℝ)⌋₊ := by
  filter_upwards [fixedEvent_implies_moving_away_from_zero hδ ha hb hca hdb]
    with N hN
  apply le_trans (count_le_count_add_bad (B := fun n => (n : ℝ) < δ * N) ?_)
    (Nat.add_le_add_left (smallPrefix_count_le δ N) _)
  intro n _ hn
  by_cases hsmall : (n : ℝ) < δ * N
  · exact Or.inr hsmall
  · exact Or.inl (hN n (le_of_not_gt hsmall) hn)

theorem movingCount_le_fixed {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a ≤ c) (hbd : b ≤ d) (N : ℕ) :
    empiricalCount (movingEvent a b) N ≤ empiricalCount (fixedScaleEvent c d N) N :=
  empiricalCount_mono fun _ hn => movingEvent_implies_fixed ha hb hac hbd hn

end JointDickman

end OAI
