import OAI.Probability.ThorpShuffle.FixedLists.Lists
import OAI.Probability.ThorpShuffle.FixedLists.FullDeck

namespace OAI


noncomputable section
open scoped BigOperators
open Filter

namespace Thorp
namespace FixedLists

lemma eventually_unshift {P : ℕ → Prop}
    (h : ∀ᶠ d : ℕ in atTop, P (d + 4)) : ∀ᶠ d : ℕ in atTop, P d := by
  rw [← map_add_atTop_eq_nat 4]
  exact h

lemma lists_256_uniform :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
      ∀ k : ℕ, 8 * k ≤ 7 * 2 ^ d →
      ∀ (start : State d) (labels : LabelList d k),
        listTV (256 * d) start labels < ε := by
  intro ε hε
  apply eventually_unshift
  have he : ∀ᶠ d : ℕ in atTop, listRate d < ε :=
    listRate_tendsto.eventually (eventually_lt_nhds hε)
  filter_upwards [he] with d hd
  intro k hk start labels
  have hk' : 16 * k ≤ 15 * 2 ^ (d + 4) := by omega
  exact (listTV_256 d k hk' start labels).trans_lt hd

lemma lists_1024_uniform :
    ∀ᶠ d : ℕ in atTop,
      ∀ k : ℕ, 16 * k ≤ 15 * 2 ^ d →
      ∀ (start : State d) (labels : LabelList d k),
        listTV (1024 * d) start labels ≤ Real.rpow ((2 : ℝ) ^ d) (-(3 : ℝ) / 2) :=
  eventually_unshift listTV_1024_eventually

end FixedLists

theorem first_main :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
      ∀ k : ℕ, 8 * k ≤ 7 * 2 ^ d →
      ∀ (start : State d) (labels : LabelList d k),
        listTV (256 * d) start labels < ε) ∧
    (∀ᶠ d : ℕ in atTop,
      ∀ k : ℕ, 16 * k ≤ 15 * 2 ^ d →
      ∀ (start : State d) (labels : LabelList d k),
        listTV (1024 * d) start labels ≤ Real.rpow ((2 : ℝ) ^ d) (-(3 : ℝ) / 2)) ∧
    (Tendsto (fun d : ℕ => distance d (2048 * d)) atTop (nhds 0) ∧
      ∀ (d : ℕ) (start : State d),
        tv (lawFrom d (2048 * d) start) (uniform d) = distance d (2048 * d)) := by
  exact ⟨FixedLists.lists_256_uniform, FixedLists.lists_1024_uniform,
    full_mixing_2048, fun d start => worst_start_eq d (2048 * d) start⟩

end Thorp

end

end OAI
