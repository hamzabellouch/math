import OAI.Probability.ThorpShuffle.FixedLists.Main

namespace OAI

open Filter

namespace Thorp

theorem full_mixing_later {C : ℕ} (hC : 1600 ≤ C) :
    Tendsto (fun d : ℕ => distance d (C * d)) atTop (nhds 0) := by
  apply squeeze_zero (fun d => by unfold distance tv; positivity) _ full_mixing
  intro d
  have ht : C * d = 1600 * d + (C - 1600) * d := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hC]
  rw [ht]
  exact distance_add_le d _ _

theorem random_coordinate_frames_main :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop, ∀ start : State d,
      tv (lawFrom d (32800 * d) start) (uniform d) < ε := by
  intro ε hε
  have h := (full_mixing_later (by norm_num : 1600 ≤ 32800)).eventually
    (eventually_lt_nhds hε)
  filter_upwards [h] with d hd start
  rwa [worst_start_eq]

theorem deterministic_coordinate_information_main :
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
        tv (lawFrom d (2048 * d) start) (uniform d) = distance d (2048 * d)) :=
  first_main

end Thorp

end OAI
