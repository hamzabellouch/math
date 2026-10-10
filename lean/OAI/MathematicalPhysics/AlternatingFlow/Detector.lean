import OAI.MathematicalPhysics.AlternatingFlow.Scales

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Detector

open Scales

noncomputable def increment (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) : ℝ :=
  ε b N n - ε b N (n + 1) + if halted n then 2 * ε b N (n + 1) else 0

noncomputable def signal (b N : ℕ) (halted : ℕ → Bool) : ℕ → ℝ
  | 0 => -ε b N 0
  | n + 1 => signal b N halted n + increment b N halted n

noncomputable def during (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) (θ : ℝ) : ℝ :=
  signal b N halted n + θ * increment b N halted n

noncomputable def loading (b N : ℕ) (θ : ℝ) : ℝ := -1 + θ * (1 - ε b N 0)

lemma signal_formula (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) :
    signal b N halted n = -ε b N n +
      2 * ∑ j ∈ Finset.range n, if halted j then ε b N (j + 1) else 0 := by
  induction n with
  | zero => simp [signal]
  | succ n ih =>
    simp only [signal, increment, ih, Finset.sum_range_succ]
    split_ifs <;> ring

lemma signal_before_halt (b N : ℕ) (halted : ℕ → Bool) (n : ℕ)
    (hn : ∀ j < n, halted j = false) : signal b N halted n = -ε b N n := by
  rw [signal_formula]
  have hsum : (∑ j ∈ Finset.range n, if halted j then ε b N (j + 1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [hn j (Finset.mem_range.1 hj)]
  rw [hsum]
  ring

lemma signal_first_halt (b N : ℕ) (halted : ℕ → Bool) (n : ℕ)
    (hprev : ∀ j < n, halted j = false) (hn : halted n = true) :
    signal b N halted (n + 1) = ε b N (n + 1) := by
  rw [signal, signal_before_halt b N halted n hprev]
  simp only [increment, hn, ite_true]
  ring

lemma increment_nonneg (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    0 ≤ increment b N halted n := by
  have hε := ε_strictAnti b N (by omega) (Nat.lt_succ_self n)
  have hp := ε_pos b N (n + 1) (by omega)
  simp only [Nat.succ_eq_add_one] at hε
  unfold increment
  split_ifs <;> linarith

lemma increment_le (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    increment b N halted n ≤ ε b N n + ε b N (n + 1) := by
  have hp := ε_pos b N (n + 1) (by omega)
  unfold increment
  split_ifs <;> linarith

lemma signal_monotone (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) :
    Monotone (signal b N halted) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [signal, le_add_iff_nonneg_right] using increment_nonneg b N hb halted n

lemma during_zero (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) :
    during b N halted n 0 = signal b N halted n := by simp [during]

lemma during_one (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) :
    during b N halted n 1 = signal b N halted (n + 1) := by simp [during, signal]

lemma during_before_halt (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ)
    (hn : ∀ j ≤ n, halted j = false) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) :
    during b N halted n θ < 0 := by
  have he := ε_strictAnti b N (by omega) (Nat.lt_succ_self n)
  have hp := ε_pos b N (n + 1) (by omega)
  simp only [Nat.succ_eq_add_one] at he
  have hm := mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr he.le)
  rw [during, signal_before_halt b N halted n (fun j hj => hn j hj.le)]
  simp only [increment, hn n le_rfl, Bool.false_eq_true, ↓reduceIte, add_zero]
  nlinarith

lemma loading_negative (b N : ℕ) (hb : 2 ≤ b) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) :
    loading b N θ < 0 := by
  have hp := ε_pos b N 0 (by omega)
  have hle := ε_le_geometric b N 0 hb
  norm_num at hle
  have hm := mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hle)
  unfold loading
  nlinarith

lemma scalar_reachability (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) :
    (∃ n : ℕ, ∃ θ ∈ Set.Icc (0 : ℝ) 1, 0 < during b N halted n θ) ↔
      ∃ n : ℕ, halted n = true := by
  constructor
  · rintro ⟨n, θ, hθ, hpos⟩
    by_contra h
    have hfalse : ∀ j, halted j = false := by
      intro j
      exact Bool.eq_false_iff.2 (fun hj => h ⟨j, hj⟩)
    exact (during_before_halt b N hb halted n (fun j _ => hfalse j) θ hθ).not_gt hpos
  · intro h
    let n := Nat.find h
    have hn : halted n = true := Nat.find_spec h
    have hprev : ∀ j < n, halted j = false :=
      fun j hj => Bool.eq_false_iff.2 (Nat.find_min h hj)
    refine ⟨n, 1, ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [during_one, signal_first_halt b N halted n hprev hn]
    exact ε_pos b N (n + 1) (by omega)

lemma signal_upper_bound (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    signal b N halted n ≤ 2 * ∑' j : ℕ, ε b N j := by
  have hsum : (∑ j ∈ Finset.range n, if halted j then ε b N (j + 1) else 0) ≤
      ∑ j ∈ Finset.range n, ε b N j := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact (ε_strictAnti b N (by omega) (Nat.lt_succ_self j)).le
    · exact ε_nonneg b N j (by omega)
  have htotal := (summable_ε b N hb).sum_le_tsum (Finset.range n)
    (fun j _ => ε_nonneg b N j (by omega))
  rw [signal_formula]
  linarith [ε_nonneg b N n (by omega)]

lemma signal_in_plateau (b N : ℕ) (hb : 4 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    signal b N halted n ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hl := signal_monotone b N (by omega) halted (Nat.zero_le n)
  have hu := signal_upper_bound b N (by omega) halted n
  have hsum := total_memory_le b N (by omega)
  have hs := initial_memory_small b N hb
  simp only [signal] at hl
  constructor <;> linarith

lemma during_in_plateau (b N : ℕ) (hb : 4 ≤ b) (halted : ℕ → Bool) (n : ℕ)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) : during b N halted n θ ∈ Set.Ioo (-1 : ℝ) 1 := by
  have h₀ := signal_in_plateau b N hb halted n
  have h₁ := signal_in_plateau b N hb halted (n + 1)
  have hi := increment_nonneg b N (by omega) halted n
  have hleft := mul_nonneg hθ.1 hi
  have hright := mul_nonneg (sub_nonneg.mpr hθ.2) hi
  simp only [signal] at h₁
  change -1 < signal b N halted n + θ * increment b N halted n ∧
    signal b N halted n + θ * increment b N halted n < 1
  constructor <;> nlinarith [h₀.1, h₁.2]

lemma machine_scalar_reachability (b : ℕ) (hb : 2 ≤ b) (M : Machine) (w : List ℕ) :
    (∃ n : ℕ, ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      0 < during b w.length (fun j => M.isHalting (M.run w j)) n θ) ↔ M.Halts w :=
  scalar_reachability b w.length hb (fun j => M.isHalting (M.run w j))

end Detector
end AlternatingNS

end OAI
