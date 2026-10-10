import OAI.MathematicalPhysics.NavierStokes.Material.Scales

namespace OAI

namespace Alternating.Memory
open scoped BigOperators
open Finset

noncomputable def signalIncrement (b N : ℕ) (halt : ℕ → Bool) (n : ℕ) : ℝ :=
  epsilon b N n - epsilon b N (n + 1) +
    if halt n then 2 * epsilon b N (n + 1) else 0

noncomputable def signal (b N : ℕ) (halt : ℕ → Bool) : ℕ → ℝ
  | 0 => -epsilon b N 0
  | n + 1 => signal b N halt n + signalIncrement b N halt n

noncomputable def signalAlong (b N : ℕ) (halt : ℕ → Bool) (n : ℕ) (u : ℝ) : ℝ :=
  (1 - u) * signal b N halt n + u * signal b N halt (n + 1)

@[simp] theorem signalAlong_zero (b N : ℕ) (halt : ℕ → Bool) (n : ℕ) :
    signalAlong b N halt n 0 = signal b N halt n := by simp [signalAlong]

@[simp] theorem signalAlong_one (b N : ℕ) (halt : ℕ → Bool) (n : ℕ) :
    signalAlong b N halt n 1 = signal b N halt (n + 1) := by simp [signalAlong]

theorem signalIncrement_bounds {b : ℕ} (hb : 2 ≤ b) (N : ℕ) (halt : ℕ → Bool) (n : ℕ) :
    0 ≤ signalIncrement b N halt n ∧
      signalIncrement b N halt n ≤ epsilon b N n + epsilon b N (n + 1) := by
  have he := (epsilon_strictAnti hb N (Nat.lt_succ_self n)).le
  have he0 := epsilon_nonneg (by omega : 0 < b) N (n + 1)
  cases hh : halt n <;> simp [signalIncrement, hh] <;> constructor <;> linarith

theorem signalIncrement_le {b : ℕ} (hb : 2 ≤ b) (N : ℕ) (halt : ℕ → Bool) (n : ℕ) :
    signalIncrement b N halt n ≤ 2 * epsilon b N n := by
  have he := (epsilon_strictAnti hb N (Nat.lt_succ_self n)).le
  have h := (signalIncrement_bounds hb N halt n).2
  linarith

theorem signal_bounds {b : ℕ} (hb : 2 ≤ b) (N : ℕ) (halt : ℕ → Bool) (n : ℕ) :
    -epsilon b N 0 ≤ signal b N halt n ∧
    signal b N halt n ≤ -epsilon b N 0 + 2 * ∑ j ∈ range n, epsilon b N j := by
  induction n with
  | zero => simp [signal]
  | succ n ih =>
    rw [signal, sum_range_succ]
    have h1 := (signalIncrement_bounds hb N halt n).1
    have h2 := signalIncrement_le hb N halt n
    constructor <;> linarith [ih.1, ih.2]

theorem signal_mem {b : ℕ} (hb : 4 ≤ b) (N : ℕ) (halt : ℕ → Bool) (n : ℕ) :
    signal b N halt n ∈ Set.Ioo (-1 : ℝ) 1 := by
  have h := signal_bounds (by omega : 2 ≤ b) N halt n
  have hs := epsilon_sum_range_le (by omega : 2 ≤ b) N n
  have he := initial_epsilon_small hb N
  constructor <;> linarith [h.1, h.2]

theorem signalAlong_mem {b : ℕ} (hb : 4 ≤ b) (N : ℕ) (halt : ℕ → Bool) (n : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc 0 1) : signalAlong b N halt n u ∈ Set.Ioo (-1 : ℝ) 1 := by
  exact (convex_Ioo (-1 : ℝ) 1) (signal_mem hb N halt n) (signal_mem hb N halt (n + 1))
    (by linarith [hu.2] : 0 ≤ 1 - u) hu.1 (by ring)

theorem signal_unhalted (b N : ℕ) (halt : ℕ → Bool) (n : ℕ)
    (hn : ∀ j < n, halt j = false) : signal b N halt n = -epsilon b N n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [signal, ih (fun j hj => hn j (by omega))]
    simp [signalIncrement, hn n (by omega)]
    ring

theorem signalAlong_unhalted {b : ℕ} (hb : 0 < b) (N : ℕ) (halt : ℕ → Bool) (n : ℕ)
    (hn : ∀ j ≤ n, halt j = false) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    signalAlong b N halt n u < 0 := by
  have h0 : signal b N halt n < 0 := by
    rw [signal_unhalted b N halt n (fun j hj => hn j (by omega))]
    exact neg_neg_of_pos (epsilon_pos hb N n)
  have h1 : signal b N halt (n + 1) < 0 := by
    rw [signal_unhalted b N halt (n + 1) (fun j hj => hn j (by omega))]
    exact neg_neg_of_pos (epsilon_pos hb N (n + 1))
  change (1 - u) * signal b N halt n + u * signal b N halt (n + 1) < 0
  rcases hu.1.eq_or_lt with h | h
  · rw [← h]; simpa using h0
  · exact add_neg_of_nonpos_of_neg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith [hu.2]) h0.le)
      (mul_neg_of_pos_of_neg h h1)

theorem signal_first_halt (b N : ℕ) (halt : ℕ → Bool) (n : ℕ)
    (hn : ∀ j < n, halt j = false) (hh : halt n = true) :
    signal b N halt (n + 1) = epsilon b N (n + 1) := by
  rw [signal, signal_unhalted b N halt n hn]
  simp [signalIncrement, hh]
  ring

theorem signal_hit_iff {b : ℕ} (hb : 0 < b) (N : ℕ) (halt : ℕ → Bool) :
    (∃ (n : ℕ) (u : ℝ), u ∈ Set.Icc 0 1 ∧ 0 < signalAlong b N halt n u) ↔
      ∃ n : ℕ, halt n = true := by
  constructor
  · rintro ⟨n, u, hu, hpos⟩
    by_contra hh
    have hn : ∀ j ≤ n, halt j = false := by
      intro j _
      exact Bool.eq_false_iff.2 (fun hj => hh ⟨j, hj⟩)
    have hneg := signalAlong_unhalted hb N halt n hn hu
    linarith
  · intro hh
    let n := Nat.find hh
    have hn : ∀ j < n, halt j = false := by
      intro j hj
      exact Bool.eq_false_iff.2 (Nat.find_min hh hj)
    have hh' : halt n = true := Nat.find_spec hh
    refine ⟨n, 1, ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [signalAlong_one, signal_first_halt b N halt n hn hh']
    exact epsilon_pos hb N (n + 1)

end Alternating.Memory

end OAI
