import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteRepetition

namespace OAI

/-! # Tail-counter repetition without a stored list of round indices -/

namespace LowSpaceSubsetSum.DecisionRepetition

variable {Ω : Type*} {k : ℕ}

def loop (step : Ω → Bool × ℕ) (draws : Fin k → Ω) :
    (remaining offset : ℕ) → offset + remaining ≤ k → ℕ → Bool × ℕ
  | 0, _, _, work => (false, work + 1)
  | remaining + 1, offset, h, work =>
    let out := step (draws ⟨offset, by omega⟩)
    if out.1 then (true, work + out.2 + 1)
    else loop step draws remaining (offset + 1) (by omega) (work + out.2 + 1)

def run (step : Ω → Bool × ℕ) (draws : Fin k → Ω) := loop step draws k 0 (by omega) 0

theorem loop_sound (step : Ω → Bool × ℕ) (draws : Fin k → Ω)
    (remaining offset : ℕ) (h : offset + remaining ≤ k) (work : ℕ)
    (hy : (loop step draws remaining offset h work).1 = true) :
    ∃ i : Fin k, offset ≤ i.val ∧ i.val < offset + remaining ∧ (step (draws i)).1 = true := by
  induction remaining generalizing offset work with
  | zero => simp only [loop, Bool.false_eq_true] at hy
  | succ remaining ih =>
    simp only [loop] at hy
    split at hy
    next hyes =>
      exact ⟨⟨offset, by omega⟩, le_rfl, Nat.lt_succ_of_le (Nat.le_add_right offset remaining), hyes⟩
    next hno =>
      obtain ⟨i, hil, hiu, hi⟩ := ih (offset + 1) (by omega) _ hy
      exact ⟨i, by omega, by omega, hi⟩

theorem loop_complete (step : Ω → Bool × ℕ) (draws : Fin k → Ω)
    (remaining offset : ℕ) (h : offset + remaining ≤ k) (work : ℕ)
    (i : Fin k) (hil : offset ≤ i.val) (hiu : i.val < offset + remaining)
    (hy : (step (draws i)).1 = true) : (loop step draws remaining offset h work).1 = true := by
  induction remaining generalizing offset work with
  | zero => omega
  | succ remaining ih =>
    simp only [loop]
    split
    · rfl
    next hno =>
      have hne : i.val ≠ offset := by
        intro he
        have hi : i = ⟨offset, by omega⟩ := Fin.ext he
        exact hno (by simpa only [← hi] using hy)
      exact ih (offset + 1) (by omega) _ (by omega) (by omega)

theorem value (step : Ω → Bool × ℕ) (draws : Fin k → Ω) :
    (run step draws).1 = repeatAccept (fun x => (step x).1) draws := by
  apply Bool.eq_iff_iff.mpr
  rw [repeatAccept_eq_true]
  constructor
  · intro hy
    obtain ⟨i, _, _, hi⟩ := loop_sound step draws k 0 (by omega) 0 hy
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact loop_complete step draws k 0 (by omega) 0 i (Nat.zero_le _) (by simpa only [Nat.zero_add] using i.isLt) hi

theorem loop_work (step : Ω → Bool × ℕ) (draws : Fin k → Ω) (T : ℕ)
    (hT : ∀ x, (step x).2 ≤ T) (remaining offset : ℕ)
    (h : offset + remaining ≤ k) (work : ℕ) :
    (loop step draws remaining offset h work).2 ≤ work + remaining * (T + 1) + 1 := by
  induction remaining generalizing offset work with
  | zero => simp only [loop, Nat.zero_mul, Nat.add_zero, le_refl]
  | succ remaining ih =>
    have ht := hT (draws ⟨offset, by omega⟩)
    simp only [loop]
    split
    · dsimp only
      nlinarith only [ht]
    · have hi := ih (offset + 1) (by omega) (work + (step (draws ⟨offset, by omega⟩)).2 + 1)
      nlinarith only [ht, hi]

theorem work (step : Ω → Bool × ℕ) (draws : Fin k → Ω) (T : ℕ)
    (hT : ∀ x, (step x).2 ≤ T) : (run step draws).2 ≤ k * (T + 1) + 1 := by
  simpa only [run, Nat.zero_add] using loop_work step draws T hT k 0 (by omega) 0

end LowSpaceSubsetSum.DecisionRepetition

end OAI
