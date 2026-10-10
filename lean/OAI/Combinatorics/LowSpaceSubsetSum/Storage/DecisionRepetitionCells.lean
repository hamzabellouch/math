import OAI.Combinatorics.LowSpaceSubsetSum.Search.DecisionRepetition

namespace OAI

/-! # Reusing one round's workspace in the tail-counter repetition

The read-only draws are addressed by the offset counter. A finished round's
workspace is released before advancing to the next draw.
-/

namespace LowSpaceSubsetSum.DecisionRepetitionCells

variable {Ω : Type*} {k : ℕ}

abbrev Execution := (Bool × ℕ) × ℕ

def loop (step : Ω → Execution) (draws : Fin k → Ω) :
    (remaining offset : ℕ) → offset + remaining ≤ k → ℕ → ℕ → Execution
  | 0, _, _, work, peak => ((false, work + 1), max peak 8)
  | remaining + 1, offset, h, work, peak =>
    let out := step (draws ⟨offset, by omega⟩)
    let used := max peak (out.2 + 8)
    if out.1.1 then ((true, work + out.1.2 + 1), used)
    else loop step draws remaining (offset + 1) (by omega) (work + out.1.2 + 1) used

def run (step : Ω → Execution) (draws : Fin k → Ω) :=
  loop step draws k 0 (by omega) 0 8

theorem loop_value (step : Ω → Execution) (draws : Fin k → Ω)
    (remaining offset : ℕ) (h : offset + remaining ≤ k) (work peak : ℕ) :
    (loop step draws remaining offset h work peak).1 =
      DecisionRepetition.loop (fun x => (step x).1) draws remaining offset h work := by
  induction remaining generalizing offset work peak with
  | zero => rfl
  | succ remaining ih =>
    rw [loop, DecisionRepetition.loop]
    split
    · rfl
    · exact ih _ _ _ _

theorem value (step : Ω → Execution) (draws : Fin k → Ω) :
    (run step draws).1 = DecisionRepetition.run (fun x => (step x).1) draws :=
  loop_value step draws k 0 (by omega) 0 8

theorem loop_cells (step : Ω → Execution) (draws : Fin k → Ω) (L : ℕ)
    (hL : ∀ x, (step x).2 ≤ L) (remaining offset : ℕ)
    (h : offset + remaining ≤ k) (work peak : ℕ) :
    (loop step draws remaining offset h work peak).2 ≤ max peak (L+8) := by
  induction remaining generalizing offset work peak with
  | zero =>
    exact max_le_max_left peak (by omega)
  | succ remaining ih =>
    have hx := hL (draws ⟨offset, by omega⟩)
    rw [loop]
    split
    · exact max_le_max_left peak (by omega)
    · exact (ih _ _ _ _).trans (max_le (max_le (le_max_left _ _) (by omega)) (le_max_right _ _))

theorem cells (step : Ω → Execution) (draws : Fin k → Ω) (L : ℕ)
    (hL : ∀ x, (step x).2 ≤ L) : (run step draws).2 ≤ L+8 := by
  exact (loop_cells step draws L hL k 0 (by omega) 0 8).trans (max_le (by omega) le_rfl)

end LowSpaceSubsetSum.DecisionRepetitionCells

end OAI
