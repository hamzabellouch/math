import OAI.Combinatorics.LowSpaceSubsetSum.Search.Watchdog

namespace OAI

/-! # Termination and value preservation under an interrupting loop -/

namespace LowSpaceSubsetSum.Watchdog

variable {σ : Type*}

theorem terminates_of_ranking (step : σ → Transition σ) (rank : σ → ℕ)
    (hpos : ∀ s, 1 ≤ rank s)
    (hdec : ∀ s t, step s = .next t → rank t < rank s) (s : σ) :
    ∃ k ≤ rank s, ∃ b, TerminatesIn step k s b := by
  generalize hm : rank s = m
  induction m using Nat.strong_induction_on generalizing s with
  | h m ih =>
    cases ht : step s with
    | halt b => exact ⟨1, hm ▸ hpos s, b, .halt ht⟩
    | next t =>
      have hd : rank t < m := hm ▸ hdec s t ht
      obtain ⟨k, hk, b, hb⟩ := ih (rank t) hd t rfl
      exact ⟨k + 1, by omega, b, .next ht hb⟩

theorem terminates_value (step : σ → Transition σ) (value : σ → Bool)
    (hstep : ∀ s, match step s with
      | .halt b => value s = b
      | .next t => value s = value t)
    {k : ℕ} {s : σ} {b : Bool} (h : TerminatesIn step k s b) : value s = b := by
  induction h with
  | @halt s b h =>
    have hv := hstep s
    rw [h] at hv
    exact hv
  | @next s t k b h rest ih =>
    have hv := hstep s
    rw [h] at hv
    exact hv.trans ih

theorem ranked_complete (step : σ → Transition σ) (cells rank : σ → ℕ)
    (hpos : ∀ s, 1 ≤ rank s)
    (hdec : ∀ s t, step s = .next t → rank t < rank s)
    (value : σ → Bool)
    (hstep : ∀ s, match step s with
      | .halt b => value s = b
      | .next t => value s = value t)
    (s : σ) (budget : ℕ) (hbudget : rank s ≤ budget) :
    (run step cells budget s).output = some (value s) := by
  obtain ⟨k, hk, b, hb⟩ := terminates_of_ranking step rank hpos hdec s
  have hv := terminates_value step value hstep hb
  rw [hv]
  exact complete step cells hb budget (hk.trans hbudget)

end LowSpaceSubsetSum.Watchdog

end OAI
