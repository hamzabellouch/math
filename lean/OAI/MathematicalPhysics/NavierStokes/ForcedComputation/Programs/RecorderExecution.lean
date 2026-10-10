import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderRun

namespace OAI

/-! The executable recorder orbit and its halting equivalence. -/

namespace ForcedComputation.Recorder

variable {Q A : Type*} [DecidableEq Q] [DecidableEq A]

def nextConfiguration (M : Machine Q A) (C : Configuration Q A) : Configuration Q A :=
  match evalLocal M C.control (C.tape C.head) with
  | none => C
  | some (q, a, d) => ⟨q, C.head + d, Function.update C.tape C.head a⟩

def run (M : Machine Q A) (C : Configuration Q A) (n : ℕ) : Configuration Q A :=
  (nextConfiguration M)^[n] C

theorem run_zero (M : Machine Q A) (C : Configuration Q A) : run M C 0 = C := rfl

theorem run_succ (M : Machine Q A) (C : Configuration Q A) (n : ℕ) :
    run M C (n + 1) = nextConfiguration M (run M C n) :=
  Function.iterate_succ_apply' _ _ _

theorem Step.next_eq {M : Machine Q A} {C D : Configuration Q A} (h : Step M C D) :
    nextConfiguration M C = D := by
  obtain ⟨q, a, d, hl, rfl⟩ := h
  simp only [nextConfiguration, hl.eval]

theorem Steps.run_eq {M : Machine Q A} {C D : Configuration Q A} {n : ℕ}
    (h : Steps M n C D) : run M C n = D := by
  induction h with
  | zero => rfl
  | next h hs ih => rw [run_succ, ih, hs.next_eq]

theorem reachable_has_successor_of_nonhalting (M : Machine Q A) (q : Q) (w : ℤ → A)
    (g₀ : ℤ) (hg₀ : 2 ≤ g₀)
    (hn : ∀ n, M.halting (workAt M q w n).state = false)
    {m : ℕ} {C : Configuration Q A} (hC : Steps M m (checkpointAt M q w g₀ 0) C) :
    ∃ D, Step M C D := by
  obtain ⟨k, hk, hlong⟩ := simulate_prefix_length M q w g₀ hg₀ (m + 1)
    (fun i _ => hn i)
  exact hC.prefix_has_successor hlong (by omega)

theorem run_steps_of_nonhalting (M : Machine Q A) (q : Q) (w : ℤ → A)
    (g₀ : ℤ) (hg₀ : 2 ≤ g₀)
    (hn : ∀ n, M.halting (workAt M q w n).state = false) (n : ℕ) :
    Steps M n (checkpointAt M q w g₀ 0) (run M (checkpointAt M q w g₀ 0) n) := by
  induction n with
  | zero => exact Steps.zero _
  | succ n ih =>
    obtain ⟨D, hD⟩ := reachable_has_successor_of_nonhalting M q w g₀ hg₀ hn ih
    rw [run_succ, hD.next_eq]
    exact Steps.next ih hD

theorem run_step_of_nonhalting (M : Machine Q A) (q : Q) (w : ℤ → A)
    (g₀ : ℤ) (hg₀ : 2 ≤ g₀)
    (hn : ∀ n, M.halting (workAt M q w n).state = false) (n : ℕ) :
    Step M (run M (checkpointAt M q w g₀ 0) n)
      (run M (checkpointAt M q w g₀ 0) (n + 1)) := by
  obtain ⟨D, hD⟩ := reachable_has_successor_of_nonhalting M q w g₀ hg₀ hn
    (run_steps_of_nonhalting M q w g₀ hg₀ hn n)
  rw [run_succ, hD.next_eq]
  exact hD

theorem run_halting_iff (M : Machine Q A) (q : Q) (w : ℤ → A)
    (g₀ : ℤ) (hg₀ : 2 ≤ g₀) :
    (∃ n, haltingControl M (run M (checkpointAt M q w g₀ 0) n).control = true) ↔
      ∃ n, M.halting (workAt M q w n).state = true := by
  constructor
  · rintro ⟨n, hterminal⟩
    by_contra hnone
    have hn (k : ℕ) : M.halting (workAt M q w k).state = false := by
      cases he : M.halting (workAt M q w k).state with
      | false => rfl
      | true => exact False.elim (hnone ⟨k, he⟩)
    obtain ⟨_, _, _, hl, _⟩ := run_step_of_nonhalting M q w g₀ hg₀ hn n
    have hf := hl.source_nonhalting
    rw [hterminal] at hf
    cases hf
  · intro hhalt
    obtain ⟨n, C, q', hC, hq', hh⟩ :=
      (halting_checkpoint_iff M q w g₀ hg₀).mpr hhalt
    refine ⟨n, ?_⟩
    rw [hC.run_eq, hq']
    exact hh

end ForcedComputation.Recorder

end OAI
