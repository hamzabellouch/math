import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace OAI

/-! # Interrupting the finite transition loop

The wrapper executes at most its supplied number of transitions. A timeout
rejects. The completeness lemma requires the underlying run to terminate
within that same budget; no after-the-fact cost computation is performed.
-/

namespace LowSpaceSubsetSum.Watchdog

variable {σ : Type*}

inductive Transition (σ : Type*)
  | halt : Bool → Transition σ
  | next : σ → Transition σ

structure Result (σ : Type*) where
  output : Option Bool
  state : σ
  steps : ℕ
  peak : ℕ

def run (step : σ → Transition σ) (cells : σ → ℕ) : ℕ → σ → Result σ
  | 0, s => ⟨none, s, 0, cells s⟩
  | k + 1, s =>
    match step s with
    | .halt b => ⟨some b, s, 1, cells s⟩
    | .next t =>
      let rest := run step cells k t
      ⟨rest.output, rest.state, rest.steps + 1, max (cells s) rest.peak⟩

def accepted (out : Result σ) : Bool := out.output.getD false

theorem steps_le (step : σ → Transition σ) (cells : σ → ℕ) (k : ℕ) (s : σ) :
    (run step cells k s).steps ≤ k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [run]
    split
    · exact Nat.succ_le_succ (Nat.zero_le _)
    · exact Nat.add_le_add_right (ih _) 1

theorem peak_le (step : σ → Transition σ) (cells : σ → ℕ)
    (Inv : σ → Prop) (S : ℕ)
    (hnext : ∀ s t, Inv s → step s = .next t → Inv t)
    (hcell : ∀ s, Inv s → cells s ≤ S) (k : ℕ) (s : σ) (hs : Inv s) :
    (run step cells k s).peak ≤ S := by
  induction k generalizing s with
  | zero => exact hcell s hs
  | succ k ih =>
    cases ht : step s with
    | halt b => simpa only [run, ht] using hcell s hs
    | next t =>
      simp only [run, ht]
      exact max_le (hcell s hs) (ih t (hnext s t hs ht))

theorem sound (step : σ → Transition σ) (cells : σ → ℕ)
    (Inv : σ → Prop) (P : Prop)
    (hnext : ∀ s t, Inv s → step s = .next t → Inv t)
    (hyes : ∀ s, Inv s → step s = .halt true → P)
    (k : ℕ) (s : σ) (hs : Inv s)
    (haccept : accepted (run step cells k s) = true) : P := by
  induction k generalizing s with
  | zero => simp [accepted, run] at haccept
  | succ k ih =>
    cases ht : step s with
    | halt b =>
      have hb : b = true := by simpa only [accepted, run, ht, Option.getD_some] using haccept
      subst b
      exact hyes s hs ht
    | next t =>
      apply ih t (hnext s t hs ht)
      simpa only [accepted, run, ht] using haccept

inductive TerminatesIn (step : σ → Transition σ) : ℕ → σ → Bool → Prop
  | halt {s b} (h : step s = .halt b) : TerminatesIn step 1 s b
  | next {s t k b} (h : step s = .next t) (rest : TerminatesIn step k t b) :
      TerminatesIn step (k + 1) s b

theorem complete (step : σ → Transition σ) (cells : σ → ℕ)
    {k : ℕ} {s : σ} {b : Bool} (h : TerminatesIn step k s b)
    (budget : ℕ) (hk : k ≤ budget) : (run step cells budget s).output = some b := by
  induction h generalizing budget with
  | halt h =>
    cases budget with
    | zero => omega
    | succ budget => simp only [run, h]
  | next h rest ih =>
    cases budget with
    | zero => omega
    | succ budget =>
      simp only [run, h]
      exact ih budget (by omega)

end LowSpaceSubsetSum.Watchdog

end OAI
