import Mathlib.Data.Fintype.Basic
import OAI.Computability.BinPacking.Reductions.MachineSubstitution

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineFiniteTable

open Turing
open BinPackingGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K] [DecidableEq σ]
variable {Γ : K → Type}

def dispatch (dst : K) (table : σ → List (Γ dst))
    (next : TM2.Stmt Γ Λ σ) : List σ → TM2.Stmt Γ Λ σ
  | [] => next
  | key :: rest =>
      .branch (fun state => decide (state = key))
        (pushWord dst (table key).reverse next) (dispatch dst table next rest)

theorem stepAux_dispatch (dst : K) (table : σ → List (Γ dst))
    (next : TM2.Stmt Γ Λ σ) (keys : List σ) (state : σ)
    (hstate : state ∈ keys) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (dispatch dst table next keys) state tapes =
      TM2.stepAux next state (Function.update tapes dst (table state ++ tapes dst)) := by
  induction keys with
  | nil => simp at hstate
  | cons key rest ih =>
      by_cases h : state = key
      · subst state
        simp only [dispatch, TM2.stepAux, decide_true, Bool.cond_true]
        simpa only [List.reverse_reverse] using
          stepAux_pushWord dst (table key).reverse next key tapes
      · have hm : state ∈ rest := (List.mem_cons.mp hstate).resolve_left h
        simpa only [dispatch, TM2.stepAux, h, decide_false, Bool.cond_false] using ih hm

omit [DecidableEq K] in

theorem dispatch_push_bound (dst : K) (table : σ → List (Γ dst))
    (next : TM2.Stmt Γ Λ σ) (keys : List σ) :
    Runtime.statementPushBound (dispatch dst table next keys) ≤
      (keys.map (fun state => (table state).length)).sum +
        Runtime.statementPushBound next := by
  induction keys with
  | nil => simp [dispatch]
  | cons key rest ih =>
      simp only [dispatch, Runtime.statementPushBound, statementPushBound_pushWord,
        List.length_reverse, List.map_cons, List.sum_cons]
      apply max_le <;> omega

def emit (dst : K) (table : σ → List (Γ dst)) (keys : List σ)
    (next : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ :=
  dispatch dst table next keys

def tableBound (dst : K) (table : σ → List (Γ dst)) (keys : List σ) : ℕ :=
  (keys.map (fun state => (table state).length)).sum

theorem stepAux_emit (dst : K) (table : σ → List (Γ dst))
    (keys : List σ) (hkeys : ∀ state, state ∈ keys) (next : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (emit dst table keys next) state tapes =
      TM2.stepAux next state (Function.update tapes dst (table state ++ tapes dst)) :=
  stepAux_dispatch dst table next keys state (hkeys state) tapes

omit [DecidableEq K] in
theorem emit_push_bound (dst : K) (table : σ → List (Γ dst))
    (keys : List σ) (next : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (emit dst table keys next) ≤
      tableBound dst table keys + Runtime.statementPushBound next :=
  dispatch_push_bound dst table next _

def emitInTime (dst : K) (table : σ → List (Γ dst))
    (keys : List σ) (hkeys : ∀ state, state ∈ keys)
    (program : Λ → TM2.Stmt Γ Λ σ) (label exitLabel : Λ)
    (atLabel : program label = emit dst table keys (.goto (fun _ => exitLabel)))
    (state : σ) (tapes : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, state, tapes⟩
      (some ⟨some exitLabel, state,
        Function.update tapes dst (table state ++ tapes dst)⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program label) state tapes) = _
    rw [atLabel, stepAux_emit dst table keys hkeys]
    rfl
  steps_le_m := Nat.le_refl _

omit [DecidableEq σ] in
theorem output_frame (dst : K) (table : σ → List (Γ dst))
    (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) (h : k ≠ dst) :
    (Function.update tapes dst (table state ++ tapes dst)) k = tapes k := by
  simp [Function.update, h]

end BinPackingGames.Foundations.Complexity.MachineFiniteTable

end OAI
