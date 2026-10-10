import OAI.Computability.BinPacking.Reductions.BinaryTokenMachine

namespace OAI

namespace BinPackingGap.FrameEmitMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => (state.1, none))
    (match exit with | none => .halt | some label => .goto fun _ => label)

def instruction (source output : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push output (fun _ => true)
        (.push output (fun state => state.2.getD false) (finish (some again))))
      (.push output (fun _ => false) (finish exit)))

variable (source output : K) (distinct : source ≠ output)
variable (again : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabel : program again = instruction source output again exit)
variable (base : K → List Bool) (ambient : A)

include distinct in
private theorem update_source (input acc next : List Bool) :
    Function.update (tapesAt source output base input acc) source next =
      tapesAt source output base next acc := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases ho : k = output
    · subst k; simp [tapesAt, hs]
    · simp [tapesAt, hs, ho]

private theorem update_output (input acc next : List Bool) :
    Function.update (tapesAt source output base input acc) output next =
      tapesAt source output base input next := by
  simp [tapesAt]

include distinct atLabel

theorem step_nil (acc : List Bool) :
    TM2.step program
      ⟨some again, (ambient, none), tapesAt source output base [] acc⟩ =
      some ⟨exit, (ambient, none), tapesAt source output base [] (false :: acc)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLabel]
  cases exit <;>
    simp [instruction, finish, TM2.stepAux, tapesAt_src, tapesAt_dst,
      distinct, update_source, update_output]

theorem step_cons (bit : Bool) (input acc : List Bool) :
    TM2.step program
      ⟨some again, (ambient, none), tapesAt source output base (bit :: input) acc⟩ =
      some ⟨some again, (ambient, none),
        tapesAt source output base input (bit :: true :: acc)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLabel]
  simp [instruction, finish, TM2.stepAux, tapesAt_src, tapesAt_dst,
    distinct, update_source, update_output]

theorem trace (input acc : List Bool) :
    (advance (TM2.step program))^[input.length + 1]
      (some ⟨some again, (ambient, none), tapesAt source output base input acc⟩) =
      some ⟨exit, (ambient, none), tapesAt source output base []
        ((BinPackingCompleteness.BinaryEncoding.frame input).reverse ++ acc)⟩ := by
  induction input generalizing acc with
  | nil =>
      simpa [advance, BinPackingCompleteness.BinaryEncoding.frame] using
        step_nil source output distinct again exit program atLabel base ambient acc
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_cons source output distinct again exit program atLabel base ambient]
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using ih (bit :: true :: acc)

def inTime (input acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, none), tapesAt source output base input acc⟩
      (some ⟨exit, (ambient, none), tapesAt source output base []
        ((BinPackingCompleteness.BinaryEncoding.frame input).reverse ++ acc)⟩)
      (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := trace source output distinct again exit program atLabel base ambient input acc
  steps_le_m := Nat.le_refl _

end BinPackingGap.FrameEmitMachine

end OAI
