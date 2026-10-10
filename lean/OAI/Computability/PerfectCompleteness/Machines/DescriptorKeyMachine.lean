import OAI.Computability.PerfectCompleteness.Machines.CanonicalKeyMachine

namespace OAI


namespace PerfectCompleteness.DescriptorKeyMachine


open Turing UniqueGamesTheorem.Foundations.Complexity MachineComposition
open CanonicalKeys CanonicalKeyShape ClauseSupport
open scoped Classical

noncomputable section

variable {n : Nat} {α K Λ σ : Type} [DecidableEq K]

inductive Label (α : Type) (n : Nat)
  | dispatch
  | key (descriptor : α) (localLabel : CanonicalKeyMachine.Label n)
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := KeyMetadataMachine.State σ

def start (n : Nat) : CanonicalKeyMachine.Label n := .inl ()

@[simp] theorem entry_eq (placed : CanonicalKeyMachine.Label n → Λ) (exit : Option Λ) :
    CanonicalKeyMachine.entry placed exit = some (placed (start n)) := rfl

def instruction (select : σ → α) (shapes : α → Fin n → Shape)
    (modes : α → Fin n → SupportMode) (side : α → Side)
    (partition : α → Set (Set (Fin n → ReducedValue)))
    (tape : Fin n → Fin 6 → K) (output : K)
    (labels : Label α n → Λ) (exit : Option Λ) :
    Label α n → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .dispatch => .goto (fun state => labels (.key (select state.1) (start n)))
  | .key descriptor localLabel =>
      CanonicalKeyMachine.instruction (shapes descriptor) (modes descriptor)
        (side descriptor) (partition descriptor) tape output
        (fun l => labels (.key descriptor l)) exit localLabel

def payload (select : σ → α) (shapes : α → Fin n → Shape)
    (modes : α → Fin n → SupportMode) (side : α → Side)
    (partition : α → Set (Set (Fin n → ReducedValue)))
    (ambient : σ) (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat) : List Bool :=
  CanonicalKeyMachine.payload (shapes (select ambient)) (modes (select ambient))
    (side (select ambient)) (partition (select ambient)) occurrences variableIDs

theorem dispatch_step (select : σ → α) (shapes : α → Fin n → Shape)
    (modes : α → Fin n → SupportMode) (side : α → Side)
    (partition : α → Set (Set (Fin n → ReducedValue)))
    (tape : Fin n → Fin 6 → K) (output : K)
    (labels : Label α n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atDispatch : program (labels .dispatch) =
      instruction select shapes modes side partition tape output labels exit .dispatch)
    (base : K → List Bool) (ambient : σ) :
    TM2.step program ⟨some (labels .dispatch), KeyMetadataMachine.clean ambient, base⟩ =
      some ⟨CanonicalKeyMachine.entry (fun l => labels (.key (select ambient) l)) exit,
        KeyMetadataMachine.clean ambient, base⟩ := by
  change some (TM2.stepAux (program (labels .dispatch))
    (KeyMetadataMachine.clean ambient) base) = _
  rw [atDispatch]
  rfl

private def prefixOne {X : Type} (step : X → Option X)
    {initial middle : X} {final : Option X} {budget : Nat}
    (first : step initial = some middle)
    (body : StateTransition.EvalsToInTime step middle final budget) :
    StateTransition.EvalsToInTime step initial final (1 + budget) := by
  refine
    { steps := 1 + body.steps
      evals_in_steps := ?_
      steps_le_m := Nat.add_le_add_left body.steps_le_m 1 }
  change (advance step)^[1 + body.steps] (some initial) = final
  rw [Nat.add_comm 1 body.steps, Function.iterate_add_apply,
    Function.iterate_one, advance_some, first]
  exact body.evals_in_steps

def keyInTime (select : σ → α) (shapes : α → Fin n → Shape)
    (modes : α → Fin n → SupportMode) (side : α → Side)
    (partition : α → Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat)
    (tape : Fin n → Fin 6 → K) (distinct : ∀ i, Function.Injective (tape i))
    (scratch output : K) (scratchOutput : scratch ≠ output)
    (sharedScratch : ∀ i, tape i 4 = scratch) (sharedOutput : ∀ i, tape i 5 = output)
    (labels : Label α n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) =
      instruction select shapes modes side partition tape output labels exit label)
    (base : K → List Bool)
    (sourceWords : ∀ i field, base (KeyMetadataMachine.idTape (tape i) field) =
      encodeWord (KeyMetadataMachine.fieldValue (occurrences i) (variableIDs i) field))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .dispatch), KeyMetadataMachine.clean ambient, base⟩
      (some ⟨exit, KeyMetadataMachine.clean ambient, Function.update base output
        (payload select shapes modes side partition ambient occurrences variableIDs ++ base output)⟩)
      (1 + (2 * CanonicalKeyMachine.sourceLength tape base + 4 * n + 2)) := by
  let body := CanonicalKeyMachine.keyInTime (shapes (select ambient)) (modes (select ambient))
    (side (select ambient)) (partition (select ambient)) occurrences variableIDs
    tape distinct scratch output scratchOutput sharedScratch sharedOutput
    (fun l => labels (.key (select ambient) l)) exit program
    (fun l => atLabels (.key (select ambient) l)) base sourceWords scratchEmpty ambient
  exact prefixOne (TM2.step program)
    (dispatch_step select shapes modes side partition tape output labels exit program
      (atLabels .dispatch) base ambient) body

theorem output_sources (tape : Fin n → Fin 6 → K)
    (distinct : ∀ i, Function.Injective (tape i)) (output : K)
    (sharedOutput : ∀ i, tape i 5 = output) (base : K → List Bool) (bits : List Bool)
    (i : Fin n) (field : Fin 4) :
    Function.update base output (bits ++ base output) (KeyMetadataMachine.idTape (tape i) field) =
      base (KeyMetadataMachine.idTape (tape i) field) :=
  CanonicalKeyMachine.output_sources tape distinct output sharedOutput base bits i field

theorem output_scratch (scratch output : K) (hne : scratch ≠ output)
    (base : K → List Bool) (bits : List Bool) (hempty : base scratch = []) :
    Function.update base output (bits ++ base output) scratch = [] :=
  CanonicalKeyMachine.output_scratch scratch output hne base bits hempty

theorem label_finite [Fintype α] : Finite (Label α n) := inferInstance

theorem state_finite [Finite σ] : Finite (State σ) := inferInstance

omit [DecidableEq K] in
theorem alphabet_finite (k : K) : Finite (Alphabet k) := inferInstance

end
end PerfectCompleteness.DescriptorKeyMachine

end OAI
