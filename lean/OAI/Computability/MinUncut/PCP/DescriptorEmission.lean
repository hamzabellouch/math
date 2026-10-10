import Mathlib
import OAI.Computability.MinUncut.PCP.EquationEmit
import OAI.Computability.MinUncut.Machines.MachineFiniteTable

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceDescriptorEmission

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open MinUncutGames.Reduction.CloneGap
open MinUncutGames.Foundations.Complexity

def codedEquation (u D : ℕ) (state : LocalInput u D) :
    Equation (Fin (localKeyEncoding u).size) :=
  mapEquation (localKeyEncoding u).code (SourceLocalEquation.emit u D state)

def descriptorWords (u D : ℕ) (state : LocalInput u D) : List ℕ :=
  MinUncutGames.Reduction.SourceEncoding.equationWords (codedEquation u D state)

def descriptorBits (u D : ℕ) (state : LocalInput u D) : List Bool :=
  encodeWords (descriptorWords u D state)

@[simp] theorem descriptorWords_length (u D : ℕ) (state : LocalInput u D) :
    (descriptorWords u D state).length = 4 :=
  MinUncutGames.Reduction.SourceEncoding.equationWords_length _

theorem descriptorBits_length_le (u D : ℕ) (state : LocalInput u D) :
    (descriptorBits u D state).length ≤ 3 * (localKeyEncoding u).size + 2 :=
  MinUncutGames.Reduction.SourceEncoding.equationBits_length_le _

@[simp] theorem decode_descriptorBits (u D : ℕ) (state : LocalInput u D) :
    decodeWords (descriptorBits u D state) = some (descriptorWords u D state) :=
  decodeWords_encodeWords _

@[simp] theorem parse_descriptorWords (u D : ℕ) (state : LocalInput u D) :
    MinUncutGames.Reduction.SourceEncoding.parseEquation (localKeyEncoding u).size
      (descriptorWords u D state) = some (codedEquation u D state, []) := by
  simpa only [List.append_nil, descriptorWords] using
    MinUncutGames.Reduction.SourceEncoding.parseEquation_encoded (codedEquation u D state) []

theorem decode_codedEquation (u D : ℕ) (state : LocalInput u D) :
    mapEquation (localKeyEncoding u).code.symm (codedEquation u D state) =
      SourceLocalEquation.emit u D state := by
  unfold codedEquation
  rw [SourceLocalEquation.mapEquation_comp]
  have h : (localKeyEncoding u).code.symm ∘ (localKeyEncoding u).code = id := by
    funext key
    exact (localKeyEncoding u).code.symm_apply_apply key
  rw [h]
  rfl

theorem codedEquation_global (F : Formula) (u D : ℕ) (p : SourceIndex F u D) :
    mapEquation
      (addressMap F u p.1.1 (sampledVariables F p.1.1 p.1.2) ∘
        (localKeyEncoding u).code.symm)
      (codedEquation u D (ofContext F p.1.1 p.1.2, p.2)) =
      sourceEquation F u D p := by
  rw [← SourceLocalEquation.mapEquation_comp, decode_codedEquation]
  exact (sourceEquation_eq_map_emit F u D p).symm

def descriptorPushBound (u D : ℕ) : ℕ :=
  ((localInputs u D).map (fun state => (descriptorBits u D state).length)).sum

theorem descriptorPushBound_le (u D : ℕ) :
    descriptorPushBound u D ≤
      (localInputs u D).length * (3 * (localKeyEncoding u).size + 2) := by
  have hlist (states : List (LocalInput u D)) :
      (states.map (fun state => (descriptorBits u D state).length)).sum ≤
        states.length * (3 * (localKeyEncoding u).size + 2) := by
    induction states with
    | nil => simp
    | cons state states ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      have hstate := descriptorBits_length_le u D state
      omega
  exact hlist (localInputs u D)

variable {K Λ : Type} [DecidableEq K]

instance localInputDecidableEq (u D : ℕ) : DecidableEq (LocalInput u D) :=
  fun x y =>
    if h : (localInputEncoding u D).code x = (localInputEncoding u D).code y then
      isTrue ((localInputEncoding u D).code.injective h)
    else isFalse (fun hxy => h (congrArg (localInputEncoding u D).code hxy))

def emitDescriptor (u D : ℕ) (dst : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (LocalInput u D)) :
    TM2.Stmt (fun _ : K => Bool) Λ (LocalInput u D) :=
  MachineFiniteTable.emit (Γ := fun _ : K => Bool) dst
    (descriptorBits u D) (localInputs u D) next

theorem stepAux_emitDescriptor (u D : ℕ) (dst : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (LocalInput u D))
    (state : LocalInput u D) (tapes : K → List Bool) :
    TM2.stepAux (emitDescriptor u D dst next) state tapes =
      TM2.stepAux next state
        (Function.update tapes dst (descriptorBits u D state ++ tapes dst)) :=
  MachineFiniteTable.stepAux_emit (Γ := fun _ : K => Bool) dst
    (descriptorBits u D) (localInputs u D)
    (mem_localInputs u D) next state tapes

omit [DecidableEq K] in
theorem emitDescriptor_push_bound (u D : ℕ) (dst : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (LocalInput u D)) :
    Runtime.statementPushBound (emitDescriptor u D dst next) ≤
      descriptorPushBound u D + Runtime.statementPushBound next :=
  MachineFiniteTable.emit_push_bound (Γ := fun _ : K => Bool) dst
    (descriptorBits u D) (localInputs u D) next

def emitDescriptorInTime (u D : ℕ) (dst : K)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (LocalInput u D))
    (label exitLabel : Λ)
    (atLabel : program label = emitDescriptor u D dst (.goto (fun _ => exitLabel)))
    (state : LocalInput u D) (tapes : K → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, state, tapes⟩
      (some ⟨some exitLabel, state,
        Function.update tapes dst (descriptorBits u D state ++ tapes dst)⟩) 1 :=
  MachineFiniteTable.emitInTime (Γ := fun _ : K => Bool) dst
    (descriptorBits u D) (localInputs u D)
    (mem_localInputs u D) program label exitLabel atLabel state tapes

theorem descriptor_output_frame (u D : ℕ) (dst : K)
    (state : LocalInput u D) (tapes : K → List Bool) (k : K) (h : k ≠ dst) :
    (Function.update tapes dst (descriptorBits u D state ++ tapes dst)) k = tapes k :=
  MachineFiniteTable.output_frame (Γ := fun _ : K => Bool) dst
    (descriptorBits u D) state tapes k h

end MinUncutGames.Foundations.Hastad.SourceDescriptorEmission

namespace MinUncutGames.Foundations.Hastad.SourceTestEmit

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit
open MinUncutGames.Reduction.CloneGap
open Complexity

abbrev Label (u D : ℕ) := Unit ⊕ (LocalInput u D × SourceEquationEmit.Label)
abbrev State (u D : ℕ) := LocalInput u D × Option Bool

def localEquation (u D : ℕ) (state : LocalInput u D) : Equation Descriptor :=
  mapEquation (descriptor u) (SourceLocalEquation.emit u D state)

def bodyLabel (u D : ℕ) (state : LocalInput u D) (label : SourceEquationEmit.Label) :
    Label u D := .inr (state, label)

variable {K : Type} [DecidableEq K]

def program (u D : ℕ) (sources : Fin 3 → K) (destination scratch : K)
    (exit : Option (Label u D)) :
    Label u D → TM2.Stmt (fun _ : K => Bool) (Label u D) (State u D)
  | .inl _ => .goto (fun state => bodyLabel u D state.1 .seed)
  | .inr (state, label) =>
      SourceEquationEmit.statement sources destination scratch (localEquation u D state)
        (bodyLabel u D state) exit label

theorem testTrace (u D : ℕ) (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (exit : Option (Label u D))
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → ℕ)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program u D sources destination scratch exit)))^[
      SourceEquationEmit.steps values (localEquation u D state) + 1]
        (some ⟨some (.inl ()), (state, register), base⟩) =
      some ⟨exit, (state, none),
        prefixTapes destination base (words values (localEquation u D state))⟩ := by
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program u D sources destination scratch exit)))^[
    SourceEquationEmit.steps values (localEquation u D state)]
      (some ⟨some (bodyLabel u D state .seed), (state, register), base⟩) = _
  exact SourceEquationEmit.equationTrace sources destination scratch sourceDestination
    sourceScratch destinationScratch (localEquation u D state) (bodyLabel u D state) exit
    (program u D sources destination scratch exit) (fun _ => rfl)
    base values sourceWords scratchEmpty state register

def testInTime (u D : ℕ) (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (exit : Option (Label u D))
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → ℕ)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program u D sources destination scratch exit))
      ⟨some (.inl ()), (state, register), base⟩
      (some ⟨exit, (state, none),
        prefixTapes destination base (words values (localEquation u D state))⟩)
      (SourceEquationEmit.steps values (localEquation u D state) + 1) where
  steps := SourceEquationEmit.steps values (localEquation u D state) + 1
  evals_in_steps := testTrace u D sources destination scratch sourceDestination sourceScratch
    destinationScratch exit state base values sourceWords scratchEmpty register
  steps_le_m := Nat.le_refl _

def sourceTestInTime (F : Formula) (u D : ℕ) (p : SourceIndex F u D)
    (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (exit : Option (Label u D))
    (base : K → List Bool)
    (sourceWords : ∀ side, base (sources side) = encodeWord
      (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2) side))
    (scratchEmpty : base scratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program u D sources destination scratch exit))
      ⟨some (.inl ()), ((ofContext F p.1.1 p.1.2, p.2), register), base⟩
      (some ⟨exit, ((ofContext F p.1.1 p.1.2, p.2), none),
        prefixTapes destination base
          (MinUncutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D p))⟩)
      (6 * nBits F u + 17) where
  steps := SourceEquationEmit.steps
    (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2))
    (localEquation u D (ofContext F p.1.1 p.1.2, p.2)) + 1
  evals_in_steps := by
    rw [sourceEquation_words]
    exact testTrace u D sources destination scratch sourceDestination sourceScratch
      destinationScratch exit (ofContext F p.1.1 p.1.2, p.2) base
      (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2)) sourceWords scratchEmpty register
  steps_le_m := by
    have h := equation_emit_steps_le F u p.1.1 (sampledVariables F p.1.1 p.1.2)
      (localEquation u D (ofContext F p.1.1 p.1.2, p.2))
    change _ + 1 ≤ _
    unfold SourceEquationEmit.steps
    omega

end MinUncutGames.Foundations.Hastad.SourceTestEmit

namespace MinUncutGames.Foundations.Hastad.SourceTestAppend

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit SourceTestEmit

inductive Label (u D : Nat)
  | test (label : SourceTestEmit.Label u D)
  | append
  deriving DecidableEq, Fintype

abbrev State (u D : Nat) := SourceTestEmit.State u D

structure Layout (K : Type) where
  sources : Fin 3 → K
  temporary : K
  scratch : K
  accumulator : K
  sourceTemporary : ∀ side, sources side ≠ temporary
  sourceScratch : ∀ side, sources side ≠ scratch
  sourceAccumulator : ∀ side, sources side ≠ accumulator
  temporaryScratch : temporary ≠ scratch
  temporaryAccumulator : temporary ≠ accumulator
  scratchAccumulator : scratch ≠ accumulator

def equationBits (u D : Nat) (values : Fin 3 → Nat) (state : LocalInput u D) : List Bool :=
  encodeWords (words values (localEquation u D state))

def steps (u D : Nat) (values : Fin 3 → Nat) (state : LocalInput u D) : Nat :=
  SourceEquationEmit.steps values (localEquation u D state) + 1 +
    (equationBits u D values state).length + 1

variable {K Λ : Type} [DecidableEq K]

def bodyLabel (u D : Nat) (labels : Label u D → Λ) (state : LocalInput u D)
    (label : SourceEquationEmit.Label) : Λ :=
  labels (.test (SourceTestEmit.bodyLabel u D state label))

def statement (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ) :
    Label u D → TM2.Stmt (fun _ : K => Bool) Λ (State u D)
  | .test (.inl _) => .goto (fun state => bodyLabel u D labels state.1 .seed)
  | .test (.inr (state, label)) =>
      SourceEquationEmit.statement layout.sources layout.temporary layout.scratch
        (localEquation u D state) (bodyLabel u D labels state) (some (labels .append)) label
  | .append => Reduction.MachineTransfer.loopAt layout.temporary layout.accumulator id false
      (labels .append) exit

def program (u D : Nat) (layout : Layout K) (exit : Option (Label u D)) :
    Label u D → TM2.Stmt (fun _ : K => Bool) (Label u D) (State u D) :=
  statement u D layout id exit

def resultTapes (layout : Layout K) (base : K → List Bool) (bits : List Bool) : K → List Bool :=
  Function.update base layout.accumulator (bits.reverse ++ base layout.accumulator)

theorem resultTapes_other (layout : Layout K) (base : K → List Bool) (bits : List Bool)
    (k : K) (hk : k ≠ layout.accumulator) : resultTapes layout base bits k = base k := by
  simp [resultTapes, hk]

theorem resultTapes_source (layout : Layout K) (base : K → List Bool) (bits : List Bool)
    (side : Fin 3) : resultTapes layout base bits (layout.sources side) = base (layout.sources side) :=
  resultTapes_other layout base bits _ (layout.sourceAccumulator side)

theorem resultTapes_temporary (layout : Layout K) (base : K → List Bool) (bits : List Bool) :
    resultTapes layout base bits layout.temporary = base layout.temporary :=
  resultTapes_other layout base bits _ layout.temporaryAccumulator

theorem resultTapes_scratch (layout : Layout K) (base : K → List Bool) (bits : List Bool) :
    resultTapes layout base bits layout.scratch = base layout.scratch :=
  resultTapes_other layout base bits _ layout.scratchAccumulator

theorem emitTrace (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[
      SourceEquationEmit.steps values (localEquation u D state) + 1]
      (some ⟨some (labels (.test (.inl ()))), (state, register), base⟩) =
      some ⟨some (labels .append), (state, none),
        prefixTapes layout.temporary base (words values (localEquation u D state))⟩ := by
  have select : TM2.step p
      ⟨some (labels (.test (.inl ()))), (state, register), base⟩ =
      some ⟨some (bodyLabel u D labels state .seed), (state, register), base⟩ := by
    change some (TM2.stepAux (p (labels (.test (.inl ())))) (state, register) base) = _
    rw [atLabels]
    rfl
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[
    SourceEquationEmit.steps values (localEquation u D state)]
      (TM2.step p ⟨some (labels (.test (.inl ()))), (state, register), base⟩) = _
  rw [select]
  exact SourceEquationEmit.equationTrace layout.sources layout.temporary layout.scratch
    layout.sourceTemporary layout.sourceScratch layout.temporaryScratch (localEquation u D state)
    (bodyLabel u D labels state) (some (labels .append)) p
    (fun label => atLabels (.test (SourceTestEmit.bodyLabel u D state label)))
    base values sourceWords scratchEmpty state register

theorem appendTrace (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps u D values state]
      (some ⟨some (labels (.test (.inl ()))), (state, register), base⟩) =
      some ⟨exit, (state, none), resultTapes layout base (equationBits u D values state)⟩ := by
  let emitted := prefixTapes layout.temporary base (words values (localEquation u D state))
  have hemit := emitTrace u D layout labels exit p atLabels state base values sourceWords
    scratchEmpty register
  have htemp : emitted layout.temporary = equationBits u D values state := by
    simp [emitted, prefixTapes, equationBits, temporaryEmpty]
  have hacc : emitted layout.accumulator = base layout.accumulator :=
    prefixTapes_other _ _ _ _ (Ne.symm layout.temporaryAccumulator)
  have hfinal : Reduction.MachineTransfer.tapesAt layout.temporary layout.accumulator emitted []
      ((equationBits u D values state).reverse ++ base layout.accumulator) =
      resultTapes layout base (equationBits u D values state) := by
    funext k
    by_cases hka : k = layout.accumulator
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, resultTapes]
    · by_cases hkt : k = layout.temporary
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, resultTapes, layout.temporaryAccumulator,
          temporaryEmpty]
      · simp [Reduction.MachineTransfer.tapesAt, resultTapes, emitted, prefixTapes, hka, hkt]
  have transferred := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := LocalInput u D)
    layout.temporary layout.accumulator layout.temporaryAccumulator id false (labels .append)
    exit p (by simpa only [statement] using atLabels .append) emitted state none
  change (MachineComposition.advance (TM2.step p))^[(emitted layout.temporary).length + 1]
    (some ⟨some (labels .append), (state, none), emitted⟩) = _ at transferred
  rw [htemp, hacc] at transferred
  simp only [List.map_id] at transferred
  rw [hfinal] at transferred
  rw [show steps u D values state = ((equationBits u D values state).length + 1) +
      (SourceEquationEmit.steps values (localEquation u D state) + 1) by unfold steps; omega,
    Function.iterate_add_apply, hemit]
  exact transferred

def appendInTime (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.test (.inl ()))), (state, register), base⟩
      (some ⟨exit, (state, none), resultTapes layout base (equationBits u D values state)⟩)
      (steps u D values state) where
  steps := steps u D values state
  evals_in_steps := appendTrace u D layout labels exit p atLabels state base values
    sourceWords scratchEmpty temporaryEmpty register
  steps_le_m := Nat.le_refl _

def programInTime (u D : Nat) (layout : Layout K) (exit : Option (Label u D))
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program u D layout exit))
      ⟨some (.test (.inl ())), (state, register), base⟩
      (some ⟨exit, (state, none), resultTapes layout base (equationBits u D values state)⟩)
      (steps u D values state) :=
  appendInTime u D layout id exit (program u D layout exit) (fun _ => rfl) state base values
    sourceWords scratchEmpty temporaryEmpty register

def sourceAppendInTime (F : Formula) (u D : Nat) (occurrence : SourceIndex F u D)
    (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (base : K → List Bool)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord
      (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2) side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.test (.inl ()))),
        ((ofContext F occurrence.1.1 occurrence.1.2, occurrence.2), register), base⟩
      (some ⟨exit, ((ofContext F occurrence.1.1 occurrence.1.2, occurrence.2), none),
        resultTapes layout base (encodeWords
          (MinUncutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D occurrence)))⟩)
      (9 * nBits F u + 20) where
  steps := steps u D
    (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2))
    (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2)
  evals_in_steps := by
    rw [sourceEquation_words]
    exact appendTrace u D layout labels exit p atLabels
      (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2) base
      (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2))
      sourceWords scratchEmpty temporaryEmpty register
  steps_le_m := by
    have he := equation_emit_steps_le F u occurrence.1.1
      (sampledVariables F occurrence.1.1 occurrence.1.2)
      (localEquation u D (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2))
    have hl := MinUncutGames.Reduction.SourceEncoding.equationBits_length_le
      (sourceEquation F u D occurrence)
    rw [sourceEquation_words] at hl
    unfold steps SourceEquationEmit.steps equationBits
    dsimp only [localEquation] at he hl ⊢
    omega

abbrev Tape := Fin 3 ⊕ Fin 3

def standardLayout : Layout Tape where
  sources := Sum.inl
  temporary := .inr 0
  scratch := .inr 1
  accumulator := .inr 2
  sourceTemporary _ := Sum.inl_ne_inr
  sourceScratch _ := Sum.inl_ne_inr
  sourceAccumulator _ := Sum.inl_ne_inr
  temporaryScratch := by decide
  temporaryAccumulator := by decide
  scratchAccumulator := by decide

def machine (u D : Nat) (initial : LocalInput u D) : FinTM2 where
  K := Tape
  k₀ := .inl 0
  k₁ := .inr 2
  Γ _ := Bool
  Λ := Label u D
  main := .test (.inl ())
  σ := State u D
  initialState := (initial, none)
  m := program u D standardLayout none

def machineInTime (u D : Nat) (initial state : LocalInput u D)
    (base : Tape → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (.inl side) = encodeWord (values side))
    (scratchEmpty : base (.inr 1) = []) (temporaryEmpty : base (.inr 0) = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (machine u D initial).step
      ⟨some (Label.test (.inl ())), (state, register), base⟩
      (some ⟨none, (state, none), resultTapes standardLayout base (equationBits u D values state)⟩)
      (steps u D values state) :=
  programInTime u D standardLayout none state base values sourceWords scratchEmpty temporaryEmpty register

end MinUncutGames.Foundations.Hastad.SourceTestAppend

namespace MinUncutGames.Foundations.Hastad.SourceQueryLoop

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceLocalEquation

abbrev Query (u D : Nat) := SourceTape.TestTape (I u) (J u) D
abbrev State (u D : Nat) := SourceTestAppend.State u D

inductive Label (u D n : Nat)
  | load (index : Fin (n + 1))
  | emit (index : Fin n) (label : SourceTestAppend.Label u D)
  deriving DecidableEq, Fintype

variable {K Λ : Type} [DecidableEq K]

def finish (u D : Nat) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State u D) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def statement (u D n : Nat) (queries : Nat → Query u D)
    (layout : SourceTestAppend.Layout K) (labels : Label u D n → Λ) (exit : Option Λ) :
    Label u D n → TM2.Stmt (fun _ : K => Bool) Λ (State u D)
  | .load index =>
    if h : index.val < n then
      .load (fun state => ((state.1.1, queries index.val), none))
        (.goto fun _ => labels (.emit ⟨index.val, h⟩ (.test (.inl ()))))
    else finish u D exit
  | .emit index label =>
    SourceTestAppend.statement u D layout (fun l => labels (.emit index l))
      (some (labels (.load ⟨index.val + 1, by omega⟩))) label

def prefixBits (u D : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u) : Nat → List Bool
  | 0 => []
  | n + 1 => prefixBits u D queries values signature n ++
      SourceTestAppend.equationBits u D values (signature, queries n)

def prefixSteps (u D : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSteps u D queries values signature n +
      (SourceTestAppend.steps u D values (signature, queries n) + 1)

theorem resultTapes_append (layout : SourceTestAppend.Layout K) (base : K → List Bool)
    (first second : List Bool) :
    SourceTestAppend.resultTapes layout
      (SourceTestAppend.resultTapes layout base first) second =
      SourceTestAppend.resultTapes layout base (first ++ second) := by
  funext k
  by_cases hk : k = layout.accumulator
  · subst k
    simp [SourceTestAppend.resultTapes, List.reverse_append, List.append_assoc]
  · simp [SourceTestAppend.resultTapes, hk]

theorem prefixTrace (u D n : Nat) (queries : Nat → Query u D)
    (layout : SourceTestAppend.Layout K) (labels : Label u D n → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ l, p (labels l) = statement u D n queries layout labels exit l)
    (signature : Signature u) (initialQuery : Query u D)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (r : Nat) (hr : r ≤ n) :
    ∃ lastQuery : Query u D,
      (MachineComposition.advance (TM2.step p))^[prefixSteps u D queries values signature r]
        (some ⟨some (labels (.load ⟨0, by omega⟩)), ((signature, initialQuery), none), base⟩) =
        some ⟨some (labels (.load ⟨r, by omega⟩)), ((signature, lastQuery), none),
          SourceTestAppend.resultTapes layout base (prefixBits u D queries values signature r)⟩ := by
  induction r with
  | zero =>
    refine ⟨initialQuery, ?_⟩
    simp [prefixSteps, prefixBits, SourceTestAppend.resultTapes]
  | succ r ih =>
    obtain ⟨lastQuery, hprevious⟩ := ih (by omega)
    have hlt : r < n := by omega
    let current := SourceTestAppend.resultTapes layout base
      (prefixBits u D queries values signature r)
    have hselect : TM2.step p
        ⟨some (labels (.load ⟨r, by omega⟩)), ((signature, lastQuery), none), current⟩ =
        some ⟨some (labels (.emit ⟨r, hlt⟩ (.test (.inl ())))),
          ((signature, queries r), none), current⟩ := by
      change some (TM2.stepAux (p (labels (.load ⟨r, by omega⟩))) _ _) = _
      rw [atLabels]
      simp only [statement, hlt, ↓reduceDIte, TM2.stepAux]
    have hbody := SourceTestAppend.appendTrace u D layout
      (fun l => labels (.emit ⟨r, hlt⟩ l))
      (some (labels (.load ⟨r + 1, by omega⟩))) p
      (fun l => atLabels (.emit ⟨r, hlt⟩ l)) (signature, queries r) current values
      (fun side => (SourceTestAppend.resultTapes_source layout base _ side).trans
        (sourceWords side))
      ((SourceTestAppend.resultTapes_scratch layout base _).trans scratchEmpty)
      ((SourceTestAppend.resultTapes_temporary layout base _).trans temporaryEmpty) none
    refine ⟨queries r, ?_⟩
    rw [show prefixSteps u D queries values signature (r + 1) =
      (SourceTestAppend.steps u D values (signature, queries r) + 1) +
        prefixSteps u D queries values signature r by rw [prefixSteps]; omega,
      Function.iterate_add_apply, hprevious, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step p))^[
      SourceTestAppend.steps u D values (signature, queries r)]
      (TM2.step p ⟨some (labels (.load ⟨r, by omega⟩)),
        ((signature, lastQuery), none), current⟩) = _
    rw [hselect, hbody]
    rw [show current = SourceTestAppend.resultTapes layout base
      (prefixBits u D queries values signature r) from rfl, resultTapes_append]
    rfl

theorem prefixSteps_le (u D n B : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u)
    (hbound : ∀ i, i < n → SourceTestAppend.steps u D values (signature, queries i) ≤ B) :
    prefixSteps u D queries values signature n ≤ n * (B + 1) := by
  induction n with
  | zero => simp [prefixSteps]
  | succ n ih =>
    have hp := ih (fun i hi => hbound i (by omega))
    have hb := hbound n (by omega)
    rw [prefixSteps, Nat.succ_mul]
    omega

theorem loopInTime (u D n B : Nat) (queries : Nat → Query u D)
    (layout : SourceTestAppend.Layout K) (labels : Label u D n → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ l, p (labels l) = statement u D n queries layout labels exit l)
    (signature : Signature u) (initialQuery : Query u D)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (hbound : ∀ i, i < n → SourceTestAppend.steps u D values (signature, queries i) ≤ B) :
    ∃ lastQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step p)
        ⟨some (labels (.load ⟨0, by omega⟩)), ((signature, initialQuery), none), base⟩
        (some ⟨exit, ((signature, lastQuery), none),
          SourceTestAppend.resultTapes layout base (prefixBits u D queries values signature n)⟩)
        (n * (B + 1) + 1)) := by
  obtain ⟨lastQuery, hprefix⟩ := prefixTrace u D n queries layout labels exit p atLabels
    signature initialQuery base values sourceWords scratchEmpty temporaryEmpty n (Nat.le_refl n)
  refine ⟨lastQuery, ⟨{
    steps := prefixSteps u D queries values signature n + 1
    evals_in_steps := ?_
    steps_le_m := ?_ }⟩⟩
  · change (MachineComposition.advance (TM2.step p))^[
      prefixSteps u D queries values signature n + 1] _ = _
    rw [Function.iterate_succ_apply', hprefix]
    rw [MachineComposition.advance_some]
    change some (TM2.stepAux (p (labels (.load ⟨n, by omega⟩))) _ _) = _
    rw [atLabels]
    simp only [statement, Nat.lt_irrefl, ↓reduceDIte]
    cases exit <;> rfl
  · exact Nat.add_le_add_right (prefixSteps_le u D n B queries values signature hbound) 1

end MinUncutGames.Foundations.Hastad.SourceQueryLoop

end OAI
