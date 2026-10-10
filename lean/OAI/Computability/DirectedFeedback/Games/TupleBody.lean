import Mathlib
import OAI.Computability.DirectedFeedback.Games.GeneratorModel
import OAI.Computability.DirectedFeedback.Machines.ContextClear

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceTupleBody

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature
open SourceRuntimeModel SourceTupleTape

abbrev SlotCount (u : Nat) := (slotContextEncoding u).size
abbrev QueryCount (u D : Nat) := (testTapeEncoding u D).size
abbrev Query (u D : Nat) := SourceQueryLoop.Query u D

inductive Label (u D : Nat) (Extra : Type)
  | prepare (label : SourceContextPrepare.Label u)
  | seedZero
  | clauseRank (label : MachineHorner.Label u)
  | rightBase (label : SourceBasePhase.Label)
  | clearClauseRank
  | select (index : Fin (SlotCount u + 1))
  | variableRank (index : Fin (SlotCount u)) (label : MachineHorner.Label u)
  | leftBase (index : Fin (SlotCount u)) (label : SourceBasePhase.Label)
  | query (index : Fin (SlotCount u)) (label : SourceQueryLoop.Label u D (QueryCount u D))
  | clearSlotRank (index : Fin (SlotCount u))
  | clearLeft (index : Fin (SlotCount u))
  | clearRight | clearZero
  | clearContext (label : SourceContextClear.Label u (BodyExtra Extra))
  | reset
  deriving DecidableEq, Fintype

variable {u D : Nat} {Extra : Type}

def selected (index : Fin (SlotCount u)) : SlotContext u :=
  (slotContextEncoding u).code.symm index

def main : Label u D Extra := .prepare (.inl (SourceContextLoad.labelAt 0))

def framed {K Λ Λ' σ τ S : Type} {Γ : K → Type}
    (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (q : TM2.Stmt Γ Λ σ) :
    TM2.Stmt Γ Λ' S :=
  MachineControl.statement id e (MachineStateFrame.statement labels exit q)

def framedConfiguration {K Λ Λ' σ τ S : Type} {Γ : K → Type}
    (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' S :=
  MachineControl.configuration id e (MachineStateFrame.configuration labels exit ambient c)

section Frame

variable {K Λ Λ' σ τ S : Type} {Γ : K → Type} [DecidableEq K]

theorem framed_stepAux (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (framed e labels exit q) (e (state, ambient)) tapes =
      framedConfiguration e labels exit ambient (TM2.stepAux q state tapes) := by
  rw [framed, MachineControl.stepAux_simulation, MachineStateFrame.stepAux_simulation]
  rfl

theorem framed_step (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' S)
    (atLabels : ∀ l, target (labels l) = framed e labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (framedConfiguration e labels exit ambient a) =
      some (framedConfiguration e labels exit ambient b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some l =>
    change some (TM2.stepAux (source l) state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux (target (labels l)) (e (state, ambient)) tapes) = _
    rw [atLabels, framed_stepAux]

def framedExecution (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' S)
    (atLabels : ∀ l, target (labels l) = framed e labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (framedConfiguration e labels exit ambient a)
      (some (framedConfiguration e labels exit ambient b)) budget :=
  MachineComposition.liftExecutionInTime _ _ (framedConfiguration e labels exit ambient)
    (framed_step e labels exit ambient source target atLabels) run

end Frame

variable [DecidableEq Extra]

def finish (exit : Option (Label u D Extra)) :
    TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u D Extra) (State u D) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def drainProgram (source : Arena u Extra) :
    Unit → TM2.Stmt (fun _ : Arena u Extra => Bool) Unit SourceContextPrepare.LoadState :=
  fun _ => MachineDrain.drain source () none

def drainStatement (source : Arena u Extra) (label : Label u D Extra)
    (exit : Option (Label u D Extra)) :
    TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u D Extra) (State u D) :=
  MachineStateFrame.statement (fun _ : Unit => label) exit (drainProgram source ())

def selectState (initialQuery : Query u D) (index : Fin (SlotCount u))
    (state : State u D) : State u D :=
  (state.1, (state.2.1, (state.2.2.1,
    ((({state.2.2.1 with selected := selected index}, initialQuery), none), state.2.2.2.2))))

def program (initialQuery : Query u D) (exit : Option (Label u D Extra)) :
    Label u D Extra → TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u D Extra) (State u D)
  | .prepare label => MachineSubroutine.statement .prepare (some .seedZero)
      (SourceContextPrepare.program label)
  | .seedZero => .push (workTape .zero) (fun _ => false) (.goto fun _ => .clauseRank .start)
  | .clauseRank label => framed (arithmeticStateEquiv u D) .clauseRank
      (some (.rightBase .seed)) (SourceRankPhase.program clauseRankSlots label)
  | .rightBase label => framed (arithmeticStateEquiv u D) .rightBase
      (some .clearClauseRank) (SourceBasePhase.program (baseSlots true) (2 ^ (8 ^ u)) label)
  | .clearClauseRank => drainStatement (workTape .rank) .clearClauseRank
      (some (.select ⟨0, by omega⟩))
  | .select index =>
    if h : index.val < SlotCount u then
      .load (selectState initialQuery ⟨index.val, h⟩)
        (.goto fun _ => .variableRank ⟨index.val, h⟩ .start)
    else .goto fun _ => .clearRight
  | .variableRank index label => framed (arithmeticStateEquiv u D) (.variableRank index)
      (some (.leftBase index .seed))
      (SourceRankPhase.program (variableRankSlots (selected index)) label)
  | .leftBase index label => framed (arithmeticStateEquiv u D) (.leftBase index)
      (some (.query index (.load ⟨0, by omega⟩)))
      (SourceBasePhase.program (baseSlots false) (2 ^ (2 ^ u)) label)
  | .query index label => framed (queryStateEquiv u D) (.query index)
      (some (.clearSlotRank index))
      (SourceQueryLoop.statement u D (QueryCount u D)
        (SourceLoopOrder.rankedQuery u D initialQuery) queryLayout id none label)
  | .clearSlotRank index => drainStatement (workTape .rank) (.clearSlotRank index)
      (some (.clearLeft index))
  | .clearLeft index => drainStatement (workTape .leftBase) (.clearLeft index)
      (some (.select ⟨index.val + 1, by omega⟩))
  | .clearRight => drainStatement (workTape .rightBase) .clearRight (some .clearZero)
  | .clearZero => drainStatement (workTape .zero) .clearZero
      (some (.clearContext SourceContextClear.main))
  | .clearContext label => MachineStateFrame.statement .clearContext (some .reset)
      (SourceContextClear.program label)
  | .reset => .load (fun _ => canonicalState initialQuery) (finish exit)

theorem reset_step (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (state : State u D) (tapes : Arena u Extra → List Bool) :
    TM2.step (program initialQuery exit) ⟨some .reset, state, tapes⟩ =
      some ⟨exit, canonicalState initialQuery, tapes⟩ := by
  cases exit <;> rfl

def resetInTime (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (state : State u D) (tapes : Arena u Extra → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .reset, state, tapes⟩ (some ⟨exit, canonicalState initialQuery, tapes⟩) 1 where
  steps := 1
  evals_in_steps := reset_step initialQuery exit state tapes
  steps_le_m := Nat.le_refl _

structure Ready (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) : Prop where
  formula : base .formula = formulaBits F
  current : ∀ j, base (.current j) = encodeWord (c j).val
  index : base .index = []
  work : base .work = []
  scratch : base .scratch = []
  copyScratch : base .copyScratch = []
  fields : ∀ j s, base (.field j s) = []
  variableCount : base variableHeader = encodeWord F.«variables»
  clauseCount : base clauseHeader = encodeWord F.clauses.length
  leftBlock : base (workTape .leftBlock) = encodeWord (2 ^ (2 ^ u) * F.«variables» ^ u)
  dummy : base (workTape .dummy) =
    encodeWord (F.«variables» ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u))
  rank : base (workTape .rank) = []
  rightBase : base (workTape .rightBase) = []
  leftBase : base (workTape .leftBase) = []
  zero : base (workTape .zero) = []
  accA : base (workTape .accA) = []
  accB : base (workTape .accB) = []
  counter : base (workTape .counter) = []
  arithScratch : base (workTape .arithScratch) = []
  coefficient : base (workTape .coefficient) = []
  queryTemporary : base (workTape .queryTemporary) = []
  queryScratch : base (workTape .queryScratch) = []

def contextSignature (F : Target.Formula) (c : ClauseContext F u) : Signature u :=
  ofContext F c (fun _ => .first)

def workingState (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) : State u D :=
  SourceContextPrepare.finalState F c (fun _ => .first)
    (((signature, query), none), (((), ()), none))

@[simp] theorem workingState_loader (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    (((), none), (workingState F c signature query).2) = workingState F c signature query := rfl

def arithmeticMetadata (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) : ArithmeticMetadata u D :=
  (((), none), (MachineFieldProfile.normalState
    (MachineFieldProfile.equalityProfile (SourceProfileBridge.nameWords F c)),
      (contextSignature F c, ((signature, query), none))))

def queryMetadata (F : Target.Formula) (c : ClauseContext F u) : QueryMetadata u :=
  (((), none), (MachineFieldProfile.normalState
    (MachineFieldProfile.equalityProfile (SourceProfileBridge.nameWords F c)),
      (contextSignature F c, (((), ()), none))))

@[simp] theorem arithmeticState_working (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    arithmeticStateEquiv u D ((((), ()), none), arithmeticMetadata F c signature query) =
      workingState F c signature query := rfl

@[simp] theorem queryState_working (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    queryStateEquiv u D (((signature, query), none), queryMetadata F c) =
      workingState F c signature query := rfl

@[simp] theorem select_workingState (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery query : Query u D) (signature : Signature u) :
    selectState initialQuery index (workingState F c signature query) =
      workingState F c (ofContext F c (selected index)) initialQuery := rfl

def rightValue (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  SourceAddressDescriptors.baseValue F u c (sampledVariables F c (fun _ => .first)) 1

def variableRank (F : Target.Formula) (c : ClauseContext F u) (index : Fin (SlotCount u)) : Nat :=
  ((variableEncoding F u).code (sampledVariables F c (selected index))).val

def leftValue (F : Target.Formula) (c : ClauseContext F u) (index : Fin (SlotCount u)) : Nat :=
  SourceAddressDescriptors.baseValue F u c (sampledVariables F c (selected index)) 0

noncomputable def slotBudget (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) : Nat :=
  1 + (MachineHorner.timePolynomial u).eval F.«variables» +
    (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval
      (SourceBasePhase.operandLength (variableRank F c index) 0) +
    (QueryCount u D * (9 * nBits F u + 21) + 1) +
    (variableRank F c index + 2) + (leftValue F c index + 2)

noncomputable def preparePhase (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (c j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (hfields : ∀ p : Position u, base (SourceSignaturePrepare.variableField p) = []) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some main, canonicalState initialQuery, base⟩
      (some ⟨some .seedZero,
        SourceContextPrepare.finalState F c (fun _ => .first)
          ((((canonicalSignature u, initialQuery), none), (((), ()), none))),
        SourceContextLoad.stageTapes F c base u⟩)
      ((u * (10 * (formulaBits F).length + 20) + 1) +
        (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
          (5 * (formulaBits F).length + 6) + 2)) := by
  let run := SourceContextPrepare.prepareInTime (τ := QueryState u D × ArithmeticState) F c (fun _ => .first) base hformula hcurrent
    hindex hwork hscratch hcopy hfields (fun _ _ => false) (canonicalSignature u) rfl
    ((((canonicalSignature u, initialQuery), none), (((), ()), none)))
  exact MachineSubroutine.execution .prepare (some .seedZero) SourceContextPrepare.program
    (program initialQuery exit) (fun _ => rfl) run

def seedZeroPhase (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (state : State u D) (base : Arena u Extra → List Bool) (hzero : base (workTape .zero) = []) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .seedZero, state, base⟩
      (some ⟨some (.clauseRank .start), state,
        Function.update base (workTape .zero) (encodeWord 0)⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program initialQuery exit .seedZero) state base) = _
    simp only [program, TM2.stepAux, hzero]
    rfl
  steps_le_m := Nat.le_refl _

def drainPhase (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (source : Arena u Extra) (entry : Label u D Extra) (next : Option (Label u D Extra))
    (atEntry : program initialQuery exit entry = drainStatement source entry next)
    (base : Arena u Extra → List Bool)
    (metadata : SourceSignaturePrepare.State u (QueryState u D × ArithmeticState))
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some entry, (((), register), metadata), base⟩
      (some ⟨next, (((), none), metadata), Function.update base source []⟩)
      ((base source).length + 1) := by
  let run := MachineDrain.drainInTime source () none (drainProgram source) rfl base () register
  exact MachineStateFrame.execution (fun _ : Unit => entry) next metadata (drainProgram source)
    (program initialQuery exit) (fun _ => atEntry) run

noncomputable def clauseRankPhase (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hradix : base (clauseRankSlots (.inl 0)) = encodeWord F.clauses.length)
    (hdigits : ∀ i, base (clauseRankSlots (.inr i)) = encodeWord (c i).val)
    (hclean : MachineHorner.Clean clauseRankSlots base) (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clauseRank .start), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some (.rightBase .seed), arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes clauseRankSlots base (((clauseEncoding F u).code c).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.clauses.length) := by
  let run := SourceRankPhase.clauseRankInTime F u c clauseRankSlots id none
    (SourceRankPhase.program clauseRankSlots) (fun _ => rfl) base hradix hdigits hclean () none
  exact framedExecution (arithmeticStateEquiv u D) .clauseRank (some (.rightBase .seed))
    metadata (SourceRankPhase.program clauseRankSlots) (program initialQuery exit)
    (fun _ => rfl) run

noncomputable def variableRankPhase (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hradix : base (variableRankSlots (selected index) (.inl 0)) = encodeWord F.«variables»)
    (hdigits : ∀ i, base (variableRankSlots (selected index) (.inr i)) =
      encodeWord (sampledVariables F c (selected index) i).val)
    (hclean : MachineHorner.Clean (variableRankSlots (selected index)) base)
    (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.variableRank index .start), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some (.leftBase index .seed), arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes (variableRankSlots (selected index)) base
          (((variableEncoding F u).code (sampledVariables F c (selected index))).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.«variables») := by
  let slots := variableRankSlots (u := u) (Extra := Extra) (selected index)
  let run := SourceRankPhase.variableRankInTime F u (sampledVariables F c (selected index))
    slots id none (SourceRankPhase.program slots) (fun _ => rfl) base hradix hdigits hclean () none
  exact framedExecution (arithmeticStateEquiv u D) (.variableRank index)
    (some (.leftBase index .seed)) metadata (SourceRankPhase.program slots)
    (program initialQuery exit) (fun _ => rfl) run

noncomputable def rightBasePhase (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hrank : base (baseSlots true (.inl 0)) = encodeWord (((clauseEncoding F u).code c).val))
    (hleftBlock : base (baseSlots true (.inr 1)) = encodeWord (2 ^ (2 ^ u) * F.«variables» ^ u))
    (hcoefficient : base (baseSlots true (.inr 0)) = [])
    (hclean : MachineHorner.Clean (baseSlots true) base) (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.rightBase .seed), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some .clearClauseRank, arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes (baseSlots true) base
          (SourceAddressDescriptors.baseValue F u c (sampledVariables F c (fun _ => .first)) 1)⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
        (SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
          (2 ^ (2 ^ u) * F.«variables» ^ u))) := by
  let run := SourceBasePhase.rightBaseInTime F u c (sampledVariables F c (fun _ => .first))
    (baseSlots true) id none (SourceBasePhase.program (baseSlots true) (2 ^ (8 ^ u)))
    (fun _ => rfl) base hrank hleftBlock hcoefficient hclean () none
  exact framedExecution (arithmeticStateEquiv u D) .rightBase (some .clearClauseRank) metadata
    (SourceBasePhase.program (baseSlots true) (2 ^ (8 ^ u)))
    (program initialQuery exit) (fun _ => rfl) run

noncomputable def leftBasePhase (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hrank : base (baseSlots false (.inl 0)) =
      encodeWord (((variableEncoding F u).code (sampledVariables F c (selected index))).val))
    (hzero : base (baseSlots false (.inr 1)) = encodeWord 0)
    (hcoefficient : base (baseSlots false (.inr 0)) = [])
    (hclean : MachineHorner.Clean (baseSlots false) base) (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.leftBase index .seed), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some (.query index (.load ⟨0, by omega⟩)),
        arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes (baseSlots false) base
          (SourceAddressDescriptors.baseValue F u c (sampledVariables F c (selected index)) 0)⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval
        (SourceBasePhase.operandLength
          (((variableEncoding F u).code (sampledVariables F c (selected index))).val) 0)) := by
  let run := SourceBasePhase.leftBaseInTime F u c (sampledVariables F c (selected index))
    (baseSlots false) id none (SourceBasePhase.program (baseSlots false) (2 ^ (2 ^ u)))
    (fun _ => rfl) base hrank hzero hcoefficient hclean () none
  exact framedExecution (arithmeticStateEquiv u D) (.leftBase index)
    (some (.query index (.load ⟨0, by omega⟩))) metadata
    (SourceBasePhase.program (baseSlots false) (2 ^ (2 ^ u)))
    (program initialQuery exit) (fun _ => rfl) run

theorem queryPhase (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery beforeQuery : Query u D)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool)
    (metadata : QueryMetadata u)
    (hsource : ∀ side, base (queryLayout.sources side) = encodeWord
      (SourceAddressDescriptors.baseValue F u c (sampledVariables F c (selected index)) side))
    (hscratch : base queryLayout.scratch = []) (htemporary : base queryLayout.temporary = []) :
    ∃ afterQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
        ⟨some (.query index (.load ⟨0, by omega⟩)),
          queryStateEquiv u D (((ofContext F c (selected index), beforeQuery), none), metadata), base⟩
        (some ⟨some (.clearSlotRank index),
          queryStateEquiv u D (((ofContext F c (selected index), afterQuery), none), metadata),
          SourceTestAppend.resultTapes queryLayout base
            (SourceQueryOrder.slotBits F u D c (selected index))⟩)
        (QueryCount u D * (9 * nBits F u + 21) + 1)) := by
  let localProgram := SourceQueryLoop.statement u D (QueryCount u D)
    (SourceLoopOrder.rankedQuery u D initialQuery) (queryLayout (u := u) (Extra := Extra)) id none
  obtain ⟨lastQuery, ⟨run⟩⟩ := SourceQueryOrder.sourceLoopInTime F u D c (selected index)
    initialQuery beforeQuery queryLayout id none localProgram (fun _ => rfl) base
    hsource hscratch htemporary
  refine ⟨lastQuery, ⟨?_⟩⟩
  exact framedExecution (queryStateEquiv u D) (.query index) (some (.clearSlotRank index))
    metadata localProgram (program initialQuery exit) (fun _ => rfl) run

def selectPhase (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (index : Fin (SlotCount u)) (state : State u D) (base : Arena u Extra → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.select index.castSucc), state, base⟩
      (some ⟨some (.variableRank index .start), selectState initialQuery index state, base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program initialQuery exit (.select index.castSucc)) state base) = _
    simp only [program, Fin.val_castSucc, index.isLt, ↓reduceDIte, TM2.stepAux]
  steps_le_m := Nat.le_refl _

omit [DecidableEq Extra] in
@[simp] theorem loaded_extra (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (extra : BodyExtra Extra) :
    SourceContextLoad.stageTapes F c base u (.extra extra) = base (.extra extra) :=
  SourceContextLoad.stageTapes_frame F c base u _ (by simp) (by simp) (by simp)

omit [DecidableEq Extra] in
theorem Ready.loadedClean {F : Target.Formula} {c : ClauseContext F u}
    {base : Arena u Extra → List Bool} (h : Ready F c base) :
    WorkClean (SourceContextLoad.stageTapes F c base u) where
  accA := (loaded_extra F c base _).trans h.accA
  accB := (loaded_extra F c base _).trans h.accB
  counter := (loaded_extra F c base _).trans h.counter
  scratch := (loaded_extra F c base _).trans h.arithScratch

def loopSnapshot (F : Target.Formula) (c : ClauseContext F u) (bits : List Bool) : Snapshot :=
  { rightBase := encodeWord (rightValue F c), zero := encodeWord 0, emitted := bits }

def rankSnapshot (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (bits : List Bool) : Snapshot :=
  { loopSnapshot F c bits with rank := encodeWord (variableRank F c index) }

def baseSnapshot (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (bits : List Bool) : Snapshot :=
  { rankSnapshot F c index bits with leftBase := encodeWord (leftValue F c index) }

theorem slotInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery beforeQuery : Query u D) (beforeSignature : Signature u)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool) (h : Ready F c base)
    (index : Fin (SlotCount u)) (bits : List Bool) :
    ∃ afterQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
        ⟨some (.select index.castSucc), workingState F c beforeSignature beforeQuery,
          tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c bits)⟩
        (some ⟨some (.select ⟨index.val + 1, by omega⟩),
          workingState F c (ofContext F c (selected index)) afterQuery,
          tapes (SourceContextLoad.stageTapes F c base u)
            (loopSnapshot F c (bits ++ SourceQueryOrder.slotBits F u D c (selected index)))⟩)
        (slotBudget (D := D) F c index)) := by
  let loaded := SourceContextLoad.stageTapes F c base u
  let sig := ofContext F c (selected index)
  let startTapes := tapes loaded (loopSnapshot F c bits)
  let rankedTapes := tapes loaded (rankSnapshot F c index bits)
  let basedTapes := tapes loaded (baseSnapshot F c index bits)
  have hs := selectPhase initialQuery exit index (workingState F c beforeSignature beforeQuery) startTapes
  rw [select_workingState] at hs
  have hr := variableRankPhase F c index initialQuery exit startTapes
    (by change loaded variableHeader = encodeWord F.«variables»
        exact (loaded_extra F c base _).trans h.variableCount)
    (by intro i
        exact SourceRankPhase.selectedDigits_loaded F c (selected index)
          (rankControls .variableCount) base (fun j => h.fields j _) i)
    (clean_variable loaded (loopSnapshot F c bits) (selected index) h.loadedClean)
    (arithmeticMetadata F c sig initialQuery)
  have hr' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.variableRank index .start), workingState F c sig initialQuery, startTapes⟩
      (some ⟨some (.leftBase index .seed), workingState F c sig initialQuery, rankedTapes⟩)
      ((MachineHorner.timePolynomial u).eval F.«variables») := by
    simpa only [arithmeticState_working, startTapes, rankedTapes, rankSnapshot,
      horner_variable_result, loopSnapshot, List.append_nil, variableRank] using hr
  have hb := leftBasePhase F c index initialQuery exit rankedTapes
    (by rfl) (by rfl)
    (by change loaded (workTape .coefficient) = []
        exact (loaded_extra F c base _).trans h.coefficient)
    (clean_base loaded (rankSnapshot F c index bits) false h.loadedClean)
    (arithmeticMetadata F c sig initialQuery)
  have hb' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.leftBase index .seed), workingState F c sig initialQuery, rankedTapes⟩
      (some ⟨some (.query index (.load ⟨0, by omega⟩)), workingState F c sig initialQuery, basedTapes⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval
        (SourceBasePhase.operandLength (variableRank F c index) 0)) := by
    simpa only [arithmeticState_working, rankedTapes, basedTapes, baseSnapshot,
      horner_left_result, rankSnapshot, loopSnapshot, List.append_nil, leftValue, variableRank] using hb
  obtain ⟨lastQuery, ⟨hq⟩⟩ := queryPhase F c index initialQuery initialQuery exit basedTapes
    (queryMetadata F c)
    (by intro side
        fin_cases side
        · rfl
        · rfl
        · change loaded (workTape .dummy) = _
          exact (loaded_extra F c base _).trans h.dummy)
    (by change loaded (workTape .queryScratch) = []
        exact (loaded_extra F c base _).trans h.queryScratch)
    (by change loaded (workTape .queryTemporary) = []
        exact (loaded_extra F c base _).trans h.queryTemporary)
  let emitted := bits ++ SourceQueryOrder.slotBits F u D c (selected index)
  let emittedSnapshot := {baseSnapshot F c index bits with emitted := emitted}
  let emittedTapes := tapes loaded emittedSnapshot
  have hq' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.query index (.load ⟨0, by omega⟩)), workingState F c sig initialQuery, basedTapes⟩
      (some ⟨some (.clearSlotRank index), workingState F c sig lastQuery, emittedTapes⟩)
      (QueryCount u D * (9 * nBits F u + 21) + 1) := by
    simpa only [queryState_working, basedTapes, emittedTapes, emittedSnapshot, query_result,
      baseSnapshot, rankSnapshot, loopSnapshot, emitted, sig] using hq
  let afterRank := tapes loaded {emittedSnapshot with rank := []}
  have hdRank := drainPhase initialQuery exit (workTape .rank) (.clearSlotRank index)
    (some (.clearLeft index)) rfl emittedTapes (workingState F c sig lastQuery).2 none
  have hdRank' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clearSlotRank index), workingState F c sig lastQuery, emittedTapes⟩
      (some ⟨some (.clearLeft index), workingState F c sig lastQuery, afterRank⟩)
      (variableRank F c index + 2) := by
    simpa only [workingState_loader, emittedTapes, afterRank, update_rank, tapes_rank, emittedSnapshot,
      baseSnapshot, rankSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hdRank
  have hdLeft := drainPhase initialQuery exit (workTape .leftBase) (.clearLeft index)
    (some (.select ⟨index.val + 1, by omega⟩)) rfl afterRank
    (workingState F c sig lastQuery).2 none
  have hdLeft' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clearLeft index), workingState F c sig lastQuery, afterRank⟩
      (some ⟨some (.select ⟨index.val + 1, by omega⟩), workingState F c sig lastQuery,
        tapes loaded (loopSnapshot F c emitted)⟩)
      (leftValue F c index + 2) := by
    simpa only [workingState_loader, afterRank, update_leftBase, tapes_leftBase, emittedSnapshot,
      baseSnapshot, rankSnapshot, loopSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hdLeft
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
      (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
        (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
          (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hs hr') hb') hq') hdRank') hdLeft'
  refine ⟨lastQuery, ⟨{ toEvalsTo := joined.toEvalsTo, steps_le_m := ?_ }⟩⟩
  have hj := joined.steps_le_m
  dsimp only [slotBudget]
  omega

def slotAt (u : Nat) (i : Nat) : SlotContext u :=
  if h : i < SlotCount u then selected ⟨i, h⟩ else fun _ => .first

def prefixBits (F : Target.Formula) (c : ClauseContext F u) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixBits F c r ++ SourceQueryOrder.slotBits F u D c (slotAt u r)

noncomputable def prefixBudget (F : Target.Formula) (c : ClauseContext F u) : Nat → Nat
  | 0 => 0
  | r + 1 => prefixBudget F c r + if h : r < SlotCount u then slotBudget (D := D) F c ⟨r, h⟩ else 0

theorem prefixInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery beforeQuery : Query u D) (beforeSignature : Signature u)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool) (h : Ready F c base)
    (r : Nat) (hr : r ≤ SlotCount u) :
    ∃ afterSignature : Signature u, ∃ afterQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
        ⟨some (.select ⟨0, by omega⟩), workingState F c beforeSignature beforeQuery,
          tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c [])⟩
        (some ⟨some (.select ⟨r, by omega⟩), workingState F c afterSignature afterQuery,
          tapes (SourceContextLoad.stageTapes F c base u)
            (loopSnapshot F c (prefixBits (D := D) F c r))⟩)
        (prefixBudget (D := D) F c r)) := by
  induction r with
  | zero =>
    refine ⟨beforeSignature, beforeQuery, ⟨{
      steps := 0
      evals_in_steps := rfl
      steps_le_m := Nat.le_refl _ }⟩⟩
  | succ r ih =>
    obtain ⟨previousSignature, previousQuery, ⟨previous⟩⟩ := ih (by omega)
    have hlt : r < SlotCount u := by omega
    let index : Fin (SlotCount u) := ⟨r, hlt⟩
    obtain ⟨lastQuery, ⟨one⟩⟩ := slotInTime F c initialQuery previousQuery previousSignature
      exit base h index (prefixBits (D := D) F c r)
    let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ previous one
    refine ⟨ofContext F c (selected index), lastQuery,
      ⟨{ steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }⟩⟩
    · simpa only [prefixBits, slotAt, dite_eq_left hlt, index] using joined.evals_in_steps
    · have hj := joined.steps_le_m
      simp only [prefixBudget, dite_eq_left hlt]
      dsimp only [index] at hj
      omega

theorem prefixBits_eq_ofFn (F : Target.Formula) (c : ClauseContext F u) (n : Nat) :
    prefixBits (D := D) F c n =
      (List.ofFn (fun i : Fin n => slotAt u i.val)).flatMap (SourceQueryOrder.slotBits F u D c) := by
  induction n with
  | zero => simp [prefixBits]
  | succ n ih =>
    rw [prefixBits, List.ofFn_succ', List.concat_eq_append, List.flatMap_append]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Fin.val_castSucc, Fin.val_last] using congrArg
        (fun bits => bits ++ SourceQueryOrder.slotBits F u D c (slotAt u n)) ih

theorem prefixBits_eq_tupleBits (F : Target.Formula) (c : ClauseContext F u) :
    prefixBits (D := D) F c (SlotCount u) = SourceQueryOrder.tupleBits F u D c := by
  rw [prefixBits_eq_ofFn]
  have hlist : List.ofFn (fun i : Fin (SlotCount u) => slotAt u i.val) =
      (slotContextEncoding u).enumerate := by
    apply congrArg List.ofFn
    funext i
    simp only [slotAt, i.isLt, ↓reduceDIte, selected]
  rw [hlist]
  rfl

noncomputable def setupBudget (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  ((u * (10 * (formulaBits F).length + 20) + 1) +
    (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
      (5 * (formulaBits F).length + 6) + 2)) + 1 +
    (MachineHorner.timePolynomial u).eval F.clauses.length +
    (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
      (SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
        (2 ^ (2 ^ u) * F.«variables» ^ u)) +
    (((clauseEncoding F u).code c).val + 2)

def finishBudget (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  1 + (rightValue F c + 2) + 2 + (6 * u * ((formulaBits F).length + 1) + 1) + 1

noncomputable def bodyBudget (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  setupBudget F c + prefixBudget (D := D) F c (SlotCount u) + finishBudget F c

noncomputable def setupInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool) (h : Ready F c base) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some main, canonicalState initialQuery, base⟩
      (some ⟨some (.select ⟨0, by omega⟩),
        workingState F c (canonicalSignature u) initialQuery,
        tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c [])⟩)
      (setupBudget F c) := by
  let loaded := SourceContextLoad.stageTapes F c base u
  let state := workingState F c (canonicalSignature u) initialQuery
  let s0 : Snapshot := {zero := encodeWord 0}
  let s1 : Snapshot := {s0 with rank := encodeWord (((clauseEncoding F u).code c).val)}
  let s2 : Snapshot := {s1 with rightBase := encodeWord (rightValue F c)}
  have hp := preparePhase F c initialQuery exit base h.formula h.current h.index h.work
    h.scratch h.copyScratch (fun p => h.fields p.1 _)
  have he : tapes loaded {} = loaded := empty_tapes loaded
    ((loaded_extra F c base _).trans h.rank) ((loaded_extra F c base _).trans h.rightBase)
    ((loaded_extra F c base _).trans h.leftBase) ((loaded_extra F c base _).trans h.zero)
  have hz := seedZeroPhase initialQuery exit state loaded ((loaded_extra F c base _).trans h.zero)
  have hupdate := update_zero loaded {} (encodeWord 0)
  rw [he] at hupdate
  rw [hupdate] at hz
  have hr := clauseRankPhase F c initialQuery exit (tapes loaded s0)
    (by change loaded clauseHeader = encodeWord F.clauses.length
        exact (loaded_extra F c base _).trans h.clauseCount)
    (by intro i
        change loaded (.current i) = encodeWord (c i).val
        exact (SourceContextLoad.stageTapes_frame F c base u (.current i)
          (by simp) (by simp) (by simp)).trans (h.current i))
    (clean_clause loaded s0 h.loadedClean)
    (arithmeticMetadata F c (canonicalSignature u) initialQuery)
  have hr' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clauseRank .start), state, tapes loaded s0⟩
      (some ⟨some (.rightBase .seed), state, tapes loaded s1⟩)
      ((MachineHorner.timePolynomial u).eval F.clauses.length) := by
    simpa only [arithmeticState_working, horner_clause_result, state, s1, s0, List.append_nil] using hr
  have hb := rightBasePhase F c initialQuery exit (tapes loaded s1) (by rfl)
    (by change loaded (workTape .leftBlock) = encodeWord (2 ^ (2 ^ u) * F.«variables» ^ u)
        exact (loaded_extra F c base _).trans h.leftBlock)
    (by change loaded (workTape .coefficient) = []
        exact (loaded_extra F c base _).trans h.coefficient)
    (clean_base loaded s1 true h.loadedClean)
    (arithmeticMetadata F c (canonicalSignature u) initialQuery)
  have hb' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.rightBase .seed), state, tapes loaded s1⟩
      (some ⟨some .clearClauseRank, state, tapes loaded s2⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
        (SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
          (2 ^ (2 ^ u) * F.«variables» ^ u))) := by
    simpa only [arithmeticState_working, horner_right_result, state, s2, s1, s0,
      List.append_nil, rightValue] using hb
  have hd := drainPhase initialQuery exit (workTape .rank) .clearClauseRank
    (some (.select ⟨0, by omega⟩)) rfl (tapes loaded s2) state.2 none
  have hd' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .clearClauseRank, state, tapes loaded s2⟩
      (some ⟨some (.select ⟨0, by omega⟩), state, tapes loaded (loopSnapshot F c [])⟩)
      (((clauseEncoding F u).code c).val + 2) := by
    simpa only [state, workingState_loader, update_rank, tapes_rank, s2, s1, s0,
      loopSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hd
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
      (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
        (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hp hz) hr') hb') hd'
  refine { toEvalsTo := joined.toEvalsTo, steps_le_m := ?_ }
  have hj := joined.steps_le_m
  dsimp only [setupBudget]
  omega

def finishInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery query : Query u D) (signature : Signature u)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool) (h : Ready F c base)
    (bits : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.select ⟨SlotCount u, by omega⟩), workingState F c signature query,
        tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c bits)⟩
      (some ⟨exit, canonicalState initialQuery, SourceTestAppend.resultTapes queryLayout base bits⟩)
      (finishBudget F c) := by
  let loaded := SourceContextLoad.stageTapes F c base u
  let state := workingState F c signature query
  let s0 := loopSnapshot F c bits
  let s1 : Snapshot := {s0 with rightBase := []}
  let s2 : Snapshot := {emitted := bits}
  have hd : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.select ⟨SlotCount u, by omega⟩), state, tapes loaded s0⟩
      (some ⟨some .clearRight, state, tapes loaded s0⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program initialQuery exit (.select ⟨SlotCount u, by omega⟩))
        state (tapes loaded s0)) = _
      simp only [program, Nat.lt_irrefl, ↓reduceDIte, TM2.stepAux]
    steps_le_m := Nat.le_refl _ }
  have hr := drainPhase initialQuery exit (workTape .rightBase) .clearRight (some .clearZero)
    rfl (tapes loaded s0) state.2 none
  have hr' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .clearRight, state, tapes loaded s0⟩
      (some ⟨some .clearZero, state, tapes loaded s1⟩) (rightValue F c + 2) := by
    simpa only [state, workingState_loader, update_rightBase, tapes_rightBase, s1, s0,
      loopSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hr
  have hz := drainPhase initialQuery exit (workTape .zero) .clearZero
    (some (.clearContext SourceContextClear.main)) rfl (tapes loaded s1) state.2 none
  have hz' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .clearZero, state, tapes loaded s1⟩
      (some ⟨some (.clearContext SourceContextClear.main), state, tapes loaded s2⟩) 2 := by
    simpa only [state, workingState_loader, update_zero, tapes_zero, s2, s1, s0,
      loopSnapshot, encodeWord_length, Nat.zero_add, show (1 : Nat) + 1 = 2 from rfl] using hz
  have cleanup := clearLoadedSnapshotInTime F c base s2 h.fields h.index h.work none
  have hc := MachineStateFrame.execution .clearContext (some .reset) state.2
    SourceContextClear.program (program initialQuery exit) (fun _ => rfl) cleanup
  have hc' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clearContext SourceContextClear.main), state, tapes loaded s2⟩
      (some ⟨some .reset, state, tapes base s2⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) := by
    simpa only [MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
      MachineSubroutine.configuration, MachineSubroutine.label, state, workingState_loader] using hc
  have reset := resetInTime initialQuery exit state (tapes base s2)
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
      (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
        (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hd hr') hz') hc') reset
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · have hend : tapes base s2 = SourceTestAppend.resultTapes queryLayout base bits :=
      final_tapes base bits h.rank h.rightBase h.leftBase h.zero
    simpa only [hend] using joined.evals_in_steps
  · have hj := joined.steps_le_m
    dsimp only [finishBudget]
    omega

theorem bodyInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool) (h : Ready F c base) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some main, canonicalState initialQuery, base⟩
      (some ⟨exit, canonicalState initialQuery,
        SourceTestAppend.resultTapes queryLayout base (SourceQueryOrder.tupleBits F u D c)⟩)
      (bodyBudget (D := D) F c)) := by
  have setup := setupInTime F c initialQuery exit base h
  obtain ⟨signature, lastQuery, ⟨loopRun⟩⟩ := prefixInTime F c initialQuery initialQuery
    (canonicalSignature u) exit base h (SlotCount u) (Nat.le_refl _)
  rw [prefixBits_eq_tupleBits] at loopRun
  have finishRun := finishInTime F c initialQuery lastQuery signature exit base h
    (SourceQueryOrder.tupleBits F u D c)
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ setup loopRun) finishRun
  refine ⟨{ toEvalsTo := joined.toEvalsTo, steps_le_m := ?_ }⟩
  have hj := joined.steps_le_m
  dsimp only [bodyBudget]
  omega

def machine (u D : Nat) (Extra : Type) [DecidableEq Extra] [Fintype Extra]
    (initialQuery : Query u D) : FinTM2 where
  K := Arena u Extra
  k₀ := .formula
  k₁ := workTape .accumulator
  Γ _ := Bool
  Λ := Label u D Extra
  main := main
  σ := State u D
  initialState := canonicalState initialQuery
  m := program initialQuery none

end DFVSGames.Foundations.Hastad.SourceTupleBody

end OAI
