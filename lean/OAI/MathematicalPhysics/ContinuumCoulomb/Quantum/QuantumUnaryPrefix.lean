import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBitTransfer
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCircuitCode

namespace OAI

/-! Preserve the unary size bound while calling the given verifier generator.
The extra tapes hold only Boolean words; the original machine is embedded
without changing any of its instructions. -/

noncomputable section
namespace ContinuumCoulomb.QuantumUnaryPrefix
open Turing ExactQuantumFactoring.BitStackProgram
open MinUncutGames.Foundations.Complexity

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

abbrev Tape (h : TM2ComputableInPolyTime ea eb f) := h.tm.K ⊕ Fin 3
abbrev Alphabet (h : TM2ComputableInPolyTime ea eb f) : Tape h → Type :=
  MachineEmbedding.Alphabet h.tm.Γ (fun _ : Fin 3 => Bool)
abbrev Label (h : TM2ComputableInPolyTime ea eb f) := h.tm.Λ ⊕ Fin 7
abbrev State (h : TM2ComputableInPolyTime ea eb f) := h.tm.σ × Option Bool

def program (h : TM2ComputableInPolyTime ea eb f) :
    Label h → TM2.Stmt (Alphabet h) (Label h) (State h)
  | .inl l => MachineEmbedding.statement (some (.inr 3)) (h.tm.m l)
  | .inr i =>
    if i=0 then
      .pop (.inr 0) (fun s b => (s.1,b))
        (.branch (fun s => s.2.getD false)
          (.pop (.inr 0) (fun s _ => s)
            (.push (.inr 1) (fun _ => true) (.goto fun _ => .inr 0)))
          (.load (fun s => (s.1,none)) (.goto fun _ => .inr 1)))
    else if i=1 then
      QuantumBitTransfer.loop (.inr 0) (.inr 2) id id (.inr 1) (some (.inr 2))
    else if i=2 then
      QuantumBitTransfer.loop (.inr 2) (.inl h.tm.k₀) id h.inputAlphabet.invFun
        (.inr 2) (some (.inl h.tm.main))
    else if i=3 then
      QuantumBitTransfer.loop (.inl h.tm.k₁) (.inr 2) h.outputAlphabet id
        (.inr 3) (some (.inr 4))
    else if i=4 then
      QuantumBitTransfer.loop (.inr 2) (.inr 0) id id (.inr 4) (some (.inr 5))
    else if i=5 then
      .push (.inr 0) (fun _ => false)
        (.load (fun s => (s.1,none)) (.goto fun _ => .inr 6))
    else
      .pop (.inr 1) (fun s b => (s.1,b))
        (.branch (fun s => s.2.isSome)
          (.push (.inr 0) (fun _ => true)
            (.push (.inr 0) (fun _ => true) (.goto fun _ => .inr 6)))
          (.load (fun _ => (h.tm.initialState,none)) .halt))

def machine (h : TM2ComputableInPolyTime ea eb f) : FinTM2 where
  K := Tape h
  kFin := by letI := h.tm.kFin; exact inferInstance
  k₀ := .inr 0
  k₁ := .inr 0
  Γ := Alphabet h
  Λ := Label h
  ΛFin := by letI := h.tm.ΛFin; exact inferInstance
  main := .inr 0
  σ := State h
  σFin := by letI := h.tm.σFin; exact inferInstance
  initialState := (h.tm.initialState,none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program h

def extraTapes (input saved temp : List Bool) : Fin 3 → List Bool :=
  fun i => if i=0 then input else if i=1 then saved else temp

def tapes (h : TM2ComputableInPolyTime ea eb f) (source : ∀ k, List (h.tm.Γ k))
    (input saved temp : List Bool) : ∀ k, List (Alphabet h k) :=
  MachineEmbedding.tapes source (extraTapes input saved temp)

def configuration (h : TM2ComputableInPolyTime ea eb f) (label : Option (Label h))
    (state : h.tm.σ) (r : Option Bool) (source : ∀ k, List (h.tm.Γ k))
    (input saved temp : List Bool) : (machine h).Cfg :=
  ⟨label,(state,r),tapes h source input saved temp⟩

def next (h : TM2ComputableInPolyTime ea eb f) (c : Option (machine h).Cfg) :=
  c.bind (machine h).step

theorem embedded_program (h : TM2ComputableInPolyTime ea eb f) :
    program h = MachineEmbedding.program (some (.inr 3)) h.tm.m
      (fun i => program h (.inr i)) := by
  funext l
  cases l <;> rfl

def source_execution (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (x : α) :
    StateTransition.EvalsToInTime (machine h).step
      (MachineEmbedding.configuration (some (.inr 3)) (none : Option Bool)
        (extraTapes [] (unaryCode b) [])
        (initList h.tm ((ea x).map h.inputAlphabet.invFun)))
      (some (MachineEmbedding.configuration (some (.inr 3)) (none : Option Bool)
        (extraTapes [] (unaryCode b) [])
        (haltList h.tm ((eb (f x)).map h.outputAlphabet.invFun))))
      (h.time.eval (ea x).length) := by
  have hh := MachineComposition.embeddedExecution (some (Sum.inr (3 : Fin 7)))
    (none : Option Bool) (extraTapes [] (unaryCode b) []) h.tm.m
    (fun i => program h (.inr i)) (h.outputsFun x)
  rw [← embedded_program h] at hh
  exact hh

end ContinuumCoulomb.QuantumUnaryPrefix

end

end OAI
