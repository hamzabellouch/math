import Mathlib
import OAI.Analysis.MatrixSigning.Realization.ScalarRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

variable {α β : Type*} {ea : α → Word} {eb : β → Word} {P : α → Prop} [DecidablePred P]

def Realizes.dite {f : {a // P a} → β} {g : {a // ¬P a} → β}
    (test : Realizes ea boolCode (fun a => decide (P a)))
    (r : Realizes (fun a : {a // P a} => ea a.val) eb f)
    (s : Realizes (fun a : {a // ¬P a} => ea a.val) eb g) :
    Realizes ea eb (fun a => if h : P a then f ⟨a,h⟩ else g ⟨a,h⟩) :=
  let n := r.routine.scratch+s.routine.scratch
  let r' := r.routine.pad n (Nat.le_add_right _ _)
  let s' := s.routine.pad n (Nat.le_add_left _ _)
  let encoded (a : α) : Word := prodCode boolCode ea (decide (P a),a)
  let prep : Realizes ea encoded id :=
    (test.both (identity ea)).changeOutput encoded id (fun _ => rfl)
  let branch : Realizes encoded eb (fun a => if h : P a then f ⟨a,h⟩ else g ⟨a,h⟩) := {
    cost := fun a => 5+(if h : P a then r.cost ⟨a,h⟩ else s.cost ⟨a,h⟩)+1
    routine := {
      scratch := n+2
      program := ConditionalRoutine.program n r'.program s'.program
      spec := fun a => by
        by_cases hp : P a
        · have h := (ConditionalRoutine.parse_spec n (ea a) true).compose
            (ConditionalRoutine.choose_true n _ (liftPorts s'.program (ConditionalRoutine.ports n)) _ _ _
              (ConditionalRoutine.core_spec n _ _ _ _ (r'.spec ⟨a,hp⟩)))
          simp only [encoded,prodCode,boolCode,hp,decide_true,dite_eq_left,Nat.add_assoc] at h ⊢
          exact h
        · have h := (ConditionalRoutine.parse_spec n (ea a) false).compose
            (ConditionalRoutine.choose_false n (liftPorts r'.program (ConditionalRoutine.ports n)) _ _ _ _
              (ConditionalRoutine.core_spec n _ _ _ _ (s'.spec ⟨a,hp⟩)))
          simp only [encoded,prodCode,boolCode,hp,decide_false,Nat.add_assoc] at h ⊢
          exact h } }
  prep.then branch

end CurrentKS.Realization

end OAI
