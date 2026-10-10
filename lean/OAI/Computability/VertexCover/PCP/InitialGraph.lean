import Mathlib
import OAI.Computability.VertexCover.PCP.ConstraintGraph
import OAI.Computability.VertexCover.PCP.NameCompaction

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.InitialGraph

open Target

abbrev Label := Bool × Bool × Bool
abbrev Vertex (F : Formula) := (Fin F.«variables» ⊕ Fin F.clauses.length) ⊕ Unit
abbrev Dart (F : Formula) := (RandomEvent F × Bool) ⊕ Unit

instance slotFintype : Fintype Slot where
  elems := {Slot.first, Slot.second, Slot.third}
  complete := by intro s; cases s <;> simp

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide
@[simp] theorem card_label : Fintype.card Label = 8 := by
  simp [Label, Fintype.card_prod]

def variableVertex (F : Formula) (v : Fin F.«variables») : Vertex F := .inl (.inl v)
def clauseVertex (F : Formula) (i : Fin F.clauses.length) : Vertex F := .inl (.inr i)
def dummyVertex (F : Formula) : Vertex F := .inr ()
def dummyDart (F : Formula) : Dart F := .inr ()

instance vertexNonempty (F : Formula) : Nonempty (Vertex F) := ⟨dummyVertex F⟩
instance dartNonempty (F : Formula) : Nonempty (Dart F) := ⟨dummyDart F⟩

def reverse (F : Formula) : Dart F → Dart F
  | .inl (event, orientation) => .inl (event, !orientation)
  | .inr _ => .inr ()

theorem reverse_involutive (F : Formula) : Function.Involutive (reverse F) := by
  intro d
  cases d with
  | inl pair => rcases pair with ⟨e, b⟩; cases b <;> rfl
  | inr u => cases u; rfl

def reverseEquiv (F : Formula) : Dart F ≃ Dart F where
  toFun := reverse F
  invFun := reverse F
  left_inv := reverse_involutive F
  right_inv := reverse_involutive F

def tail (F : Formula) : Dart F → Vertex F
  | .inl (event, false) => clauseVertex F event.1
  | .inl (event, true) => variableVertex F (nameAt (clauseAt F event.1) event.2)
  | .inr _ => dummyVertex F

def toClauseAnswer (label : Label) : ClauseAnswer := ⟨label.1, label.2.1, label.2.2⟩
def fromClauseAnswer (answer : ClauseAnswer) : Label := (answer.first, answer.second, answer.third)
def variableLabel (value : Bool) : Label := (value, false, false)

@[simp] theorem to_fromClauseAnswer (answer : ClauseAnswer) :
    toClauseAnswer (fromClauseAnswer answer) = answer := by
  cases answer; rfl

def variableValid (label : Label) : Bool :=
  decide (label.2.1 = false ∧ label.2.2 = false)

def incidenceAccept (F : Formula) (event : RandomEvent F)
    (clauseLabel variableAnswer : Label) : Bool :=
  variableValid variableAnswer &&
    (localSatisfies (clauseAt F event.1) (toClauseAnswer clauseLabel) &&
      decide (answerAt (toClauseAnswer clauseLabel) event.2 = variableAnswer.1))

def predicate (F : Formula) : Dart F → Label → Label → Bool
  | .inl (event, false), a, b => incidenceAccept F event a b
  | .inl (event, true), a, b => incidenceAccept F event b a
  | .inr _, _, _ => true

def raw (F : Formula) : ConstraintGraph (Vertex F) (Dart F) Label where
  reverse := reverseEquiv F
  reverse_involutive := reverse_involutive F
  tail := tail F
  accepts := predicate F
  reverse_accepts := by
    intro d a b
    cases d with
    | inl pair => rcases pair with ⟨event, orientation⟩; cases orientation <;> rfl
    | inr u => rfl

theorem raw_forward (F : Formula) (labeling : Vertex F → Label) (event : RandomEvent F) :
    (raw F).edgeSatisfied labeling (.inl (event, false)) =
      incidenceAccept F event (labeling (clauseVertex F event.1))
        (labeling (variableVertex F (nameAt (clauseAt F event.1) event.2))) := rfl

theorem incidenceAccept_true (F : Formula) (event : RandomEvent F) (a b : Label)
    (h : incidenceAccept F event a b = true) :
    localSatisfies (clauseAt F event.1) (toClauseAnswer a) = true ∧
      answerAt (toClauseAnswer a) event.2 = b.1 := by
  simp only [incidenceAccept, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

def honestLabeling (F : Formula) (A : Fin F.«variables» → Bool) : Vertex F → Label
  | .inl (.inl v) => variableLabel (A v)
  | .inl (.inr i) => fromClauseAnswer (honestAnswer (clauseAt F i) A)
  | .inr _ => variableLabel false

theorem incidence_honest (F : Formula) (A : Fin F.«variables» → Bool)
    (sat : ∀ «c» ∈ F.clauses, «c».eval A = true) (event : RandomEvent F) :
    incidenceAccept F event (honestLabeling F A (clauseVertex F event.1))
      (honestLabeling F A (variableVertex F (nameAt (clauseAt F event.1) event.2))) = true := by
  have hc : (clauseAt F event.1).eval A = true := sat _ (List.getElem_mem _)
  simp [incidenceAccept, honestLabeling, clauseVertex, variableVertex, variableLabel,
    variableValid, honest_satisfies, honest_answerAt, hc]

theorem raw_completeness (F : Formula) (sat : F.Satisfiable) : (raw F).Satisfiable := by
  rcases sat with ⟨A, hA⟩
  refine ⟨honestLabeling F A, fun d => ?_⟩
  cases d with
  | inl pair =>
    rcases pair with ⟨event, orientation⟩
    cases orientation <;> exact incidence_honest F A hA event
  | inr u => rfl

theorem clauseAnswer_eq_of_slots (a b : ClauseAnswer)
    (h : ∀ s, answerAt a s = answerAt b s) : a = b := by
  rcases a with ⟨a₀, a₁, a₂⟩
  rcases b with ⟨b₀, b₁, b₂⟩
  have h₀ : a₀ = b₀ := h .first
  have h₁ : a₁ = b₁ := h .second
  have h₂ : a₂ = b₂ := h .third
  cases h₀; cases h₁; cases h₂; rfl

theorem raw_reflects (F : Formula) (sat : (raw F).Satisfiable) : F.Satisfiable := by
  rcases sat with ⟨labeling, hlabeling⟩
  let A : Fin F.«variables» → Bool := fun v => (labeling (variableVertex F v)).1
  have slot_correct (i : Fin F.clauses.length) (s : Slot) :
      localSatisfies (clauseAt F i) (toClauseAnswer (labeling (clauseVertex F i))) = true ∧
        answerAt (toClauseAnswer (labeling (clauseVertex F i))) s =
          A (nameAt (clauseAt F i) s) := by
    exact incidenceAccept_true F (i, s) _ _ (hlabeling (.inl ((i, s), false)))
  have clause_correct (i : Fin F.clauses.length) : (clauseAt F i).eval A = true := by
    have equal : toClauseAnswer (labeling (clauseVertex F i)) = honestAnswer (clauseAt F i) A :=
      clauseAnswer_eq_of_slots _ _ (fun s => by
        simpa only [honest_answerAt] using (slot_correct i s).2)
    have satisfied := (slot_correct i .first).1
    rw [equal, honest_satisfies] at satisfied
    exact satisfied
  refine ⟨A, fun «c» hc => ?_⟩
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hc
  simpa only [clauseAt, heq] using clause_correct ⟨i, hi⟩

theorem raw_satisfiable_iff (F : Formula) : (raw F).Satisfiable ↔ F.Satisfiable :=
  ⟨raw_reflects F, raw_completeness F⟩

@[simp] theorem card_vertex (F : Formula) :
    Fintype.card (Vertex F) = F.«variables» + F.clauses.length + 1 := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart (F : Formula) :
    Fintype.card (Dart F) = 6 * F.clauses.length + 1 := by
  simp [Dart, RandomEvent, Fintype.card_sum, Fintype.card_prod]
  omega

abbrev CompactVertex (F : Formula) := Vertex (NameCompaction.compact F)
abbrev CompactDart (F : Formula) := Dart (NameCompaction.compact F)

def build (F : Formula) : ConstraintGraph (CompactVertex F) (CompactDart F) Label :=
  raw (NameCompaction.compact F)

theorem build_satisfiable_iff (F : Formula) : (build F).Satisfiable ↔ F.Satisfiable := by
  exact (raw_satisfiable_iff (NameCompaction.compact F)).trans
    (NameCompaction.compact_satisfiable_iff F)

theorem build_vertex_bound (F : Formula) :
    Fintype.card (CompactVertex F) ≤ 4 * F.clauses.length + 1 := by
  have h := NameCompaction.compact_active_bound F
  simp only [CompactVertex, card_vertex, NameCompaction.compact_clause_count]
  omega

theorem build_dart_count (F : Formula) :
    Fintype.card (CompactDart F) = 6 * F.clauses.length + 1 := by
  simp only [CompactDart, card_dart, NameCompaction.compact_clause_count]

theorem build_initial_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : CompactVertex F → Label) : 1 ≤ (build F).rejectionCount labeling := by
  apply ConstraintGraph.rejectionCount_positive
  intro h
  exact unsat ((build_satisfiable_iff F).mp h)

theorem build_inverse_size_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : CompactVertex F → Label) :
    Fintype.card (CompactDart F) ≤
      (6 * F.clauses.length + 1) * (build F).rejectionCount labeling := by
  rw [build_dart_count]
  simpa only [Nat.mul_one] using
    Nat.mul_le_mul_left (6 * F.clauses.length + 1) (build_initial_gap F unsat labeling)

end UniqueGames.Foundations.PCP.InitialGraph

end OAI
