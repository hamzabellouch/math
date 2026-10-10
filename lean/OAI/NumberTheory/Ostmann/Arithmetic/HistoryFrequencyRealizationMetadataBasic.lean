import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyExposure

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts Characters.FrequencyExposure

def ScheduleMatches {R : ℕ} (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (p : List Bool) :
    {l : ℕ} → History l → History l → Prop
  | _, .leaf _, .leaf _ => True
  | _, .node a _ u hp hm left right, .node a' _ u' hp' hm' left' right' =>
    (d p).s = a.frequency ∧ (d p).s' = a'.frequency ∧
    (d p).v = left.root.frequency ∧ (d p).w = right.root.frequency ∧
    (d p).v' = left'.root.frequency ∧ (d p).w' = right'.root.frequency ∧
    (f p).1 = ⟨fixedProduct hp, fixedProduct hm, (u.map SmallSlot.value).prod⟩ ∧
    (f p).2 = ⟨fixedProduct hp', fixedProduct hm', (u'.map SmallSlot.value).prod⟩ ∧
    ScheduleMatches d f (false :: p) left left' ∧
    ScheduleMatches d f (true :: p) right right'

@[simp] theorem scheduleMatches_leaf {R : ℕ} (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (p : List Bool) (a a' : State) :
    ScheduleMatches d f p (.leaf a) (.leaf a') := trivial

@[simp] theorem scheduleMatches_node {R l : ℕ} (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (p : List Bool)
    (a a' : State) (pivot pivot' : ℕ) (u hp hm u' hp' hm' : List SmallSlot)
    (left right left' right' : History l) :
    ScheduleMatches d f p (.node a pivot u hp hm left right)
      (.node a' pivot' u' hp' hm' left' right') ↔
    (d p).s = a.frequency ∧ (d p).s' = a'.frequency ∧
    (d p).v = left.root.frequency ∧ (d p).w = right.root.frequency ∧
    (d p).v' = left'.root.frequency ∧ (d p).w' = right'.root.frequency ∧
    (f p).1 = ⟨fixedProduct hp, fixedProduct hm, (u.map SmallSlot.value).prod⟩ ∧
    (f p).2 = ⟨fixedProduct hp', fixedProduct hm', (u'.map SmallSlot.value).prod⟩ ∧
    ScheduleMatches d f (false :: p) left left' ∧
    ScheduleMatches d f (true :: p) right right' := Iff.rfl

theorem scheduleMatches_append_iff {R l : ℕ} (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (p q : List Bool)
    (h h' : History l) :
    ScheduleMatches (fun r => d (r ++ q)) (fun r => f (r ++ q)) p h h' ↔
      ScheduleMatches d f (p ++ q) h h' := by
  induction h generalizing p with
  | leaf a => cases h'; rfl
  | @node l a pivot u hp hm left right ihl ihr =>
    cases h' with
    | node a' pivot' u' hp' hm' left' right' =>
      simp only [ScheduleMatches, List.cons_append, ihl, ihr]

def reverseAddressSchedule {α : Type*} (root : α)
    (left right : List Bool → α) (p : List Bool) : α :=
  match p.reverse with
  | [] => root
  | false :: q => left q.reverse
  | true :: q => right q.reverse

@[simp] theorem reverseAddressSchedule_nil {α : Type*} (root : α)
    (left right : List Bool → α) : reverseAddressSchedule root left right [] = root := rfl

@[simp] theorem reverseAddressSchedule_append_false {α : Type*} (root : α)
    (left right : List Bool → α) (p : List Bool) :
    reverseAddressSchedule root left right (p ++ [false]) = left p := by
  simp [reverseAddressSchedule]

@[simp] theorem reverseAddressSchedule_append_true {α : Type*} (root : α)
    (left right : List Bool → α) (p : List Bool) :
    reverseAddressSchedule root left right (p ++ [true]) = right p := by
  simp [reverseAddressSchedule]

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
