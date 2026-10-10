import Mathlib.Data.Fintype.Prod
import Init.Data.List.Count
import Lean.Elab.Tactic.Omega

namespace OAI

namespace MarkovSuperreflexivity

abbrev Letter := Fin 2 × Bool

namespace Letter

def inv (s : Letter) : Letter := (s.1, !s.2)

def isPositive (s : Letter) : Prop := s.2 = true

def isNegative (s : Letter) : Prop := s.2 = false

@[simp] theorem inv_inv (s : Letter) : s.inv.inv = s := by
  rcases s with ⟨i, b⟩
  cases b <;> rfl

@[simp] theorem inv_ne_self (s : Letter) : s.inv ≠ s := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [inv]

theorem inv_injective : Function.Injective inv := by
  intro s a h
  simpa only [inv_inv] using congrArg inv h

theorem eq_inv_iff (s a : Letter) : s = a.inv ↔ a = s.inv := by
  constructor <;> intro h <;> simpa only [inv_inv] using (congrArg inv h).symm

end Letter

@[simp] theorem card_letter : Fintype.card Letter = 4 := by
  simp [Letter]

def positiveCount (w : List Letter) : ℕ := w.countP (fun s => s.2)

def negativeCount (w : List Letter) : ℕ := w.countP (fun s => !s.2)

@[simp] theorem positiveCount_nil : positiveCount [] = 0 := rfl

@[simp] theorem negativeCount_nil : negativeCount [] = 0 := rfl

theorem counts_nil : positiveCount [] = 0 ∧ negativeCount [] = 0 := ⟨rfl, rfl⟩

@[simp] theorem positiveCount_cons (s : Letter) (w : List Letter) :
    positiveCount (s :: w) = positiveCount w + (if s.2 then 1 else 0) :=
  List.countP_cons

@[simp] theorem negativeCount_cons (s : Letter) (w : List Letter) :
    negativeCount (s :: w) = negativeCount w + (if !s.2 then 1 else 0) :=
  List.countP_cons

@[simp] theorem positiveCount_append (v w : List Letter) :
    positiveCount (v ++ w) = positiveCount v + positiveCount w :=
  List.countP_append

@[simp] theorem negativeCount_append (v w : List Letter) :
    negativeCount (v ++ w) = negativeCount v + negativeCount w :=
  List.countP_append

theorem positiveCount_add_negativeCount (w : List Letter) :
    positiveCount w + negativeCount w = w.length := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases hsign : s.2 <;>
      simp [positiveCount_cons, negativeCount_cons, hsign] <;> omega

theorem positiveCount_le_length (w : List Letter) : positiveCount w ≤ w.length :=
  List.countP_le_length

theorem negativeCount_le_length (w : List Letter) : negativeCount w ≤ w.length :=
  List.countP_le_length

end MarkovSuperreflexivity

end OAI
