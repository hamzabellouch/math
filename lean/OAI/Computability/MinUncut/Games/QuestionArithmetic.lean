import Mathlib
import OAI.Computability.MinUncut.Estimates.Bridge

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences
variable {N t : ℕ}

def equationNumber (E : Equation (Fin N)) : ℕ :=
  E.rhs.val+2*∑p : Fin 3, (E.names p).val*N^p.val

def firstNumber (U : Fin t → Equation (Fin N)) : ℕ :=
  ∑i : Fin t,equationNumber (U i)*(N^3*2)^i.val

def secondNumber (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3) : ℕ :=
  ∑i : Fin t,(if h i then ((U i).names (pos i)).val else N+equationNumber (U i))*(N+N^3*2)^i.val

lemma equation_code (E : Equation (Fin N)) : ((equationEncoding N).code E).val=equationNumber E := rfl
lemma first_code (U : Fin t → Equation (Fin N)) :
    ((questionEncoding N t).code (.inl U)).val=firstNumber U := rfl
lemma second_code (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3) :
    ((questionEncoding N t).code (.inr (secondQuestion U h pos))).val=
      (N^3*2)^t+secondNumber U h pos := by
  change (N^3*2)^t+(∑i : Fin t, ((secondQuestionEncoding N).code (slotQuestion (U i) (h i) (pos i))).val*(N+N^3*2)^i.val)=_
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases h i <;> rfl

def tableNumber (f : (Fin t → Triple) → Bool) : ℕ :=
  (((ambientEncoding t).function Encoding.bool).code f).val

lemma variable_number (v : FamilyVariable (Fin N) (Fin t)) :
    (variableCode v).val= tableNumber (extendTable v.1 v.2.val)+
      2^((2^3)^t)*((questionEncoding N t).code v.1).val := rfl

variable {h : Fin t → Bool}
def Query.leftNumber (T : Query h) (U : Fin t → Equation (Fin N)) (pos : Fin t → Fin 3) : ℕ :=
  tableNumber (T.leftTable pos (signature U))+
    2^((2^3)^t)*(if T.first then firstNumber U else (N^3*2)^t+secondNumber U h pos)

def Query.rightNumber (T : Query h) (U : Fin t → Equation (Fin N)) (pos : Fin t → Fin 3) : ℕ :=
  tableNumber T.rightTable+2^((2^3)^t)*((N^3*2)^t+secondNumber U h pos)

lemma Query.left_number (T : Query h) (U : Fin t → Equation (Fin N)) (pos : Fin t → Fin 3) :
    (variableCode ((T.realize U pos).signed familyBase).left).val=T.leftNumber U pos := by
  rw [variable_number]
  change tableNumber (extendTable _ (rep (familyBase _) (T.realize U pos).left.2).val)+_= _
  rw [T.left_extended]
  unfold Query.leftNumber Query.realize
  by_cases hf : T.first=true
  · simp only [ite_eq_left hf,comparison,QueryDemand.signed,vertex,first_code]
  · simp only [ite_eq_right hf,comparison,QueryDemand.signed,vertex,second_code]

lemma Query.right_number (T : Query h) (U : Fin t → Equation (Fin N)) (pos : Fin t → Fin 3) :
    (variableCode ((T.realize U pos).signed familyBase).right).val=T.rightNumber U pos := by
  rw [variable_number]
  change tableNumber (extendTable _ (rep (familyBase _) (T.realize U pos).right.2).val)+_= _
  rw [T.right_extended]
  unfold Query.rightNumber Query.realize
  by_cases hf : T.first=true
  · simp only [ite_eq_left hf,comparison,QueryDemand.signed,vertex,second_code]
  · simp only [ite_eq_right hf,comparison,QueryDemand.signed,vertex,second_code]

end MinUncut.Outer.LocalTemplate

end
end

end OAI
