import Mathlib
import OAI.Computability.MinUncut.PCP.Occurrences
import OAI.Computability.MinUncut.Search.FiniteQueryFamily

namespace OAI

section
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences

def equationPair (N : ℕ) : Equation (Fin N) ≃ ((Fin 3 → Fin N) × F₂) where
  toFun E := (E.names,E.rhs)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def fieldEncoding : Encoding F₂ := ⟨2,Equiv.refl _⟩

def equationEncoding (N : ℕ) : Encoding (Equation (Fin N)) :=
  let a := ((Encoding.fin 3).function (Encoding.fin N)).prod fieldEncoding
  ⟨a.size,(equationPair N).trans a.code⟩

def secondQuestionEncoding (N : ℕ) : Encoding (SecondQuestion (Fin N)) :=
  (Encoding.fin N).sum (equationEncoding N)

def questionEncoding (N t : ℕ) : Encoding (FamilyQuestion (Fin N) (Fin t)) :=
  ((Encoding.fin t).function (equationEncoding N)).sum
    ((Encoding.fin t).function (secondQuestionEncoding N))

def ambientEncoding (t : ℕ) : Encoding (Fin t → Triple) :=
  (Encoding.fin t).function ((Encoding.fin 3).function fieldEncoding)

instance validDecidable {N : ℕ} (E : Equation (Fin N)) (a : Triple) : Decidable (Valid E a) :=
  inferInstanceAs (Decidable (parity a=E.rhs ∧ ∀p p', E.names p=E.names p' → a p=a p'))

def encodeFirst {N t : ℕ} (U : Fin t → Equation (Fin N)) (a : FirstAlphabet U) : Fin t → Triple :=
  fun j => (a j).val

def decodeFirst {N t : ℕ} (U : Fin t → Equation (Fin N)) (x : Fin t → Triple) :
    Option (FirstAlphabet U) :=
  if h : ∀j, Valid (U j) (x j) then some (fun j => ⟨x j,h j⟩) else none

lemma decodeFirst_encodeFirst {N t : ℕ} (U : Fin t → Equation (Fin N)) (a : FirstAlphabet U) :
    decodeFirst U (encodeFirst U a)=some a := by
  have ha : ∀j, Valid (U j) (encodeFirst U a j) := fun j => (a j).property
  simp only [decodeFirst,dite_eq_left ha]
  rfl

lemma secondSlotCount_le {N : ℕ} (q : SecondQuestion (Fin N)) : secondSlotCount q≤3 := by
  cases q <;> norm_num [secondSlotCount]

def encodeSecond {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (a : SecondAlphabet Q) : Fin t → Triple :=
  fun j k => if h : k.val<secondSlotCount (Q j) then a j ⟨k.val,h⟩ else 0

def decodeSecond {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (x : Fin t → Triple) : SecondAlphabet Q :=
  fun j k => x j ⟨k.val,k.isLt.trans_le (secondSlotCount_le (Q j))⟩

lemma decodeSecond_encodeSecond {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (a : SecondAlphabet Q) :
    decodeSecond Q (encodeSecond Q a)=a := by
  funext j k
  exact dite_eq_left k.isLt

def encodeAlphabet {N t : ℕ} : (q : FamilyQuestion (Fin N) (Fin t)) → FamilyAlphabet q → (Fin t → Triple)
  | .inl U => encodeFirst U
  | .inr Q => encodeSecond Q

def decodeAlphabet {N t : ℕ} : (q : FamilyQuestion (Fin N) (Fin t)) → (Fin t → Triple) → Option (FamilyAlphabet q)
  | .inl U => decodeFirst U
  | .inr Q => fun x => some (decodeSecond Q x)

lemma decodeAlphabet_encodeAlphabet {N t : ℕ} (q : FamilyQuestion (Fin N) (Fin t)) (a : FamilyAlphabet q) :
    decodeAlphabet q (encodeAlphabet q a)=some a := by
  cases q with
  | inl U => exact decodeFirst_encodeFirst U a
  | inr Q => exact congrArg some (decodeSecond_encodeSecond Q a)

def extendTable {N t : ℕ} (q : FamilyQuestion (Fin N) (Fin t)) (R : FamilyAlphabet q → Bool) :
    (Fin t → Triple) → Bool := fun x => ((decodeAlphabet q x).map R).getD false

lemma extendTable_eval {N t : ℕ} (q : FamilyQuestion (Fin N) (Fin t)) (R : FamilyAlphabet q → Bool)
    (a : FamilyAlphabet q) : extendTable q R (encodeAlphabet q a)=R a := by
  simp only [extendTable,decodeAlphabet_encodeAlphabet,Option.map_some,Option.getD_some]

lemma extendTable_injective {N t : ℕ} (q : FamilyQuestion (Fin N) (Fin t)) :
    Function.Injective (extendTable q) := by
  intro R S h
  funext a
  simpa only [extendTable_eval] using congrFun h (encodeAlphabet q a)

def paddedVariableEncoding (N t : ℕ) :
    Encoding (FamilyQuestion (Fin N) (Fin t) × ((Fin t → Triple) → Bool)) :=
  (questionEncoding N t).prod ((ambientEncoding t).function Encoding.bool)

def variableCode {N t : ℕ} (v : FamilyVariable (Fin N) (Fin t)) : Fin (paddedVariableEncoding N t).size :=
  (paddedVariableEncoding N t).code (v.1,extendTable v.1 v.2.val)

lemma variableCode_injective {N t : ℕ} : Function.Injective (variableCode (N := N) (t := t)) := by
  rintro ⟨q,R⟩ ⟨s,S⟩ h
  have hp := (paddedVariableEncoding N t).code.injective h
  have hq : q=s := congrArg Prod.fst hp
  subst s
  have hR : R=S := Subtype.ext (extendTable_injective q (congrArg Prod.snd hp))
  subst S
  rfl

lemma paddedVariableEncoding_size (N t : ℕ) :
    (paddedVariableEncoding N t).size=
      ((N^3*2)^t+(N+N^3*2)^t)*2^((2^3)^t) := rfl

end MinUncut.Outer

end

end OAI
