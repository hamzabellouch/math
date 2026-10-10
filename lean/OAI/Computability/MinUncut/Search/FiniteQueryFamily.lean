import Mathlib
import OAI.Computability.MinUncut.Graphs.SignedGraph
import OAI.Computability.MinUncut.Analysis.GaussianRows

namespace OAI

section
noncomputable section
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

abbrev FamilyQuestion (Name I : Type*) := (I → Equation Name) ⊕ (I → SecondQuestion Name)

def FamilyAlphabet : FamilyQuestion Name I → Type _
  | .inl U => FirstAlphabet U
  | .inr Q => SecondAlphabet Q

instance familyAlphabetFintype (q : FamilyQuestion Name I) : Fintype (FamilyAlphabet q) := by
  cases q <;> unfold FamilyAlphabet <;> infer_instance

def familyBase : (q : FamilyQuestion Name I) → FamilyAlphabet q
  | .inl U => fun j => origin (U j)
  | .inr _ => fun _ _ => 0

abbrev FamilyVariable (Name I : Type*) [Fintype I] := Variable (familyBase (Name := Name) (I := I))

def variableProof (y : FamilyVariable Name I → Bool) : ProofFamily Name I where
  first U := ⟨answer familyBase y (.inl U),answer_folded familyBase y (.inl U)⟩
  second Q := ⟨answer familyBase y (.inr Q),answer_folded familyBase y (.inr Q)⟩

def ProofFamily.queryAnswer (f : ProofFamily Name I) :
    (q : FamilyQuestion Name I) → (FamilyAlphabet q → Bool) → Bool
  | .inl U => (f.first U).answer
  | .inr Q => (f.second Q).answer

lemma ProofFamily.queryAnswer_folded (f : ProofFamily Name I) : Folded f.queryAnswer := by
  intro q P
  cases q with
  | inl U => exact (f.first U).folded P
  | inr Q => exact (f.second Q).folded P

def ProofFamily.assignment (f : ProofFamily Name I) : FamilyVariable Name I → Bool :=
  fun p => f.queryAnswer p.1 p.2.val

lemma ProofFamily.answer_assignment (f : ProofFamily Name I) :
    answer familyBase f.assignment=f.queryAnswer :=
  answer_of_folded familyBase f.queryAnswer f.queryAnswer_folded

lemma foldedProof_ext {A : Type*} {f g : FoldedProof A} (h : f.answer=g.answer) : f=g := by
  cases f
  cases g
  cases h
  rfl

lemma proofFamily_ext {f g : ProofFamily Name I}
    (hf : f.first=g.first) (hg : f.second=g.second) : f=g := by
  cases f
  cases g
  cases hf
  cases hg
  rfl

lemma ProofFamily.variableProof_assignment (f : ProofFamily Name I) : variableProof f.assignment=f := by
  apply proofFamily_ext
  · funext U
    apply foldedProof_ext
    exact (congrFun f.answer_assignment (.inl U))
  · funext Q
    apply foldedProof_ext
    exact (congrFun f.answer_assignment (.inr Q))

lemma variableProof_queryAnswer (y : FamilyVariable Name I → Bool) :
    (variableProof y).queryAnswer=answer familyBase y := by
  funext q
  cases q <;> rfl
end MinUncut.Outer

end
end

end OAI
