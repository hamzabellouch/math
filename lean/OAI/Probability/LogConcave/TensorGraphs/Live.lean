import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

section
namespace LogConcaveSampling.Frontier

variable {E : Type*} (a b : E → ℕ)

abbrev Live (k : ℕ) := {e : E // a e≤k ∧ k<b e}
abbrev Incoming (k : ℕ) := {e : E // b e=k+1}
abbrev Outgoing (k : ℕ) := {e : E // a e=k+1}
abbrev Spectator (k : ℕ) := {e : E // a e≤k ∧ k+1<b e}

def splitIncoming (hab : ∀e,a e<b e) (k : ℕ) :
    Live a b k ≃ Incoming b k ⊕ Spectator a b k where
  toFun e := if h : b e.val=k+1 then Sum.inl ⟨e.val,h⟩ else
    Sum.inr ⟨e.val,e.property.1,by have := e.property.2; omega⟩
  invFun e := match e with
    | Sum.inl e => ⟨e.val,by have := hab e.val; have := e.property; omega,
        by have := e.property; omega⟩
    | Sum.inr e => ⟨e.val,e.property.1,by have := e.property.2; omega⟩
  left_inv e := by
    dsimp only
    split_ifs <;> rfl
  right_inv e := by
    cases e with
    | inl e => simp only [e.property,dite_eq_left]
    | inr e =>
      have hn : b e.val≠k+1 := by have := e.property.2; omega
      simp [hn]

def splitOutgoing (hab : ∀e,a e<b e) (k : ℕ) :
    Live a b (k+1) ≃ Outgoing a k ⊕ Spectator a b k where
  toFun e := if h : a e.val=k+1 then Sum.inl ⟨e.val,h⟩ else
    Sum.inr ⟨e.val,by have := e.property.1; omega,e.property.2⟩
  invFun e := match e with
    | Sum.inl e => ⟨e.val,by have := e.property; omega,
        by have := hab e.val; have := e.property; omega⟩
    | Sum.inr e => ⟨e.val,by have := e.property.1; omega,e.property.2⟩
  left_inv e := by
    dsimp only
    split_ifs <;> rfl
  right_inv e := by
    cases e with
    | inl e => simp only [e.property,dite_eq_left]
    | inr e =>
      have hn : a e.val≠k+1 := by have := e.property.1; omega
      simp [hn]

def inputCoordinates {C : Type*} (hab : ∀e,a e<b e) (k : ℕ) :
    (Live a b k → C) ≃ (Incoming b k → C) × (Spectator a b k → C) :=
  (Equiv.arrowCongr (splitIncoming a b hab k) (Equiv.refl C)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

def outputCoordinates {C : Type*} (hab : ∀e,a e<b e) (k : ℕ) :
    (Live a b (k+1) → C) ≃ (Outgoing a k → C) × (Spectator a b k → C) :=
  (Equiv.arrowCongr (splitOutgoing a b hab k) (Equiv.refl C)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

lemma inputCoordinates_apply {C : Type*} (hab : ∀e,a e<b e) (k : ℕ)
    (x : Live a b k → C) :
    (inputCoordinates a b hab k x).1=(fun e => x ⟨e.val,by
      have := hab e.val; have := e.property; omega,by have := e.property; omega⟩) ∧
    (inputCoordinates a b hab k x).2=(fun e => x ⟨e.val,e.property.1,by have := e.property.2; omega⟩) := by
  constructor <;> rfl

lemma outputCoordinates_apply {C : Type*} (hab : ∀e,a e<b e) (k : ℕ)
    (x : Live a b (k+1) → C) :
    (outputCoordinates a b hab k x).1=(fun e => x ⟨e.val,by have := e.property; omega,
      by have := hab e.val; have := e.property; omega⟩) ∧
    (outputCoordinates a b hab k x).2=(fun e => x ⟨e.val,by have := e.property.1; omega,e.property.2⟩) := by
  constructor <;> rfl
end LogConcaveSampling.Frontier

end
end UpperProof
end
end
end

end OAI
