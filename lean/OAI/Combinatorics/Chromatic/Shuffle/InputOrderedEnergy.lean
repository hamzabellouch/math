import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.InputTorusEnergy
import OAI.Combinatorics.Chromatic.GradedAlgebra.SupportedConvolution

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open WeightedTorusSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ)

def crossDiagonal (d : I → ℕ) : ℤ := ∑i,(1-(a i i:ℤ))*(d i:ℤ)^2

omit [DecidableEq I] in
lemma crossInteraction_euler (d : I → ℕ) :
    crossInteraction a d=crossDiagonal a d-eulerForm a d d := by
  have H : crossDiagonal a d=(∑ i,(d i:ℤ)*(d i:ℤ))-∑i,(a i i:ℤ)*(d i:ℤ)^2 := by
    rw [crossDiagonal,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [H,crossInteraction,eulerForm]
  ring

omit [DecidableEq I] in
lemma crossDiagonal_add_disjoint (d e : I → ℕ) (hde : ∀i,d i=0 ∨ e i=0) :
    crossDiagonal a (d+e)=crossDiagonal a d+crossDiagonal a e := by
  rw [crossDiagonal,crossDiagonal,crossDiagonal,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hde i with H|H <;> simp [H]

omit [DecidableEq I] in
lemma eulerForm_zero_separated (d e : I → ℕ) (hde : ∀i,d i=0 ∨ e i=0)
    (ha : ∀i j,d i≠0 → e j≠0 → a i j=0) : eulerForm a d e=0 := by
  unfold eulerForm
  have H₁ : (∑i,(d i:ℤ)*(e i:ℤ))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rcases hde i with H|H <;> simp [H]
  have H₂ : (∑ i,∑j,(a i j:ℤ)*(d i:ℤ)*(e j:ℤ))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hd : d i=0
    · simp [hd]
    · by_cases he : e j=0
      · simp [he]
      · simp [ha i j hd he]
  rw [H₁,H₂,sub_self]

omit [DecidableEq I] in
lemma crossInteraction_add_separated (d e : I → ℕ) (hde : ∀i,d i=0 ∨ e i=0)
    (ha : ∀i j,d i≠0 → e j≠0 → a i j=0) :
    crossInteraction a (d+e)=crossInteraction a d+crossInteraction a e+
      (eulerForm a d e-eulerForm a e d) := by
  rw [crossInteraction_euler,crossInteraction_euler,crossInteraction_euler,
    crossDiagonal_add_disjoint a d e hde,eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,
    eulerForm_zero_separated a d e hde ha]
  ring

lemma crossInteraction_restrict_union (S T : Finset I) (hST : Disjoint S T)
    (ha : ∀i∈S,∀j∈T,a i j=0) (d : I → ℕ) (hd : Supported (S∪T) d) :
    crossInteraction a d=crossInteraction a (restrictDim S d)+crossInteraction a (restrictDim T d)+
      (eulerForm a (restrictDim S d) (restrictDim T d)-eulerForm a (restrictDim T d) (restrictDim S d)) := by
  conv_lhs => rw [←restrictDim_split S T hST d hd]
  apply crossInteraction_add_separated
  · intro i
    by_cases hS : i∈S
    · exact Or.inr (restrictDim_supported T d i (fun hT=>Finset.disjoint_left.mp hST hS hT))
    · exact Or.inl (restrictDim_supported S d i hS)
  · intro i j hi hj
    apply ha
    · by_contra H
      exact hi (restrictDim_supported S d i H)
    · by_contra H
      exact hj (restrictDim_supported T d j H)

end
end ElementaryPositivity.RawShuffle

end

end OAI
