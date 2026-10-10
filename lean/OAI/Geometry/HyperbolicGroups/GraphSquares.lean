import Mathlib
import OAI.Geometry.HyperbolicGroups.Graph

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate

lemma code_injective : Function.Injective code := by
  intro e f hh
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  all_goals
    have he := e.val.2.isLt
    have hf := f.val.2.isLt
    unfold code at hh
    omega

/-- Every literal nonbacktracking core two-path is one of the ninety
square slots, up to reversal. -/
lemma twoPath_complete {a b c : CoreGeometry.Vertex}
    (hab : CoreGeometry.Adjacent a b) (hbc : CoreGeometry.Adjacent b c) (hac : a ≠ c) :
    ∃ τ : TwoPath, (left τ = a ∧ middle τ = b ∧ right τ = c) ∨
      (left τ = c ∧ middle τ = b ∧ right τ = a) := by
  rcases a with r | l <;> rcases b with r' | l' <;> rcases c with r'' | l''
  all_goals first | exact hab.elim | exact hbc.elim | skip
  · have hne : r ≠ r'' := fun he => hac (congrArg Sum.inl he)
    let e : Edge := ⟨(r,l'), hab⟩
    let f : Edge := ⟨(r'',l'), hbc⟩
    have hcode : code e ≠ code f := fun he => hne (congrArg (fun e : Edge => e.val.1) (code_injective he))
    by_cases hlt : code e < code f
    · refine ⟨⟨(e,f), hlt, Or.inr rfl⟩, Or.inl ?_⟩
      simp [left, middle, right, e, f, hne]
    · refine ⟨⟨(f,e), lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hcode), Or.inr rfl⟩, Or.inr ?_⟩
      simp [left, middle, right, e, f, Ne.symm hne]
  · have hne : l ≠ l'' := fun he => hac (congrArg Sum.inr he)
    let e : Edge := ⟨(r',l), hab⟩
    let f : Edge := ⟨(r',l''), hbc⟩
    have hcode : code e ≠ code f := fun he => hne (congrArg (fun e : Edge => e.val.2) (code_injective he))
    by_cases hlt : code e < code f
    · refine ⟨⟨(e,f), hlt, Or.inl rfl⟩, Or.inl ?_⟩
      simp [left, middle, right, e, f]
    · refine ⟨⟨(f,e), lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hcode), Or.inl rfl⟩, Or.inr ?_⟩
      simp [left, middle, right, e, f]

lemma square_core_ne (τ : TwoPath) : τ.val.1 ≠ τ.val.2 := by
  intro he
  have hh := τ.property.1
  rw [he] at hh
  exact (lt_irrefl _ hh)

lemma admissible_square_pair (τ : TwoPath) (e f : Field)
    (he : e ∈ squareSupport τ) (hf : f ∈ squareSupport τ) : Admissible {e,f} := by
  exact Or.inr ⟨τ, by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro he hf,
    Finset.card_le_two⟩

lemma first_mem_square (τ : TwoPath) : (first τ).field ∈ squareSupport τ := by
  simp [first_field, squareSupport]
lemma second_mem_square (τ : TwoPath) : (second τ).field ∈ squareSupport τ := by
  simp [second_field, squareSupport]
lemma fresh_mem_square (τ : TwoPath) (j : Fin 2) : (.inr (τ,j) : Field) ∈ squareSupport τ := by
  fin_cases j <;> simp [squareSupport]

end MasterGraph
end HyperbolicObstruction
end
end

section

end
end

end OAI
