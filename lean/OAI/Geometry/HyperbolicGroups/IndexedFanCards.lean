import Mathlib
import OAI.Geometry.HyperbolicGroups.IndexedFanCounts

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink.IndexedFanData
attribute [local instance] Classical.propDecidable
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

abbrev TurnIndex := {p : Σ z,L z // ∃ f, D.mark p.1 p.2 = Mark.top f}
abbrev TriangleIndex := {p : Σ z,L z // D.mark p.1 p.2 = Mark.triangle}

lemma turnIndex_card : Fintype.card D.TurnIndex = D.turns := by
  rw [show Fintype.card D.TurnIndex = _ from Fintype.card_subtype _]
  have hh := Finset.sum_boole (R := ℕ)
    (fun p : Σ z,L z => ∃ f, D.mark p.1 p.2 = Mark.top f) Finset.univ
  simp only [Nat.cast_id] at hh
  rw [← hh,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  cases he : D.mark z i <;> simp [he,state,Mark.plain,State.turn]

lemma triangleIndex_card : Fintype.card D.TriangleIndex = D.triangles := by
  rw [show Fintype.card D.TriangleIndex = _ from Fintype.card_subtype _]
  have hh := Finset.sum_boole (R := ℕ)
    (fun p : Σ z,L z => D.mark p.1 p.2 = Mark.triangle) Finset.univ
  simp only [Nat.cast_id] at hh
  rw [← hh,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  cases he : D.mark z i <;> simp [he,state,Mark.plain,State.f]

abbrev BoundaryIndex := {p : Σ z,L z // (D.state p.1 p.2).active ≠
  (D.state p.1 (D.next p.1 p.2)).active}

lemma boundaryIndex_card : Fintype.card D.BoundaryIndex = D.boundary := by
  rw [show Fintype.card D.BoundaryIndex = _ from Fintype.card_subtype _]
  have hh := Finset.sum_boole (R := ℕ)
    (fun p : Σ z,L z => (D.state p.1 p.2).active ≠ (D.state p.1 (D.next p.1 p.2)).active) Finset.univ
  simp only [Nat.cast_id] at hh
  rw [← hh,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (D.state z i).active = (D.state z (D.next z i)).active <;>
    simp [State.boundary,h]

section Family
variable {J : Type*} [Fintype J] {I F : J → Type*} {O : Type*}
  {L : (j : J) → I j → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (F j)]
  [Fintype O] [∀ j z, Fintype (L j z)]
  (D : (j : J) → IndexedFanData (I j) (F j) O (L j))
lemma family_turnIndex_card : Fintype.card (Σ j, (D j).TurnIndex) = ∑ j, (D j).turns := by
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => (D j).turnIndex_card)
lemma family_natTurnIndex_card : Nat.card (Σ j, (D j).TurnIndex) = ∑ j, (D j).turns := by
  rw [Nat.card_eq_fintype_card]
  exact family_turnIndex_card D
lemma family_natBoundaryIndex_card : Nat.card (Σ j, (D j).BoundaryIndex) = ∑ j, (D j).boundary := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => (D j).boundaryIndex_card)
lemma family_natTriangleIndex_card : Nat.card (Σ j, (D j).TriangleIndex) = ∑ j, (D j).triangles := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => (D j).triangleIndex_card)
end Family
end HyperbolicObstruction.FanLink.IndexedFanData
end
end

section

end
end

end OAI
