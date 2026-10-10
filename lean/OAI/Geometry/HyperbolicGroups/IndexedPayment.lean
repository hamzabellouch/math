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

/-- Outgoing and incoming exceptional-port incidences of selected top turns. -/
abbrev PaymentIndex := {p : (Σ z,L z) × Bool //
  (∃ f, D.mark p.1.1 p.1.2 = Mark.top f) ∧
    D.line p.1.1 (if p.2 then p.1.2 else D.next p.1.1 p.1.2) = false}

lemma paymentIndex_card : Fintype.card D.PaymentIndex = D.payments := by
  rw [show Fintype.card D.PaymentIndex = _ from Fintype.card_subtype _]
  have hh := Finset.sum_boole (R := ℕ) (fun p : (Σ z,L z) × Bool =>
    (∃ f, D.mark p.1.1 p.1.2 = Mark.top f) ∧
      D.line p.1.1 (if p.2 then p.1.2 else D.next p.1.1 p.1.2) = false) Finset.univ
  simp only [Nat.cast_id] at hh
  rw [← hh,Fintype.sum_prod_type,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  cases he : D.mark z i <;> cases hx : D.line z i <;> cases hy : D.line z (D.next z i) <;>
    simp [he, hx, hy, state, Mark.plain, State.turn,State.bit]

section Family
variable {J : Type*} [Fintype J] {I F : J → Type*} {O : Type*}
  {L : (j : J) → I j → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (F j)]
  [Fintype O] [∀ j z, Fintype (L j z)]
  (D : (j : J) → IndexedFanData (I j) (F j) O (L j))
lemma family_natPaymentIndex_card : Nat.card (Σ j, (D j).PaymentIndex) = ∑ j, (D j).payments := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => (D j).paymentIndex_card)
end Family
end HyperbolicObstruction.FanLink.IndexedFanData
end
end

section

end
end

end OAI
