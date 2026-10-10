import Mathlib
import OAI.Geometry.HyperbolicGroups.IndexedFanCounts
import OAI.Geometry.HyperbolicGroups.IndexedFanCards

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink.IndexedFanData
attribute [local instance] Classical.propDecidable
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

lemma multiplicity_le_card (a : O) : D.multiplicity a ≤ Fintype.card F := by
  exact Fintype.card_subtype_le _
lemma maxMultiplicity_le_card : D.maxMultiplicity ≤ Fintype.card F := by
  apply Finset.sup_le
  intro a _
  exact D.multiplicity_le_card a

/-- A positive-weight nominal fan is supported either by a selected top slot
or by a selected fan triangle. This includes slots omitted by a top boundary. -/
lemma activation_bound (h : 0 < D.weight) : 1 ≤ Fintype.card F + D.triangles := by
  by_cases hf : 0 < Fintype.card F
  · omega
  have hf0 : Fintype.card F = 0 := by omega
  have hm := D.maxMultiplicity_le_card
  have hi : 0 < Fintype.card I := by
    unfold weight at h
    omega
  obtain ⟨z⟩ := Fintype.card_pos_iff.mp hi
  obtain ⟨x,hx⟩ := D.represented z
  have hx' : D.mark z x = .triangle := by
    cases he : D.mark z x with
    | absent => exact False.elim (hx he)
    | triangle => rfl
    | top f => exact False.elim ((Fintype.card_eq_zero_iff.mp hf0).false f)
  have ht : 0 < Fintype.card D.TriangleIndex := Fintype.card_pos_iff.mpr ⟨⟨⟨z,x⟩,hx'⟩⟩
  rw [D.triangleIndex_card] at ht
  omega

end HyperbolicObstruction.FanLink.IndexedFanData
end
end

section

end
end

end OAI
