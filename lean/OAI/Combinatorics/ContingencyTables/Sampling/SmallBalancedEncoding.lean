import OAI.Combinatorics.ContingencyTables.Sampling.SmallRepairWords
import OAI.Combinatorics.ContingencyTables.Transport.RawSmallChoiceProperties

namespace OAI

/-! # Every bounded balanced small profile has its literal word encoding -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open SmallContextEnumeration RowMajorEnumeration

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def balancedChoices (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (z : BoundedProfile small B) :
    Cells small → Fin (U+1) := fun a =>
  ⟨(z (a,false)).val,(z (a,false)).isLt.trans_le (by rw [hB _ _ a.property])⟩

omit [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J] in
lemma balancedChoices_profile (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (z : BoundedProfile small B)
    (hz : Balanced small B (naturalProfile z)) :
    rawChoice small U (balancedChoices small B U hB z)=naturalProfile z := by
  funext p
  rcases p with ⟨a,b⟩
  cases b
  · rfl
  · have h := hz a.val.1 a.val.2
    have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
    simp only [smallView,smallQ,a.property,dite_eq_left] at h
    rw [heta] at h
    dsimp only [naturalProfile] at h
    have hy := (z (a,true)).isLt
    have hb := hB _ _ a.property
    change U-(z (a,false)).val=(z (a,true)).val
    change (z (a,true)).val < B a.val.1 a.val.2+1 at hy
    omega

noncomputable def balancedWord (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (z : BoundedProfile small B) :
    Fin (Fintype.card (Cells small)) → Fin (U+1) :=
  (wordChoices small U).symm (balancedChoices small B U hB z)

lemma balancedWord_profile (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (z : BoundedProfile small B)
    (hz : Balanced small B (naturalProfile z)) :
    rawChoice small U (wordChoices small U (balancedWord small B U hB z))=naturalProfile z := by
  unfold balancedWord
  rw [Equiv.apply_symm_apply]
  exact balancedChoices_profile small B U hB z hz

end ContingencyTables.SmallGraphProfiles

end OAI
