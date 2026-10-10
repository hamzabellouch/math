import OAI.NumberTheory.Ostmann.Conclusion.LowLevelBadPairs

namespace OAI

noncomputable section
namespace Ostmann.Conclusion

theorem inverse_rightComponent_eq_of_overlap {r m : ℕ}
    (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m) {a b : Fin r}
    (h : overlapRelation σ a b) :
    rightComponent σ.symm hm a=rightComponent σ.symm hm b := by
  obtain ⟨u,v,huv⟩ := h
  have ha := slot_component σ.symm hm (σ (a,u))
  have hb := slot_component σ.symm hm (σ (b,v))
  simp only [Equiv.symm_apply_apply] at ha hb
  exact ha.symm.trans ((congrArg (leftComponent σ.symm) huv).trans hb)

def inverseOverlapMap {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m) :
    OverlapComponent σ → OverlapComponent σ.symm :=
  Quotient.lift (rightComponent σ.symm hm) (by
    intro a b h
    induction h with
    | rel a b h => exact inverse_rightComponent_eq_of_overlap σ hm h
    | refl a => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂)

theorem inverseOverlapMap_surjective {r m : ℕ}
    (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m) :
    Function.Surjective (inverseOverlapMap σ hm) := by
  intro c
  obtain ⟨b,rfl⟩ := leftComponent_surjective σ.symm c
  refine ⟨leftComponent σ (σ.symm (b,⟨0,hm⟩)).1,?_⟩
  exact (slot_component σ.symm hm (b,⟨0,hm⟩)).symm

theorem overlapComponent_card_symm {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) :
    Fintype.card (OverlapComponent σ.symm)=Fintype.card (OverlapComponent σ) := by
  by_cases hm : 0 < m
  · apply Nat.le_antisymm
    · exact Fintype.card_le_of_surjective _ (inverseOverlapMap_surjective σ hm)
    · simpa only [Equiv.symm_symm] using
        Fintype.card_le_of_surjective _ (inverseOverlapMap_surjective σ.symm hm)
  · have hm0 : m=0 := by omega
    subst m
    have he : σ.symm=σ := Subsingleton.elim _ _
    rw [he]

@[simp] theorem badArrangement_symm_iff {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) :
    BadArrangement σ.symm ↔ BadArrangement σ := by
  simp only [BadArrangement,overlapComponent_card_symm]

@[simp] theorem transferBadArrangement_symm_iff {r m : ℕ}
    (σ : Equiv.Perm (Fin r × Fin m)) :
    TransferBadArrangement σ.symm ↔ TransferBadArrangement σ := by
  simp only [TransferBadArrangement,badArrangement_symm_iff]

end Ostmann.Conclusion

end

end OAI
