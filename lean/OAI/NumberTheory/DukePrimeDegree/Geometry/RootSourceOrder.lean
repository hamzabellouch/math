import OAI.NumberTheory.DukePrimeDegree.Geometry.CanonicalRootBasic
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! # A root graph without two consecutive edges admits a source ordering -/

noncomputable section
open Set
namespace DukePrimeDegree

/-- Put targets before sources. This is the only finite ordering fact needed
when the commutator theorem rules out two consecutive positive roots. -/
theorem exists_source_order (n : ℕ) (r : Fin n → Fin n → Prop)
    (hchain : ∀ a b c, r a b → r b c → False) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, r i j → e j < e i := by
  classical
  let S : Set (Fin n) := {i | ∃ j, r i j}
  let F : Fin n ≃ ((Sᶜ : Set (Fin n)) ⊕ S) :=
    (Equiv.Set.sumCompl S).symm.trans (Equiv.sumComm _ _)
  let E : ((Sᶜ : Set (Fin n)) ⊕ S) ≃
      Fin (Fintype.card (Sᶜ : Set (Fin n)) + Fintype.card S) :=
    (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finSumFinEquiv
  have hc : Fintype.card (Sᶜ : Set (Fin n)) + Fintype.card S=n := by
    simpa only [Fintype.card_fin,Fintype.card_sum] using (Fintype.card_congr F).symm
  let e : Equiv.Perm (Fin n) := F.trans (E.trans (finCongr hc))
  refine ⟨e,?_⟩
  intro i j hij
  have hi : i ∈ S := ⟨j,hij⟩
  have hj : j ∉ S := by
    rintro ⟨k,hjk⟩
    exact hchain i j k hij hjk
  have hFi : F i = Sum.inr (⟨i,hi⟩ : S) := by
    change Sum.swap ((Equiv.Set.sumCompl S).symm i) = _
    rw [Equiv.Set.sumCompl_symm_apply_of_mem hi]
    rfl
  have hFj : F j = Sum.inl (⟨j,hj⟩ : (Sᶜ : Set (Fin n))) := by
    change Sum.swap ((Equiv.Set.sumCompl S).symm j) = _
    rw [Equiv.Set.sumCompl_symm_apply_of_notMem hj]
    rfl
  have hei : (e i).val = Fintype.card (Sᶜ : Set (Fin n)) +
      (Fintype.equivFin S ⟨i,hi⟩).val := by
    change (finCongr hc (E (F i))).val = _
    rw [hFi]
    rfl
  have hej : (e j).val = (Fintype.equivFin (Sᶜ : Set (Fin n)) ⟨j,hj⟩).val := by
    change (finCongr hc (E (F j))).val = _
    rw [hFj]
    rfl
  change (e j).val < (e i).val
  rw [hei,hej]
  exact (Fintype.equivFin (Sᶜ : Set (Fin n)) ⟨j,hj⟩).isLt.trans_le (Nat.le_add_right _ _)

end DukePrimeDegree

end

end OAI
