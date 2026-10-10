import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GroupedTypes

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
variable {I : Type*} [Fintype I] [LinearOrder I]
  {X : I → Type*} [∀i,Fintype (X i)] {N : ℕ}

omit [LinearOrder I] in
theorem groupingCard (e : (Σi, X i) ≃ Fin N) :
    Fintype.card (Σₗ i, Fin (Fintype.card (X i)))=N := by
  change Fintype.card (Σi, Fin (Fintype.card (X i)))=N
  have he := Fintype.card_congr e
  simpa only [Fintype.card_sigma,Fintype.card_fin] using he

def groupingOrder (e : (Σi, X i) ≃ Fin N) :
    (Σₗ i, Fin (Fintype.card (X i))) ≃o Fin N :=
  (Fintype.orderIsoFinOfCardEq _ (groupingCard e)).symm

def groupingPerm (e : (Σi, X i) ≃ Fin N) : Equiv.Perm (Fin N) :=
  ((groupingOrder e).symm.toEquiv.trans ofLex).trans
    ((Equiv.sigmaCongrRight (fun i => (Fintype.equivFin (X i)).symm)).trans e)

lemma groupingPerm_apply (e : (Σi, X i) ≃ Fin N) (i : I) (a : Fin (Fintype.card (X i))) :
    groupingPerm e (groupingOrder e (toLex ⟨i,a⟩))=e ⟨i,(Fintype.equivFin (X i)).symm a⟩ := by
  simp [groupingPerm,Equiv.sigmaCongrRight]

@[simp] lemma groupingPerm_inv_apply (e : (Σi, X i) ≃ Fin N) (i : I) (x : X i) :
    (groupingPerm e)⁻¹ (e ⟨i,x⟩)=groupingOrder e (toLex ⟨i,Fintype.equivFin (X i) x⟩) := by
  apply (groupingPerm e).injective
  rw [groupingPerm_apply,Equiv.symm_apply_apply]
  exact (groupingPerm e).apply_symm_apply _

lemma grouping_groupOf (e : (Σi, X i) ≃ Fin N) (t : Fin N) :
    groupOf (groupingOrder e) (groupingPerm e) t=(e.symm t).1 := by
  simp [groupOf,groupingPerm,Equiv.sigmaCongrRight]

lemma grouping_permutation (e : (Σi, X i) ≃ Fin N)
    (a : ∀i, Equiv.Perm (X i)) :
    e.permCongr (Equiv.Perm.sigmaCongrRight a)=
      groupingPerm e*blockPerm (groupingOrder e)
        (fun i => (Fintype.equivFin (X i)).permCongr (a i))*(groupingPerm e)⁻¹ := by
  apply Equiv.ext
  intro t
  obtain ⟨⟨i,x⟩,rfl⟩ := e.surjective t
  simp only [Equiv.Perm.mul_apply,groupingPerm_inv_apply,blockPerm_apply,groupingPerm_apply,
    Equiv.permCongr_apply,Equiv.symm_apply_apply]
  rfl

end BinaryCoordinateSweeps.Signed

end

end OAI
