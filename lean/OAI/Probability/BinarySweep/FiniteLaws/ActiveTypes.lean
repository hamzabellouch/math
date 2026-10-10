import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungResolution
import OAI.Probability.BinarySweep.TensorBounds.SignedWhitening

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Matrix

namespace BinaryCoordinateSweeps
open Density Irrep Representation

lemma orthogonal_idempotents_independent {I X : Type*} [Fintype I] [Fintype X]
    (P : I → Matrix X X ℂ) (hp : ∀i, P i*P i=P i)
    (hz : ∀i j, i≠j → P i*P j=0) (hne : ∀i, P i≠0) :
    LinearIndependent ℂ P := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hh := congrArg (fun M => P i*M) hc
  rw [Matrix.mul_zero,Matrix.mul_sum] at hh
  have he : (∑j, P i*(c j • P j))=c i • P i := by
    rw [Finset.sum_eq_single i]
    · rw [Matrix.mul_smul,hp]
    · intro j _ hji; rw [Matrix.mul_smul,hz i j hji.symm,smul_zero]
    · simp
  rw [he] at hh
  exact (smul_eq_zero.mp hh).resolve_right (hne i)

namespace Signed
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

def typeProjection (p : A → Bool) (α : n.Partition) :=
  isotypicProjection p (Young.partitionHilbertRep α)

lemma typeProjection_linear (p : A → Bool) (α : n.Partition) :
    (typeProjection p α).toEuclideanLin=
      (isotypicSpan (Young.partitionHilbertRep α) (hilbertTensorRep p n)).starProjection.toLinearMap := by
  rw [hilbert_isotypic_eq]
  exact projectionMatrix_linear _

lemma typeProjection_idempotent (p : A → Bool) (α : n.Partition) :
    typeProjection p α*typeProjection p α=typeProjection p α := projectionMatrix_idempotent _

lemma typeProjection_orthogonal (p : A → Bool) (α β : n.Partition) (h : α≠β) :
    typeProjection p α*typeProjection p β=0 := by
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toLpLin_mul_same,map_zero,typeProjection_linear]
  apply LinearMap.ext
  intro v
  change (isotypicSpan (Young.partitionHilbertRep α) (hilbertTensorRep p n)).starProjection
    ((isotypicSpan (Young.partitionHilbertRep β) (hilbertTensorRep p n)).starProjection v)=0
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  apply isotypic_orthogonal (Young.partitionHilbertRep α) (Young.partitionHilbertRep β)
    (hilbertTensorRep p n) (Young.partitionHilbertRep_unitary α)
    (Young.partitionHilbertRep_unitary β) (hilbertTensorRep_unitary p)
    (fun ⟨e⟩ => h (Young.partitionHilbertRep_equiv_injective α β e))
  exact Submodule.starProjection_apply_mem _ _

abbrev ActiveType (p : A → Bool) (n : ℕ) := {α : n.Partition // typeProjection p α≠0}

lemma activeType_card (p : A → Bool) (n : ℕ) :
    Fintype.card (ActiveType p n) ≤ (n+1)^((Fintype.card A)^2) := by
  let P (α : ActiveType p n) : invariantSubspace p n :=
    ⟨typeProjection p α.val,isotypicProjection_invariant p _⟩
  have hi : LinearIndependent ℂ (fun α : ActiveType p n => typeProjection p α.val) :=
    orthogonal_idempotents_independent _ (fun α => typeProjection_idempotent p α.val)
      (fun α β h => typeProjection_orthogonal p α.val β.val (fun he => h (Subtype.ext he)))
      (fun α => α.property)
  have hP : LinearIndependent ℂ P := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    apply Fintype.linearIndependent_iff.mp hi c
    have hh := congrArg (fun v : invariantSubspace p n => v.val) hc
    simpa only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_zero,P] using hh
  exact hP.fintype_card_le_finrank.trans (invariantSubspace_finrank p n)

lemma all_typeProjection_sum (p : A → Bool) (n : ℕ) :
    (∑α : n.Partition, typeProjection p α)=1 := by
  apply Matrix.toEuclideanLin.injective
  simp only [map_sum,typeProjection_linear,Matrix.toLpLin_one]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sum_apply,ContinuousLinearMap.coe_coe,LinearMap.id_apply]
  exact Young.partition_projection_sum (hilbertTensorRep p n) (hilbertTensorRep_unitary p) v

theorem active_typeProjection_sum (p : A → Bool) (n : ℕ) :
    (∑α : ActiveType p n, typeProjection p α.val)=1 := by
  rw [← all_typeProjection_sum p n]
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun α : n.Partition => typeProjection p α≠0))
    (by simp) (fun α => typeProjection p α)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with h
  · rfl
  · exact (not_ne_iff.mp h).symm

end Signed
end BinaryCoordinateSweeps

end

end OAI
