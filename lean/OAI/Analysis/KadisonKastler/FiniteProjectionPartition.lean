import OAI.Analysis.KadisonKastler.FinitePinchingApproximation

namespace OAI

/-! # Completing a finite orthogonal family to a partition of one -/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projection_le_familyRemainder (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (hp : ∀ q∈S, q.val*p.val=0) :
    p≤projectionFamilyRemainder S := by
  apply Subtype.ext
  ext x
  change (projectionFamilyRemainderSpace S).toSubmodule.starProjection (p.val.val x)=p.val.val x
  apply Submodule.starProjection_eq_self_iff.mpr
  change p.val.val x ∈ projectionFamilyRemainderSpace S
  rw [mem_projectionFamilyRemainderSpace]
  intro q hq
  exact congrArg (fun a : Algebra M => a.val x) (hp q hq)

theorem finite_family_partition_identities
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (F : Finset (AlgebraProjection M))
    (hF : (F : Set (AlgebraProjection M)).Pairwise (fun p q => p.val*q.val=0)) :
    (∑ p∈F, p.val)+(projectionFamilyRemainder (F : Set (AlgebraProjection M))).val=1 ∧
    projectionFamilyPinching J (F : Set (AlgebraProjection M))=
      (∑ p∈F, modularQuadratic J p.val)+
        modularQuadratic J (projectionFamilyRemainder (F : Set (AlgebraProjection M))).val := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.coe_empty,Finset.sum_empty,zero_add]
    rw [projectionFamilyRemainder_empty,projectionFamilyPinching_empty J,
      modularQuadratic_one J hJ]
    exact ⟨rfl,rfl⟩
  | @insert p F hp ih =>
    have hsub : (F : Set (AlgebraProjection M))⊆(↑(insert p F) : Set (AlgebraProjection M)) := by
      intro q hq
      exact Finset.mem_insert_of_mem hq
    obtain ⟨hs,hr⟩ := ih (hF.mono hsub)
    have hpq : p≤projectionFamilyRemainder (F : Set (AlgebraProjection M)) := by
      apply projection_le_familyRemainder
      intro q hq
      exact hF (hsub hq) (Finset.mem_insert_self p F) (by
        intro he
        subst q
        exact hp hq)
    have hrem := projectionFamilyRemainder_insert (F : Set (AlgebraProjection M)) p hpq
    have hpin := projectionFamilyPinching_insert J hJ hright (F : Set (AlgebraProjection M)) p hpq
    rw [Finset.coe_insert,Finset.sum_insert hp,Finset.sum_insert hp]
    constructor
    · rw [hrem]
      rw [← hs]
      abel
    · rw [hpin,projectionFamilySelectedPart,refinedCornerProjection,hr,hrem]
      abel

def finitePartitionProjection (F : Finset (AlgebraProjection M)) : Option F → AlgebraProjection M
  | none => projectionFamilyRemainder (F : Set (AlgebraProjection M))
  | some p => p.val

theorem finitePartitionProjection_sum
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (F : Finset (AlgebraProjection M))
    (hF : (F : Set (AlgebraProjection M)).Pairwise (fun p q => p.val*q.val=0)) :
    (∑ i, (finitePartitionProjection F i).val)=1 ∧
    (∑ i, modularQuadratic J (finitePartitionProjection F i).val)=
      projectionFamilyPinching J (F : Set (AlgebraProjection M)) := by
  classical
  obtain ⟨hs,hr⟩ := finite_family_partition_identities J hJ hright F hF
  simp only [Fintype.sum_option,finitePartitionProjection]
  rw [Finset.sum_coe_sort F (fun p => p.val),
    Finset.sum_coe_sort F (fun p => modularQuadratic J p.val)]
  exact ⟨(add_comm _ _).trans hs,(add_comm _ _).trans hr.symm⟩

theorem finitePartitionProjection_orthogonal (F : Finset (AlgebraProjection M))
    (hF : (F : Set (AlgebraProjection M)).Pairwise (fun p q => p.val*q.val=0)) :
    Pairwise (fun i j : Option F => (finitePartitionProjection F i).val*
      (finitePartitionProjection F j).val=0) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some p =>
      exact Subtype.ext (projectionFamily_right_annihilate _ p.val p.property)
  | some p =>
    cases j with
    | none => exact Subtype.ext (projectionFamily_left_annihilate _ p.val p.property)
    | some q =>
      exact hF p.property q.property (by
        intro he
        exact hij (congrArg (fun r : F => some r) (Subtype.ext he)))

end

end KadisonKastler

end OAI
