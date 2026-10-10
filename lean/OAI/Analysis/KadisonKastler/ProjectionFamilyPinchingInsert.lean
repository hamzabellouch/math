import OAI.Analysis.KadisonKastler.ProjectionFamilyInsert

namespace OAI

/-! # Exact pinching refinement for an infinite family -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def projectionFamilySelectedPart (J : H ≃ₗᵢ⋆[ℂ] H) (S : Set (AlgebraProjection M)) : H →L[ℂ] H :=
  projectionFamilyPinching J S-modularQuadratic J (projectionFamilyRemainder S).val

theorem projectionFamilySelectedPart_isProjection
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) : IsStarProjection (projectionFamilySelectedPart J S) :=
  (modularQuadratic_projection J hJ hright (projectionFamilyRemainder S)).sub_of_mul_eq_right
    (projectionFamilyPinching_isProjection J S) (projectionFamilyPinching_quadratic J hJ hright S)

theorem projectionFamilySelectedPart_orthogonal
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) :
    projectionFamilySelectedPart J S*modularQuadratic J (projectionFamilyRemainder S).val=0 := by
  rw [projectionFamilySelectedPart,sub_mul,projectionFamilyPinching_quadratic J hJ hright,
    (modularQuadratic_projection J hJ hright (projectionFamilyRemainder S)).isIdempotentElem.eq,sub_self]

theorem projectionFamilyPinching_insert
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) (p : AlgebraProjection M)
    (hpq : p≤projectionFamilyRemainder S) :
    projectionFamilyPinching J (insert p S)=projectionFamilySelectedPart J S+
      refinedCornerProjection J (projectionFamilyRemainder S) p := by
  let q := projectionFamilyRemainder S
  let R := projectionFamilyPinching J S
  let A := projectionFamilySelectedPart J S
  let C := pairedProjectionCut p.val.val (conjugationOperator J p.val.val)
  let U := projectionFamilyPinching J (insert p S)
  have hA : IsStarProjection A := projectionFamilySelectedPart_isProjection J hJ hright S
  have hAQ : A*modularQuadratic J q.val=0 := projectionFamilySelectedPart_orthogonal J hJ hright S
  have hpa := projectionFamily_subprojection_mul_pinching J hJ hright S p hpq
  have hpA : p.val.val*A=0 := by
    change p.val.val*(R-modularQuadratic J q.val)=0
    rw [mul_sub,hpa.1,sub_self]
  have hjpA : conjugationOperator J p.val.val*A=0 := by
    change conjugationOperator J p.val.val*(R-modularQuadratic J q.val)=0
    rw [mul_sub,hpa.2,sub_self]
  have hCA : C*A=A := by
    have hj : (1-conjugationOperator J p.val.val)*A=A := by
      rw [sub_mul,one_mul,hjpA,sub_zero]
    have hp' : (1-p.val.val)*A=A := by rw [sub_mul,one_mul,hpA,sub_zero]
    change (p.val.val*conjugationOperator J p.val.val+
      (1-p.val.val)*(1-conjugationOperator J p.val.val))*A=A
    rw [add_mul,mul_assoc,hjpA,mul_zero,zero_add,mul_assoc,hj,hp']
  have hCR : C*R=A+refinedCornerProjection J q p := by
    have he : R=A+modularQuadratic J q.val := by dsimp only [A,projectionFamilySelectedPart,R,q]; abel
    rw [he,mul_add,hCA,refinedCornerProjection_mul_right J hJ hright q p hpq]
  have hCRp : IsStarProjection (C*R) := by
    rw [hCR]
    exact partialPinching_refinement_isProjection J hJ hright A hA q p hpq hAQ
  have hp := p.property.map M.toStarSubalgebra.subtype
  have hjp := (conjugateAlgebraProjection M M.commutant J hJ hright p).property.map
    M.commutant.toStarSubalgebra.subtype
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) p.val.val p.val.property
  have hCp : IsStarProjection C := pairedProjectionCut_isProjection hp hjp hcomm
  have hRp : IsStarProjection R := projectionFamilyPinching_isProjection J S
  have hRC : R*C=C*R := by
    have he := hCRp.isSelfAdjoint.star_eq
    simpa only [star_mul,hCp.isSelfAdjoint.star_eq,hRp.isSelfAdjoint.star_eq] using he
  have hUprod : U*(C*R)=C*R := by
    ext x
    change (projectionFamilyCommutationSpace J (insert p S)).toSubmodule.starProjection
      (C (R x))=C (R x)
    apply Submodule.starProjection_eq_self_iff.mpr
    change C (R x) ∈ projectionFamilyCommutationSpace J (insert p S)
    rw [mem_projectionFamilyCommutationSpace_insert]
    constructor
    · have he := congrArg (fun T : H →L[ℂ] H => T x) hRC
      change R (C x)=C (R x) at he
      rw [← he]
      exact Submodule.starProjection_apply_mem _ _
    · apply (pairedProjectionCut_fixed_iff hp hjp hcomm _).mp
      exact congrArg (fun T : H →L[ℂ] H => T (R x)) hCp.isIdempotentElem.eq
  have hprodU : (C*R)*U=U := by
    ext x
    have hx := (mem_projectionFamilyCommutationSpace_insert J S p _).mp
      (Submodule.starProjection_apply_mem (projectionFamilyCommutationSpace J (insert p S)).toSubmodule x)
    have hr : R (U x)=U x := Submodule.starProjection_eq_self_iff.mpr hx.1
    have hc : C (U x)=U x := (pairedProjectionCut_fixed_iff hp hjp hcomm _).mpr hx.2
    change C (R (U x))=U x
    rw [hr,hc]
  have hprodU' : (C*R)*U=C*R := by
    have he := congrArg star hUprod
    have hUp : IsStarProjection U := projectionFamilyPinching_isProjection J (insert p S)
    simpa only [star_mul,hCRp.isSelfAdjoint.star_eq,hUp.isSelfAdjoint.star_eq] using he
  exact hprodU.symm.trans (hprodU'.trans hCR)

end

end KadisonKastler

end OAI
