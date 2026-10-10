import OAI.Analysis.KadisonKastler.PositiveVectorPinching

namespace OAI

/-! # Energy gained by refining one two-sided corner

Splitting q into p and q-p removes exactly the p-commutator energy
inside qJq. These identities are the local step in Haagerup's
projection-family amplification argument.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def refinedCornerProjection (J : H ≃ₗᵢ⋆[ℂ] H) (q p : AlgebraProjection M) : H →L[ℂ] H :=
  modularQuadratic J p.val+modularQuadratic J (q.val-p.val)

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ hright in
theorem modularQuadratic_projection (p : AlgebraProjection M) :
    IsStarProjection (modularQuadratic J p.val) := by
  constructor
  · change modularQuadratic J p.val*modularQuadratic J p.val=modularQuadratic J p.val
    rw [modularQuadratic_mul J hJ hright,p.property.isIdempotentElem.eq]
  · change star (modularQuadratic J p.val)=modularQuadratic J p.val
    rw [modularQuadratic_star J hJ hright,p.property.isSelfAdjoint.star_eq]

include hJ in
theorem pairedProjectionCut_eq_quadratics (p : AlgebraProjection M) :
    pairedProjectionCut p.val.val (conjugationOperator J p.val.val)=
      modularQuadratic J p.val+modularQuadratic J (1-p.val) := by
  ext ξ
  exact positiveVectorPinch_eq J hJ p ξ

include hJ hright in
theorem refinedCornerProjection_mul_left (q p : AlgebraProjection M) (hpq : p ≤ q) :
    modularQuadratic J q.val*pairedProjectionCut p.val.val (conjugationOperator J p.val.val)=
      refinedCornerProjection J q p := by
  rw [pairedProjectionCut_eq_quadratics J hJ,mul_add,
    modularQuadratic_mul J hJ hright,modularQuadratic_mul J hJ hright,hpq,
    mul_sub,mul_one,hpq]
  rfl

include hJ hright in
theorem refinedCornerProjection_mul_right (q p : AlgebraProjection M) (hpq : p ≤ q) :
    pairedProjectionCut p.val.val (conjugationOperator J p.val.val)*modularQuadratic J q.val=
      refinedCornerProjection J q p := by
  rw [pairedProjectionCut_eq_quadratics J hJ,add_mul,
    modularQuadratic_mul J hJ hright,modularQuadratic_mul J hJ hright,
    projection_mul_of_le hpq,sub_mul,one_mul,projection_mul_of_le hpq]
  rfl

include hJ hright in
theorem refinedCornerProjection_isProjection (q p : AlgebraProjection M) (hpq : p ≤ q) :
    IsStarProjection (refinedCornerProjection J q p) := by
  have hc : Commute (modularQuadratic J q.val)
      (pairedProjectionCut p.val.val (conjugationOperator J p.val.val)) :=
    (refinedCornerProjection_mul_left J hJ hright q p hpq).trans
      (refinedCornerProjection_mul_right J hJ hright q p hpq).symm
  have hp := p.property.map M.toStarSubalgebra.subtype
  have hr := (conjugateAlgebraProjection M M.commutant J hJ hright p).property.map
    M.commutant.toStarSubalgebra.subtype
  have hpr := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) p.val.val p.val.property
  rw [← refinedCornerProjection_mul_left J hJ hright q p hpq]
  exact (modularQuadratic_projection J hJ hright q).mul
    (pairedProjectionCut_isProjection hp hr hpr) hc

include hJ hright in
theorem refinedCornerProjection_nested (q p : AlgebraProjection M) (hpq : p ≤ q) :
    refinedCornerProjection J q p*modularQuadratic J q.val=refinedCornerProjection J q p := by
  rw [← refinedCornerProjection_mul_right J hJ hright q p hpq,mul_assoc,
    (modularQuadratic_projection J hJ hright q).isIdempotentElem.eq]

include hJ hright in
theorem refinedCornerProjection_discarded_norm (q p : AlgebraProjection M) (hpq : p ≤ q) (ξ : H) :
    ‖(modularQuadratic J q.val-refinedCornerProjection J q p) ξ‖=
      ‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val ξ)‖ := by
  have hp := p.property.map M.toStarSubalgebra.subtype
  have hr := (conjugateAlgebraProjection M M.commutant J hJ hright p).property.map
    M.commutant.toStarSubalgebra.subtype
  have hpr := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) p.val.val p.val.property
  rw [← refinedCornerProjection_mul_right J hJ hright q p hpq]
  calc
    _ = ‖((1-pairedProjectionCut p.val.val (conjugationOperator J p.val.val))*
        modularQuadratic J q.val) ξ‖ := by rw [sub_mul,one_mul]
    _ = _ := pairedProjectionCut_discarded_norm hp hr hpr (modularQuadratic J q.val ξ)

include hJ hright in
theorem refinedCornerProjection_energy (q p : AlgebraProjection M) (hpq : p ≤ q) (ξ : H) :
    ‖refinedCornerProjection J q p ξ‖^2+
      ‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val ξ)‖^2=
        ‖modularQuadratic J q.val ξ‖^2 := by
  have he := nested_projection_norm_sq_eq
    (refinedCornerProjection_isProjection J hJ hright q p hpq)
    (refinedCornerProjection_nested J hJ hright q p hpq) ξ
  rwa [refinedCornerProjection_discarded_norm J hJ hright q p hpq] at he

end

end KadisonKastler

end OAI
