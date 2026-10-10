import OAI.Analysis.KadisonKastler.ProjectionFamilyCorner

namespace OAI

/-! # Adding a projection from the remaining corner -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem pairedProjectionCut_fixed_iff {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) (x : H) :
    pairedProjectionCut p q x=x ↔ p x=q x := by
  have hn := pairedProjectionCut_discarded_norm hp hq hc x
  constructor
  · intro he
    have hz : (1-pairedProjectionCut p q) x=0 := by
      change x-pairedProjectionCut p q x=0
      rw [he,sub_self]
    rw [hz,norm_zero] at hn
    exact sub_eq_zero.mp (norm_eq_zero.mp hn.symm)
  · intro he
    have hz : (p-q) x=0 := sub_eq_zero.mpr he
    rw [hz,norm_zero] at hn
    have hh := norm_eq_zero.mp hn
    change x-pairedProjectionCut p q x=0 at hh
    exact (sub_eq_zero.mp hh).symm

theorem projectionFamily_conjugate_remainder_mul_pinching
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) :
    conjugationOperator J (projectionFamilyRemainder S).val.val*projectionFamilyPinching J S=
      modularQuadratic J (projectionFamilyRemainder S).val := by
  ext x
  have hx : projectionFamilyPinching J S x ∈ projectionFamilyCommutationSpace J S :=
    Submodule.starProjection_apply_mem _ _
  have he := projectionFamily_remainder_central J hJ hright S hx
  exact he.symm.trans (congrArg (fun T : H →L[ℂ] H => T x)
    (projectionFamily_remainder_mul_pinching J hJ hright S))

theorem projectionFamily_subprojection_mul_pinching
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) (p : AlgebraProjection M)
    (hpq : p≤projectionFamilyRemainder S) :
    p.val.val*projectionFamilyPinching J S=
      p.val.val*modularQuadratic J (projectionFamilyRemainder S).val ∧
    conjugationOperator J p.val.val*projectionFamilyPinching J S=
      conjugationOperator J p.val.val*modularQuadratic J (projectionFamilyRemainder S).val := by
  let q := projectionFamilyRemainder S
  let R := projectionFamilyPinching J S
  let Q := modularQuadratic J q.val
  have hp : p.val.val*q.val.val=p.val.val := congrArg Subtype.val (projection_mul_of_le hpq)
  have hrightq : conjugationOperator J q.val.val*R=Q :=
    projectionFamily_conjugate_remainder_mul_pinching J hJ hright S
  have hp' : conjugationOperator J p.val.val*conjugationOperator J q.val.val=
      conjugationOperator J p.val.val := by
    rw [← conjugationOperator_mul J hJ,hp]
  constructor
  · change p.val.val*R=p.val.val*Q
    calc
      _ = (p.val.val*q.val.val)*R := by rw [hp]
      _ = _ := by rw [mul_assoc,projectionFamily_remainder_mul_pinching J hJ hright S]
  · change conjugationOperator J p.val.val*R=conjugationOperator J p.val.val*Q
    calc
      _ = (conjugationOperator J p.val.val*conjugationOperator J q.val.val)*R := by rw [hp']
      _ = _ := by rw [mul_assoc,hrightq]

end

end KadisonKastler

end OAI
