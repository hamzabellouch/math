import OAI.Analysis.KadisonKastler.PositiveMatrixAveraging
import OAI.Analysis.KadisonKastler.ProjectionCommutatorEnergy

namespace OAI

/-! # Pinching positive vectors directly in the original representation

The matching two-sided cut preserves the positive cone and faithfulness,
centralizes the chosen projection, and has exactly the original
left-right projection gap as its displacement.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positivePinchRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem pairedProjectionCut_intertwines {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) :
    p * pairedProjectionCut p q = q * pairedProjectionCut p q := by
  have hl : p * pairedProjectionCut p q = p*q := by
    simp only [pairedProjectionCut,mul_add,← mul_assoc,hp.isIdempotentElem.eq,
      hp.mul_one_sub_self,zero_mul,add_zero]
  have hr : q * pairedProjectionCut p q = p*q := by
    have hs := (Commute.one_left q).sub_left hc
    simp only [pairedProjectionCut,mul_add,← mul_assoc]
    rw [← hc.eq,mul_assoc,hq.isIdempotentElem.eq,← hs.eq,mul_assoc,
      hq.mul_one_sub_self,mul_zero,add_zero]
  exact hl.trans hr.symm

def positiveVectorPinch (J : H ≃ₗᵢ⋆[ℂ] H) (p : AlgebraProjection M) (η : H) : H :=
  pairedProjectionCut p.val.val (conjugationOperator J p.val.val) η

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ in
theorem positiveVectorPinch_eq (p : AlgebraProjection M) (η : H) :
    positiveVectorPinch J p η = modularQuadratic J p.val η +
      modularQuadratic J (1-p.val) η := by
  change (p.val.val * conjugationOperator J p.val.val +
      (1-p.val.val) * (1-conjugationOperator J p.val.val)) η = _
  have he : conjugationOperator J (1-p.val).val = 1-conjugationOperator J p.val.val := by
    change conjugationOperator J (1-p.val.val) = _
    rw [conjugationOperator_sub,conjugationOperator_one J hJ]
  rw [add_apply]
  simp only [modularQuadratic,he]
  rfl

include hJ hright in
theorem positiveVectorPinch_norm_sub (p : AlgebraProjection M) (η : H) :
    ‖positiveVectorPinch J p η - η‖ =
      ‖p.val.val η - conjugationOperator J p.val.val η‖ := by
  have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  have hq : IsStarProjection (conjugationOperator J p.val.val) := by
    constructor
    · rw [IsIdempotentElem,← conjugationOperator_mul J hJ,hp.isIdempotentElem.eq]
    · rw [IsSelfAdjoint,← conjugationOperator_star J hJ,hp.isSelfAdjoint.star_eq]
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) p.val.val p.val.property
  have he := pairedProjectionCut_discarded_norm hp hq hc η
  change ‖η - positiveVectorPinch J p η‖ = _ at he
  rw [norm_sub_rev] at he
  exact he

include hJ hright in
theorem positiveVectorPinch_centralizes_projection (p : AlgebraProjection M) (η : H) :
    p.val.val (positiveVectorPinch J p η) =
      conjugationOperator J p.val.val (positiveVectorPinch J p η) := by
  have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  have hq : IsStarProjection (conjugationOperator J p.val.val) := by
    constructor
    · rw [IsIdempotentElem,← conjugationOperator_mul J hJ,hp.isIdempotentElem.eq]
    · rw [IsSelfAdjoint,← conjugationOperator_star J hJ,hp.isSelfAdjoint.star_eq]
  exact congrArg (fun T : H →L[ℂ] H => T η)
    (pairedProjectionCut_intertwines hp hq
      (VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) p.val.val p.val.property))

include hJ hright in
theorem positiveVectorPinch_mem_cone (ξ : H) (p : AlgebraProjection M) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    positiveVectorPinch J p η ∈ modularPositiveCone (M := M) J ξ := by
  rw [positiveVectorPinch_eq J hJ]
  exact (modularPositiveCone J ξ).add_mem
    (modularQuadratic_preserves_positiveCone J hJ hright ξ p.val hη)
    (modularQuadratic_preserves_positiveCone J hJ hright ξ (1-p.val) hη)

include hJ hright in
theorem positiveVectorPinch_separating (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (p : AlgebraProjection M) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hs : Function.Injective (algebraVectorMap M η)) :
    Function.Injective (algebraVectorMap M (positiveVectorPinch J p η)) := by
  have hkill (q : AlgebraProjection M) (hq : q.val.val (positiveVectorPinch J p η) = 0) :
      q.val = 0 := by
    rw [positiveVectorPinch_eq J hJ] at hq
    have hh := positiveCone_projection_kills_summands J hJ hright ξ hξ hpos
      (modularQuadratic_preserves_positiveCone J hJ hright ξ p.val hη)
      (modularQuadratic_preserves_positiveCone J hJ hright ξ (1-p.val) hη) q hq
    have hp := positiveCone_projection_kills_quadratic J hJ hright ξ hξ hpos hη q p.val hh.1
    have hp' := positiveCone_projection_kills_quadratic J hJ hright ξ hξ hpos hη q (1-p.val) hh.2
    have hzero : q.val.val η = 0 := by
      have he : p.val.val η + (1-p.val).val η = η := by
        change p.val.val η + (η-p.val.val η) = η
        abel
      rw [← he,map_add,hp,hp',add_zero]
    exact hs (hzero.trans (map_zero (algebraVectorMap M η)).symm)
  let ζ := positiveVectorPinch J p η
  let q := vectorSupportProjection M ζ
  let r : AlgebraProjection M := ⟨1-q.val,q.property.one_sub⟩
  have hr : r.val.val ζ = 0 := by
    change ζ-q.val.val ζ = 0
    rw [vectorSupportProjection_apply,sub_self]
  have hq : q.val = 1 := (sub_eq_zero.mp (hkill r hr)).symm
  intro a b hab
  have hm := mul_vectorSupport_eq_zero M ζ (a-b) (sub_eq_zero.mpr hab)
  change (a-b).val * q.val.val = 0 at hm
  rw [hq,OneMemClass.coe_one,mul_one] at hm
  exact sub_eq_zero.mp (Subtype.ext hm)

end

end KadisonKastler

end OAI
