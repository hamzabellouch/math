import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTranslatedCuspStrip
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientMeasure

namespace OAI

/-! Integral Mobius changes of cusp descend to the actual principal
quotient and preserve its constructed hyperbolic measure. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrincipalConjugateEquiv (δ : SL(2,Eisenstein)) :
    cubicThetaPrincipalGroup ≃ cubicThetaPrincipalGroup where
  toFun := cubicThetaPrincipalConjugate δ
  invFun := cubicThetaPrincipalConjugate δ⁻¹
  left_inv g := by
    apply Subtype.ext
    simp [cubicThetaPrincipalConjugate,mul_assoc]
  right_inv g := by
    apply Subtype.ext
    simp [cubicThetaPrincipalConjugate,mul_assoc]

def cubicThetaIntegralQuotientMap (δ : SL(2,Eisenstein)) :
    CubicThetaQuotient → CubicThetaQuotient :=
  Quotient.map (fun p => δ • p) (by
    intro p q hpq
    obtain ⟨g,hg⟩ := hpq
    refine ⟨cubicThetaPrincipalConjugate δ⁻¹ g,?_⟩
    change (((δ⁻¹)⁻¹*g.val*δ⁻¹):SL(2,Eisenstein)) • (δ • q)=δ • p
    rw [inv_inv]
    simp only [←mul_smul,mul_assoc,inv_mul_cancel,mul_one]
    rw [mul_smul]
    exact congrArg (fun r => δ • r) hg)

lemma cubicThetaIntegralQuotientMap_apply (δ : SL(2,Eisenstein)) (p : CubicThetaPoint) :
    cubicThetaIntegralQuotientMap δ (cubicThetaQuotientMap p)=cubicThetaQuotientMap (δ • p) := rfl

lemma cubicThetaIntegralQuotientMap_comp (δ ε : SL(2,Eisenstein)) (q : CubicThetaQuotient) :
    cubicThetaIntegralQuotientMap δ (cubicThetaIntegralQuotientMap ε q)=
      cubicThetaIntegralQuotientMap (δ*ε) q := by
  induction q using Quotient.inductionOn with
  | h p =>
    change cubicThetaQuotientMap (δ • (ε • p))=cubicThetaQuotientMap ((δ*ε) • p)
    rw [mul_smul]

lemma cubicThetaIntegralQuotientMap_one (q : CubicThetaQuotient) :
    cubicThetaIntegralQuotientMap 1 q=q := by
  induction q using Quotient.inductionOn with
  | h p =>
    change cubicThetaQuotientMap ((1:SL(2,Eisenstein)) • p)=cubicThetaQuotientMap p
    rw [one_smul]

lemma cubicThetaIntegralQuotientMap_continuous (δ : SL(2,Eisenstein)) :
    Continuous (cubicThetaIntegralQuotientMap δ) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  exact cubicThetaQuotientMap_open.continuous.comp (continuous_const_smul δ)

def cubicThetaIntegralQuotientHomeomorph (δ : SL(2,Eisenstein)) :
    CubicThetaQuotient ≃ₜ CubicThetaQuotient where
  toFun := cubicThetaIntegralQuotientMap δ
  invFun := cubicThetaIntegralQuotientMap δ⁻¹
  left_inv q := by rw [cubicThetaIntegralQuotientMap_comp,inv_mul_cancel,cubicThetaIntegralQuotientMap_one]
  right_inv q := by rw [cubicThetaIntegralQuotientMap_comp,mul_inv_cancel,cubicThetaIntegralQuotientMap_one]
  continuous_toFun := cubicThetaIntegralQuotientMap_continuous δ
  continuous_invFun := cubicThetaIntegralQuotientMap_continuous δ⁻¹

lemma cubicThetaIntegralImage_fundamental (δ : SL(2,Eisenstein)) :
    IsFundamentalDomain cubicThetaPrincipalGroup
      ((fun p : CubicThetaPoint => δ • p) '' cubicThetaFundamentalDomain) cubicThetaPointMeasure := by
  apply (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul δ).toEquiv
    (measurePreserving_smul δ⁻¹ cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrincipalConjugateEquiv δ)
  intro g p
  change δ • ((δ⁻¹*g.val*δ) • p)=g.val • (δ • p)
  simp only [←mul_smul,mul_assoc,mul_inv_cancel_left]

theorem cubicThetaIntegralQuotient_measurePreserving (δ : SL(2,Eisenstein)) :
    MeasurePreserving (cubicThetaIntegralQuotientMap δ) cubicThetaQuotientMeasure
      cubicThetaQuotientMeasure := by
  refine ⟨(cubicThetaIntegralQuotientMap_continuous δ).measurable,?_⟩
  calc
    _ = ((cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain).map
        (fun p : CubicThetaPoint => δ • p)).map cubicThetaQuotientMap := by
      rw [cubicThetaQuotientMeasure,
        Measure.map_map (cubicThetaIntegralQuotientMap_continuous δ).measurable
          cubicThetaQuotientMap_open.continuous.measurable,
        Measure.map_map cubicThetaQuotientMap_open.continuous.measurable
          (measurable_const_smul δ)]
      rfl
    _ = (cubicThetaPointMeasure.restrict
        ((fun p : CubicThetaPoint => δ • p) '' cubicThetaFundamentalDomain)).map
        cubicThetaQuotientMap := by
      rw [cubicThetaSmul_map_restrict δ cubicThetaFundamentalDomain_measurable]
    _ = cubicThetaQuotientMeasure :=
      (cubicThetaQuotientMeasure_independent (cubicThetaIntegralImage_fundamental δ)).symm

end CubicFirstMoment

end

end OAI
