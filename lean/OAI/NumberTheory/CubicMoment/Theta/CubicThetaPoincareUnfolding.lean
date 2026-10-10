import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPoincarePairing
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Exact unfolding against compact periodized seeds, using the actual
measurable arithmetic fundamental domain and absolute integrability. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators CompactlySupported Pointwise
namespace CubicFirstMoment

lemma cubicThetaFundamental_translates_summable {f : CubicThetaPoint → ℂ}
    (hf : Integrable f cubicThetaPointMeasure) :
    Summable (fun g : cubicThetaPrincipalGroup => ∫ p in cubicThetaFundamentalDomain,
      ‖f (g • p)‖ ∂cubicThetaPointMeasure) := by
  have hD := cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure
  have hsum : Integrable f (Measure.sum (fun g : cubicThetaPrincipalGroup =>
      cubicThetaPointMeasure.restrict (g • cubicThetaFundamentalDomain))) := by
    rwa [hD.sum_restrict]
  apply hsum.summable_integral.congr
  intro g
  exact (measurePreserving_smul g cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul g) (fun p => ‖f p‖) cubicThetaFundamentalDomain

lemma cubicThetaFundamental_integral_tsum {f : CubicThetaPoint → ℂ}
    (hf : Integrable f cubicThetaPointMeasure) :
    (∫ p in cubicThetaFundamentalDomain, (∑' g : cubicThetaPrincipalGroup, f (g • p))
      ∂cubicThetaPointMeasure)=∫ p, f p ∂cubicThetaPointMeasure := by
  have hgi (g : cubicThetaPrincipalGroup) :
      IntegrableOn (fun p => f (g • p)) cubicThetaFundamentalDomain cubicThetaPointMeasure :=
    ((measurePreserving_smul g cubicThetaPointMeasure).integrable_comp_of_integrable hf).integrableOn
  calc
    _ = ∑' g : cubicThetaPrincipalGroup, ∫ p in cubicThetaFundamentalDomain,
        f (g • p) ∂cubicThetaPointMeasure :=
      (integral_tsum_of_summable_integral_norm hgi (cubicThetaFundamental_translates_summable hf)).symm
    _ = _ := (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).integral_eq_tsum'' f hf |>.symm

theorem cubicThetaPoincare_pairing_integral (ψ : C_c(CubicThetaPoint,ℂ)) (F : CubicThetaSection) :
    (∫ q, cubicThetaSectionPairing (cubicThetaPoincareSection ψ) F q ∂cubicThetaQuotientMeasure)=
      ∫ p, star (ψ p)*F.val p ∂cubicThetaPointMeasure := by
  have hf : Integrable (fun p => star (ψ p)*F.val p) cubicThetaPointMeasure :=
    (ψ.continuous.star.mul F.val.continuous).integrable_of_hasCompactSupport
      ((ψ.hasCompactSupport.comp_left (g:=star) (star_zero ℂ)).mul_right)
  rw [cubicThetaQuotientMeasure,
    integral_map_of_stronglyMeasurable cubicThetaQuotientMap_open.continuous.measurable
      (cubicThetaSectionPairing_continuous _ _).stronglyMeasurable]
  simp_rw [cubicThetaPoincare_pairing_point]
  exact cubicThetaFundamental_integral_tsum hf

end CubicFirstMoment

end

end OAI
