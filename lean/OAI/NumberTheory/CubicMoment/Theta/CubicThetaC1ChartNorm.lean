import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1EnergyNorm
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaChartRestrictedIntegral

namespace OAI

/-! The full energy norm of a compact C1 section supported in an
injective chart equals its literal integral over that covering sheet. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1EnergyData_chart_norm (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F))
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source)
    (hs : tsupport (cubicThetaSectionNorm F)⊆cubicThetaQuotientMap '' S) :
    ‖cubicThetaC1EnergyData F hF hc‖^2=
      ∫ p in S, ‖F.val p‖^2+cubicThetaSectionEnergy F p ∂cubicThetaPointMeasure := by
  rw [cubicThetaC1EnergyData_norm_sq]
  have hz : ∀ q, q∉cubicThetaQuotientMap '' S →
      cubicThetaSectionNorm F q^2+cubicThetaC1QuotientEnergy F q=0 := by
    intro q hq
    have hout : q∉tsupport (cubicThetaSectionNorm F) := fun h => hq (hs h)
    have hn := image_eq_zero_of_notMem_tsupport hout
    have hp : cubicThetaQuotientMap (cubicThetaQuotientLift q)∉tsupport (cubicThetaSectionNorm F) := by
      rwa [cubicThetaQuotientLift_map]
    have hd := cubicThetaSectionDifferential_eq_zero F (cubicThetaQuotientLift q) hp
    simp only [hn,cubicThetaC1QuotientEnergy,cubicThetaSectionEnergy,hd,
      cubicThetaTangentEnergy,zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
      Finset.sum_const_zero,mul_zero,add_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hcont : Continuous (fun q => cubicThetaSectionNorm F q^2+cubicThetaC1QuotientEnergy F q) :=
    ((cubicThetaSectionNorm_continuous F).pow 2).add (cubicThetaC1QuotientEnergy_continuous F hF)
  rw [cubicThetaChart_integral e he hS hSe _ hcont.stronglyMeasurable]
  apply setIntegral_congr_fun hS
  intro p hp
  dsimp only
  rw [cubicThetaSectionNorm_apply,cubicThetaC1QuotientEnergy_apply F hF]

end CubicFirstMoment

end

end OAI
