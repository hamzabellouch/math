import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1L2

namespace OAI

/-! The norm of compact C1 value-gradient data is the actual
hyperbolic mass-plus-gradient integral. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1EnergyData_norm_sq (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    ‖cubicThetaC1EnergyData F hF hc‖^2=
      ∫ q, cubicThetaSectionNorm F q^2+cubicThetaC1QuotientEnergy F q
        ∂cubicThetaQuotientMeasure := by
  let m := cubicThetaCompactSection_memLp F hc
  let g := cubicThetaC1Gradient_memLp F hF hc
  have hm : Integrable (fun q => ‖cubicThetaSectionRepresentative F q‖^2)
      cubicThetaQuotientMeasure := m.integrable_norm_pow (by norm_num)
  have hg : Integrable (fun q => ‖cubicThetaGradientRepresentative F q‖^2)
      cubicThetaQuotientMeasure := g.integrable_norm_pow (by norm_num)
  have hv : (∫ q, ‖m.toLp (cubicThetaSectionRepresentative F) q‖^2 ∂cubicThetaQuotientMeasure)=
      ∫ q, ‖cubicThetaSectionRepresentative F q‖^2 ∂cubicThetaQuotientMeasure := by
    apply integral_congr_ae
    filter_upwards [m.coeFn_toLp] with q hq
    rw [hq]
  have hd : (∫ q, ‖g.toLp (cubicThetaGradientRepresentative F) q‖^2 ∂cubicThetaQuotientMeasure)=
      ∫ q, ‖cubicThetaGradientRepresentative F q‖^2 ∂cubicThetaQuotientMeasure := by
    apply integral_congr_ae
    filter_upwards [g.coeFn_toLp] with q hq
    rw [hq]
  calc
    _ = ‖m.toLp (cubicThetaSectionRepresentative F)‖^2+
        ‖g.toLp (cubicThetaGradientRepresentative F)‖^2 :=
      WithLp.prod_norm_sq_eq_of_L2 _
    _ = (∫ q, ‖cubicThetaSectionRepresentative F q‖^2 ∂cubicThetaQuotientMeasure)+
        ∫ q, ‖cubicThetaGradientRepresentative F q‖^2 ∂cubicThetaQuotientMeasure := by
      rw [cubicTheta_l2_norm_sq_measure,cubicTheta_l2_norm_sq_measure,hv,hd]
    _ = _ := by
      rw [← integral_add hm hg]
      apply integral_congr_ae
      filter_upwards with q
      rw [cubicThetaSectionRepresentative_norm,cubicThetaC1Gradient_norm_sq F hF]

lemma cubicThetaC1EnergyData_smooth (F : cubicThetaSmoothTests) :
    cubicThetaC1EnergyData F (F.property.1.of_le (by simp)) F.property.2=
      cubicThetaGlobalEnergyGraph F := rfl

end CubicFirstMoment

end

end OAI
