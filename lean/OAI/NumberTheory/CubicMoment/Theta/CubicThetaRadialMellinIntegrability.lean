import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAveragedHeat

namespace OAI

/-! Absolute convergence for the radial-test Mellin interchange. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaRadialMellinIntegrand (W : C_c(ℝ,ℂ)) (A : ℝ) (s : ℂ)
    (p : ℝ × ℝ) : ℂ :=
  star (W p.1)/(p.1:ℂ)^2*(p.2:ℂ)^(s-2)*cubicThetaLinearHeat p.1 A p.2

lemma cubicThetaRadialMellin_integrable (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A)
    (s : ℂ) :
    Integrable (cubicThetaRadialMellinIntegrand W A s)
      ((volume.restrict (Ioi (2:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hh := (cubicThetaDoubleHeat_mellinConvergent (by norm_num : (0:ℝ)<1) hA (s-1)).norm
  change IntegrableOn (fun u : ℝ => ‖(u:ℂ)^(s-1-1)*cubicThetaDoubleHeat 1 A u‖) (Ioi 0) at hh
  rw [show s-1-1=s-2 by ring] at hh
  have hm := (cubicThetaRadialWeight_integrable W).mul_prod hh
  rw [Measure.prod_restrict] at hm ⊢
  apply hm.mono' (by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaRadialMellinIntegrand cubicThetaLinearHeat
    fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  have hb := mul_le_mul_of_nonneg_left
    (cubicThetaLinearHeat_average_bound W hA hp.2 hp.1) (_root_.norm_nonneg ((p.2:ℂ)^(s-2)))
  simpa only [cubicThetaRadialMellinIntegrand,norm_mul,mul_comm,mul_left_comm,mul_assoc] using hb

end CubicFirstMoment

end

end OAI
