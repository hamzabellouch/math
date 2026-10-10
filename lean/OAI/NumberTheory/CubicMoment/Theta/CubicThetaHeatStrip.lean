import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeatMoments

namespace OAI

/-! A fixed pair of real spectral parameters dominates every nonzero
heat mode in the intervening strip. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaDualHeat_norm_strip (v A a b : ℝ) {s : ℂ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) {t : ℝ} (ht : 0<t) :
    ‖cubicThetaDualHeat v s A t‖≤
      ‖cubicThetaDualHeat v (a:ℂ) A t‖+‖cubicThetaDualHeat v (b:ℂ) A t‖ := by
  have hp : t^(s.re-2)≤t^(a-2)+t^(b-2) := by
    rcases le_total 1 t with ht1 | ht1
    · exact (Real.rpow_le_rpow_of_exponent_le ht1 (sub_le_sub_right hb 2)).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))
    · exact (Real.rpow_le_rpow_of_exponent_ge ht ht1 (sub_le_sub_right ha 2)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
  rw [cubicThetaDualHeat_norm v s A ht,cubicThetaDualHeat_norm v (a:ℂ) A ht,
    cubicThetaDualHeat_norm v (b:ℂ) A ht]
  simp only [Complex.ofReal_re]
  calc
    _ ≤ (t^(a-2)+t^(b-2))*Real.exp (-v^2*t)*Real.exp (-A/t) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by ring

lemma cubicThetaNonzeroHeat_mass_strip {v A : ℝ} (hv : 0<v) (hA : 0<A)
    {a b : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b) :
    (∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s A t‖)≤
      (∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v (a:ℂ) A t‖)+
      (∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v (b:ℂ) A t‖) := by
  have hi := (cubicThetaNonzeroHeat_integrable hv hA (a:ℂ)).norm
  have hj := (cubicThetaNonzeroHeat_integrable hv hA (b:ℂ)).norm
  rw [←integral_add hi hj]
  apply integral_mono_ae (cubicThetaNonzeroHeat_integrable hv hA s).norm (hi.add hj)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cubicThetaDualHeat_norm_strip v A a b ha hb ht

end CubicFirstMoment

end

end OAI
