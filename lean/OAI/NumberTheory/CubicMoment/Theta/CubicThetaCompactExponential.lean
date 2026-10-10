import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointMeasureLocallyFinite
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Exponential

namespace OAI

/-! Entire dependence of the compact incoming correction. Only an
integrable amplitude and a bounded continuous real exponent are needed. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

lemma cubicThetaCompactExponential_differentiable {K : Set CubicThetaPoint}
    (hK : IsCompact K) (a : CubicThetaPoint → ℂ)
    (ha : IntegrableOn a K cubicThetaPointMeasure)
    (b : CubicThetaPoint → ℝ) (hb : ContinuousOn b K) :
    Differentiable ℂ (fun s : ℂ =>
      ∫ p in K,a p*Complex.exp (s*(b p:ℂ)) ∂cubicThetaPointMeasure) := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hb
  let M := max C 0
  have hM : 0≤M := le_max_right _ _
  have hbM (p : CubicThetaPoint) (hp : p∈K) : |b p|≤M :=
    (hC p hp).trans (le_max_left _ _)
  intro s
  let H := Real.exp ((‖s‖+1)*M)
  have hH : 0<H := Real.exp_pos _
  let F : ℂ → CubicThetaPoint → ℂ := fun z p => a p*Complex.exp (z*(b p:ℂ))
  let F' : ℂ → CubicThetaPoint → ℂ := fun z p => a p*(Complex.exp (z*(b p:ℂ))*(b p:ℂ))
  have hm (z : ℂ) : AEStronglyMeasurable (F z) (cubicThetaPointMeasure.restrict K) := by
    apply ha.aestronglyMeasurable.mul
    exact (Complex.continuous_exp.comp_continuousOn
      (continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hb))).aestronglyMeasurable hK.measurableSet
  have hm' : AEStronglyMeasurable (F' s) (cubicThetaPointMeasure.restrict K) := by
    apply ha.aestronglyMeasurable.mul
    apply ContinuousOn.aestronglyMeasurable _ hK.measurableSet
    exact (Complex.continuous_exp.comp_continuousOn
      (continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hb))).mul
        (Complex.continuous_ofReal.comp_continuousOn hb)
  have he (z : ℂ) (hz : ‖z‖≤‖s‖+1) (p : CubicThetaPoint) (hp : p∈K) :
      ‖Complex.exp (z*(b p:ℂ))‖≤H := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul hz (hbM p hp) (abs_nonneg _) (by positivity)
  have hi : Integrable (F s) (cubicThetaPointMeasure.restrict K) := by
    apply (ha.norm.mul_const H).mono' (hm s)
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (he s (by linarith) p hp) (_root_.norm_nonneg _)
  have hd : ∀ᵐ p ∂cubicThetaPointMeasure.restrict K,∀ z∈Metric.ball s 1,
      HasDerivAt (fun w => F w p) (F' z p) z := by
    filter_upwards with p z _
    simpa only [F,F',id_eq,one_mul] using
      (((hasDerivAt_id z).mul_const (b p:ℂ)).cexp.const_mul (a p))
  have hbound : ∀ᵐ p ∂cubicThetaPointMeasure.restrict K,∀ z∈Metric.ball s 1,
      ‖F' z p‖≤‖a p‖*(H*M) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp z hz
    have hz' : ‖z‖≤‖s‖+1 := by
      have ht := norm_le_norm_add_norm_sub s z
      rw [Metric.mem_ball,dist_eq_norm] at hz
      rw [norm_sub_rev s z] at ht
      linarith
    dsimp only [F']
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
    exact mul_le_mul (he z hz' p hp) (hbM p hp) (abs_nonneg _) hH.le
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s zero_lt_one) (Eventually.of_forall hm) hi hm' hbound
    (ha.norm.mul_const (H*M)) hd).2.differentiableAt

end CubicFirstMoment

end

end OAI
