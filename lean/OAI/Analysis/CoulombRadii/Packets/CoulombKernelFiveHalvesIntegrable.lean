import Mathlib
import OAI.Analysis.CoulombRadii.Localization.TruncatedCoulomb

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma coulombKernel_fiveHalves_integrableOn (R : ℝ) :
    IntegrableOn (fun x : Space => coulombKernel x ^ (5/2:ℝ)) (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 5/2) (by simp) (by norm_num)
  · exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (coulombKernel_nonneg x) _)]
      simp [coulombKernel, Real.rpow_neg_eq_inv_rpow])
  · exact (coulombKernel_measurable.pow_const _).aestronglyMeasurable

lemma truncatedCoulomb_memLp (R : ℝ) :
    MemLp (truncatedCoulomb R) (ENNReal.ofReal (5/2:ℝ)) volume := by
  apply (integrable_norm_rpow_iff
    (coulombKernel_measurable.indicator measurableSet_ball).aestronglyMeasurable
    (by norm_num) (by simp)).mp
  have H := (coulombKernel_fiveHalves_integrableOn R).integrable_indicator measurableSet_ball
  apply H.congr
  filter_upwards [] with x
  by_cases hx : x ∈ Metric.ball (0:Space) R
  · simp [hx, Real.norm_of_nonneg (coulombKernel_nonneg x), ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤5/2)]
  · simp [hx, ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤5/2)]

lemma truncatedCoulomb_fiveHalves_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : Space, ‖truncatedCoulomb R x‖ ^ (5/2:ℝ)) =
      8*Real.pi*R^(1/2:ℝ) := by
  have he (x : Space) : ‖truncatedCoulomb R x‖ ^ (5/2:ℝ) =
      if ‖x‖ < R then ‖x‖ ^ (-(5/2:ℝ)) else 0 := by
    by_cases hx : ‖x‖ < R
    · simp [truncatedCoulomb, Metric.mem_ball, dist_zero_right, hx, coulombKernel,
        ← Real.rpow_neg_eq_inv_rpow]
    · simp [truncatedCoulomb, Metric.mem_ball, dist_zero_right, hx]
  simp_rw [he]
  rw [integral_fun_norm_addHaar (volume : Measure Space)
    (fun t : ℝ => if t < R then t ^ (-(5/2:ℝ)) else 0)]
  have hball : volume.real (Metric.ball (0 : Space) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  simp only [hdim, hball, nsmul_eq_mul, smul_eq_mul]
  have hint : (∫ t in Ioi (0:ℝ), t^(3-1) * (if t < R then t^(-(5/2:ℝ)) else 0)) =
      ∫ t in Ioo 0 R, t^(-(1/2:ℝ)) := by
    calc
      _ = ∫ t in Ioi (0:ℝ), (Iio R).indicator (fun u : ℝ => u^(-(1/2:ℝ))) t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change 0 < t at ht
        by_cases h : t < R
        · simp only [h, ite_true, Set.indicator, mem_Iio]
          rw [show (3:ℕ)-1=2 by norm_num, ← Real.rpow_natCast, ← Real.rpow_add ht]
          norm_num
        · simp [Set.indicator, h]
      _ = _ := by rw [integral_indicator measurableSet_Iio,
        Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio]
  rw [hint, setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hR,
    integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -(1/2:ℝ)))]
  norm_num
  ring

lemma coulomb_holder_exponents : (5/2:ℝ).HolderConjugate (5/3:ℝ) := by
  constructor <;> norm_num

lemma truncatedCoulomb_mul_integrable {f : Space → ℝ}
    (hf : MemLp f (ENNReal.ofReal (5/3:ℝ)) volume) (R : ℝ) (x : Space) :
    Integrable (fun y => truncatedCoulomb R (x-y)*f y) := by
  have hk := (truncatedCoulomb_memLp R).comp_measurePreserving
    (volume.measurePreserving_sub_left x)
  have : ENNReal.HolderConjugate (ENNReal.ofReal (5/2:ℝ))
      (ENNReal.ofReal (5/3:ℝ)) := by
    exact coulomb_holder_exponents.ennrealOfReal
  exact hk.integrable_mul hf

lemma coulomb_near_holder {f : Space → ℝ}
    (hf : MemLp f (ENNReal.ofReal (5/3:ℝ)) volume) {R : ℝ} (hR : 0 ≤ R) (x : Space) :
    (∫ y, truncatedCoulomb R (x-y)*‖f y‖) ≤
      (8*Real.pi*R^(1/2:ℝ))^(2/5:ℝ) * (∫ y, ‖f y‖^(5/3:ℝ))^(3/5:ℝ) := by
  have hk := (truncatedCoulomb_memLp R).comp_measurePreserving
    (volume.measurePreserving_sub_left x)
  have H := integral_mul_norm_le_Lp_mul_Lq coulomb_holder_exponents hk hf
  simp only [Function.comp_apply] at H
  rw [integral_sub_left_eq_self (fun z : Space => ‖truncatedCoulomb R z‖^(5/2:ℝ)) volume x,
    truncatedCoulomb_fiveHalves_integral hR] at H
  simpa only [Real.norm_of_nonneg (truncatedCoulomb_nonneg ..),
    show (1:ℝ)/(5/2)=2/5 by norm_num, show (1:ℝ)/(5/3)=3/5 by norm_num] using H
lemma coulomb_lp_integrand_bound {R : ℝ} (hR : 0 < R) (x y : Space) :
    coulombKernel (x-y) ≤ truncatedCoulomb R (x-y)+R⁻¹ := by
  by_cases h : x-y ∈ Metric.ball (0:Space) R
  · rw [truncatedCoulomb, Set.indicator_of_mem h]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hR.le)
  · rw [truncatedCoulomb, Set.indicator_of_notMem h, zero_add]
    have hn : R ≤ ‖x-y‖ := by simpa [Metric.mem_ball, dist_zero_right] using h
    exact inv_anti₀ hR hn

lemma coulomb_lp_convolution_integrable {f : Space → ℝ} (hf : Integrable f)
    (hfm : Measurable f) (hfp : MemLp f (ENNReal.ofReal (5/3:ℝ)) volume) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*f y) := by
  have hi := (truncatedCoulomb_mul_integrable hfp.norm 1 x).add hf.norm
  apply hi.mono'
    ((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).mul hfm).aestronglyMeasurable
  filter_upwards [] with y
  change ‖coulombKernel (x-y)*f y‖ ≤ truncatedCoulomb 1 (x-y)*‖f y‖+‖f y‖
  rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)]
  calc
    _ ≤ (truncatedCoulomb 1 (x-y)+1)*‖f y‖ :=
      mul_le_mul_of_nonneg_right (by simpa using coulomb_lp_integrand_bound (by norm_num : (0:ℝ)<1) x y)
        (norm_nonneg _)
    _ = _ := by ring

lemma coulomb_lp_convolution_bound {f : Space → ℝ} (hf : Integrable f)
    (hfm : Measurable f) (hfp : MemLp f (ENNReal.ofReal (5/3:ℝ)) volume)
    {R : ℝ} (hR : 0 < R) (x : Space) :
    (∫ y, coulombKernel (x-y)*‖f y‖) ≤
      (8*Real.pi*R^(1/2:ℝ))^(2/5:ℝ)*(∫ y, ‖f y‖^(5/3:ℝ))^(3/5:ℝ) +
      R⁻¹*(∫ y, ‖f y‖) := by
  have hi := truncatedCoulomb_mul_integrable hfp.norm R x
  calc
    _ ≤ ∫ y, truncatedCoulomb R (x-y)*‖f y‖ + R⁻¹*‖f y‖ :=
      integral_mono (coulomb_lp_convolution_integrable hf.norm hfm.norm hfp.norm x)
        (hi.add (hf.norm.const_mul _)) (fun y => by
          simpa only [add_mul] using
            mul_le_mul_of_nonneg_right (coulomb_lp_integrand_bound hR x y) (norm_nonneg (f y)))
    _ = (∫ y, truncatedCoulomb R (x-y)*‖f y‖) + R⁻¹*(∫ y, ‖f y‖) := by
      rw [integral_add hi (hf.norm.const_mul _), integral_const_mul]
    _ ≤ _ := add_le_add (coulomb_near_holder hfp hR.le x) le_rfl

lemma coulomb_lp_pair_integrable {f g : Space → ℝ} (hf : Integrable f) (hfm : Measurable f)
    (hg : Integrable g) (hgm : Measurable g)
    (hgp : MemLp g (ENNReal.ofReal (5/3:ℝ)) volume) :
    Integrable (fun p : Space × Space => f p.1*g p.2*coulombKernel (p.1-p.2)) := by
  have hm : Measurable (fun p : Space × Space => f p.1*g p.2*coulombKernel (p.1-p.2)) :=
    ((hfm.comp measurable_fst).mul (hgm.comp measurable_snd)).mul
      (coulombKernel_measurable.comp (measurable_fst.sub measurable_snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply ae_of_all
    intro x
    have hi := (coulomb_lp_convolution_integrable hg hgm hgp x).const_mul (f x)
    exact hi.congr (ae_of_all _ (fun y => by dsimp only; ring))
  · let A : ℝ := (8*Real.pi)^(2/5:ℝ)*(∫ y, ‖g y‖^(5/3:ℝ))^(3/5:ℝ) + ∫ y, ‖g y‖
    have hb (x : Space) : (∫ y, coulombKernel (x-y)*‖g y‖) ≤ A := by
      simpa [A] using coulomb_lp_convolution_bound hg hgm hgp (by norm_num : (0:ℝ)<1) x
    have he (x : Space) : (∫ y, ‖f x*g y*coulombKernel (x-y)‖) =
        ‖f x‖*(∫ y, coulombKernel (x-y)*‖g y‖) := by
      simp_rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)]
      simp_rw [mul_assoc, mul_comm ‖g _‖ (coulombKernel _)]
      rw [integral_const_mul]
    apply (hf.norm.mul_const A).mono' hm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [] with x
    change ‖∫ y, ‖f x*g y*coulombKernel (x-y)‖‖ ≤ ‖f x‖*A
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _)), he]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
