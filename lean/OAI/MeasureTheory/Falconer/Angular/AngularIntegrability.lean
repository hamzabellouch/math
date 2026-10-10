import OAI.MeasureTheory.Falconer.Fourier.FourierEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def sineKernel (v θ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (|Real.sin θ|))^(-v)

theorem sine_power_domination {v x : ℝ} (hv : 0 < v) (hx : |x| ≤ Real.pi/2) :
    ‖|Real.sin x|^(-v)‖ ≤ (2/Real.pi)^(-v) * |x|^(-v) := by
  by_cases hz : x = 0
  · subst x
    simp [Real.zero_rpow (neg_ne_zero.mpr hv.ne')]
  · have hxpos : 0 < |x| := abs_pos.mpr hz
    have hc : 0 < 2/Real.pi := by positivity
    have hs := Real.mul_abs_le_abs_sin hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    calc
      |Real.sin x|^(-v) ≤ ((2/Real.pi)*|x|)^(-v) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hc hxpos) hs (by linarith)
      _ = _ := Real.mul_rpow hc.le hxpos.le

theorem intervalIntegrable_sine_power {v : ℝ} (hv : 0 < v) (hv1 : v < 1)
    (a b : ℝ) : IntervalIntegrable (fun θ : ℝ => |Real.sin θ|^(-v)) volume a b := by
  have hi : IntegrableOn (fun θ : ℝ => |Real.sin θ|^(-v)) (ball 0 (Real.pi/2)) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp) (by simpa using hv1)
      (C := (2/Real.pi)^(-v))
    · filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx
      rw [mem_ball_zero_iff] at hx
      simpa only [Real.norm_eq_abs] using sine_power_domination hv hx.le
    · have hm : Measurable (fun θ : ℝ => |Real.sin θ|^(-v)) := by fun_prop
      exact hm.aestronglyMeasurable
  have hj : IntervalIntegrable (fun θ : ℝ => |Real.sin θ|^(-v)) volume
      (-Real.pi/2) (Real.pi/2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])]
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add, neg_div] using hi
  have hp : Function.Periodic (fun θ : ℝ => |Real.sin θ|^(-v)) Real.pi := by
    intro θ
    simp
  apply hp.intervalIntegrable Real.pi_ne_zero (t := -Real.pi/2) _ a b
  simpa only [show -Real.pi / 2 + Real.pi = Real.pi / 2 by ring] using hj

theorem sine_ne_zero_ae : ∀ᵐ θ : ℝ ∂volume, Real.sin θ ≠ 0 := by
  have he : {θ : ℝ | Real.sin θ = 0} = range (fun n : ℤ => (n : ℝ)*Real.pi) := by
    ext θ
    simp only [mem_ofPred_eq,mem_range,Real.sin_eq_zero_iff]
  rw [ae_iff]
  simp only [not_not]
  change volume {θ : ℝ | Real.sin θ = 0} = 0
  rw [he]
  exact (countable_range _).measure_zero volume

theorem sineKernel_lintegral_eq {v : ℝ} (hv : 0 < v) (hv1 : v < 1) (a b : ℝ) :
    (∫⁻ θ : ℝ in Ioc a b, sineKernel v θ) =
      ENNReal.ofReal (∫ θ : ℝ in Ioc a b, |Real.sin θ|^(-v)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_sine_power hv hv1 a b).1
    (Filter.Eventually.of_forall (fun θ => Real.rpow_nonneg (abs_nonneg _) _))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae sine_ne_zero_ae] with θ hθ
  exact ENNReal.ofReal_rpow_of_pos (abs_pos.mpr hθ)

theorem sineKernel_lintegral_lt_top {v : ℝ} (hv : 0 < v) (hv1 : v < 1) (a b : ℝ) :
    (∫⁻ θ : ℝ in Ioc a b, sineKernel v θ) < ∞ := by
  rw [sineKernel_lintegral_eq hv hv1]
  exact ENNReal.ofReal_lt_top

theorem one_le_sineKernel {v : ℝ} (hv : 0 ≤ v) (θ : ℝ) : 1 ≤ sineKernel v θ := by
  have hbase : ENNReal.ofReal |Real.sin θ| ≤ 1 := by
    exact ENNReal.ofReal_le_one.mpr (Real.abs_sin_le_one θ)
  simpa only [sineKernel,ENNReal.rpow_zero] using
    ENNReal.rpow_le_rpow_of_exponent_ge hbase (show -v ≤ 0 by linarith)

noncomputable def angularEnergyConstant (v : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), sineKernel v θ

theorem angularEnergyConstant_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < angularEnergyConstant v := by
  have h := lintegral_mono (μ := volume.restrict (Ioc 0 (2*Real.pi))) (one_le_sineKernel hv)
  simp only [lintegral_const,one_mul,Measure.restrict_apply MeasurableSet.univ,
    univ_inter,Real.volume_Ioc,sub_zero] at h
  exact (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).trans_le h

theorem angularEnergyConstant_lt_top {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    angularEnergyConstant v < ∞ := sineKernel_lintegral_lt_top hv hv1 _ _

theorem sine_shift_ne_zero_ae (c : ℝ) :
    ∀ᵐ θ : ℝ ∂volume, Real.sin (θ-c) ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  apply measure_mono_null (t := range (fun n : ℤ => (n : ℝ)*Real.pi+c))
  · intro θ hθ
    obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp hθ
    exact ⟨n,by linarith⟩
  · exact (countable_range _).measure_zero volume

theorem sineKernel_shift_integral {v : ℝ} (hv : 0 < v) (hv1 : v < 1) (c : ℝ) :
    (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), sineKernel v (θ-c)) = angularEnergyConstant v := by
  let f : ℝ → ℝ := fun θ => |Real.sin θ|^(-v)
  have hp : Function.Periodic f (2*Real.pi) := by intro θ; simp [f]
  have hi : IntervalIntegrable (fun θ => f (θ-c)) volume 0 (2*Real.pi) := by
    simpa only [f, neg_add_cancel, sub_add_cancel] using
      (intervalIntegrable_sine_power hv hv1 (-c) (2*Real.pi-c)).comp_sub_right c
  have hnon : ∀ θ, 0 ≤ f θ := fun θ => Real.rpow_nonneg (abs_nonneg _) _
  have he : (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), sineKernel v (θ-c)) =
      ENNReal.ofReal (∫ θ : ℝ in Ioc 0 (2*Real.pi), f (θ-c)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi.1 (Filter.Eventually.of_forall (fun θ => hnon (θ-c)))]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (sine_shift_ne_zero_ae c)] with θ hθ
    exact ENNReal.ofReal_rpow_of_pos (abs_pos.mpr hθ)
  rw [he,angularEnergyConstant,sineKernel_lintegral_eq hv hv1]
  congr 1
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi),
    intervalIntegral.integral_comp_sub_right]
  rw [zero_sub]
  change (∫ x in -c..2*Real.pi-c, f x) = ∫ x in Ioc 0 (2*Real.pi), f x
  rw [show 2*Real.pi-c = -c+2*Real.pi by ring,
    hp.intervalIntegral_add_eq (-c) 0,zero_add,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)]

end PlanarFalconer

end OAI
