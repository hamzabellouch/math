import OAI.Analysis.CircleDomains.Probability.OpenLineImageMeasure
import OAI.Analysis.CircleDomains.Sobolev.SmoothCutoffLinePayment
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! The image length of a smooth function on an arbitrary open subset
of a line is bounded by its actual derivative integral. The domain may
have countably many interval components. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_open_image_measure_le {U : Set ℝ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hi : IntegrableOn (fun x => |deriv f x|) U volume) :
    volume (f '' U) ≤ ENNReal.ofReal (∫ x in U, |deriv f x|) := by
  let g := U.indicator (fun x => |deriv f x|)
  have hg : Integrable g volume := (integrable_indicator_iff hU.measurableSet).mpr hi
  have hg0 (x : ℝ) : 0 ≤ g x := indicator_nonneg (fun _ _ => abs_nonneg _) _
  let κ := volume.withDensity (fun x => ENNReal.ofReal (g x))
  let : IsFiniteMeasure κ := ⟨by
    change volume.withDensity (fun x => ENNReal.ofReal (g x)) univ < ∞
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg0)]
    exact ENNReal.ofReal_lt_top⟩
  have hκ {S : Set ℝ} (hS : MeasurableSet S) (hSU : S ⊆ U) :
      κ S = ENNReal.ofReal (∫ x in S, |deriv f x|) := by
    rw [withDensity_apply _ hS,← ofReal_integral_eq_lintegral_ofReal hg.restrict
      (ae_restrict_of_ae (Eventually.of_forall hg0))]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS] with x hx
    exact indicator_of_mem (hSU hx) _
  rw [← hκ hU.measurableSet Subset.rfl]
  apply open_line_image_measure_le κ hU f
  intro x hx y hy hxy hI
  have hd : ContinuousOn (deriv f) U := by
    have h := (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply (continuousOn_const (c := (1 : ℝ)))
    simpa only [fderiv_apply_one_eq_deriv] using h
  have hint : IntervalIntegrable (deriv f) volume x y :=
    (hd.mono (by simpa only [uIcc_of_le hxy] using hI)).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => ((hf.contDiffAt (hU.mem_nhds (hI (by simpa only [uIcc_of_le hxy] using ht)))).differentiableAt
      (by norm_num)).hasDerivAt) hint
  calc
    |f y-f x| = ‖∫ t in x..y, deriv f t‖ := by rw [he,Real.norm_eq_abs]
    _ ≤ ∫ t in x..y, ‖deriv f t‖ := intervalIntegral.norm_integral_le_integral_norm hxy
    _ = ∫ t in Icc x y, |deriv f t| := by
      rw [intervalIntegral.integral_of_le hxy,← integral_Icc_eq_integral_Ioc]
      simp only [Real.norm_eq_abs]
    _ = κ.real (Icc x y) := by
      rw [measureReal_def,hκ measurableSet_Icc hI,ENNReal.toReal_ofReal]
      exact integral_nonneg (fun _ => abs_nonneg _)

end CircleDomainRigidity

end

end OAI
