import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialEnergySpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The weighted Volterra kernels for reconstructing a radial H¹ value from its derivative. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralPrimitiveKernelValue (R r s : ℝ) : ℂ :=
  (Icc r R).indicator (fun t : ℝ => ((t : ℂ)^11)⁻¹) s

theorem spectralPrimitiveKernelValue_bound (R r : ℝ) (hr : 0 < r) (s : ℝ) :
    ‖spectralPrimitiveKernelValue R r s‖ ≤ (r^11)⁻¹ := by
  by_cases hs : s ∈ Icc r R
  · rw [spectralPrimitiveKernelValue,indicator_of_mem hs,norm_inv,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hr.trans_le hs.1)]
    exact inv_anti₀ (pow_pos hr _) (pow_le_pow_left₀ hr.le hs.1 _)
  · simp only [spectralPrimitiveKernelValue,indicator_of_notMem hs,norm_zero]
    positivity

theorem spectralPrimitiveKernelValue_measurable (R r : ℝ) :
    Measurable (spectralPrimitiveKernelValue R r) := by
  apply Measurable.indicator _ measurableSet_Icc
  fun_prop

noncomputable def spectralPrimitiveKernel (R r : ℝ) (hr : 0 < r) : SpectralRadialL2 R :=
  (MemLp.of_bound (spectralPrimitiveKernelValue_measurable R r).aestronglyMeasurable
    ((r^11)⁻¹) (Filter.Eventually.of_forall (spectralPrimitiveKernelValue_bound R r hr))).toLp
      (spectralPrimitiveKernelValue R r)

theorem spectralPrimitiveKernel_ae (R r : ℝ) (hr : 0 < r) :
    spectralPrimitiveKernel R r hr =ᵐ[radialPressureMeasure R] spectralPrimitiveKernelValue R r :=
  MemLp.coeFn_toLp _

theorem spectralPrimitiveKernel_norm_sq (R r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ‖spectralPrimitiveKernel R r hr‖^2 = ∫ s in r..R, (s^11)⁻¹ := by
  have hR : 0 ≤ R := hr.le.trans hrR
  calc
    _ = ∫ s, ‖spectralPrimitiveKernelValue R r s‖^2 ∂radialPressureMeasure R := by
      rw [← real_inner_self_eq_norm_sq]
      change (∫ s, inner ℝ (spectralPrimitiveKernel R r hr s) (spectralPrimitiveKernel R r hr s)
        ∂radialPressureMeasure R)=_
      apply integral_congr_ae
      filter_upwards [spectralPrimitiveKernel_ae R r hr] with s hs
      rw [hs,real_inner_self_eq_norm_sq]
    _ = ∫ s in Icc (0 : ℝ) R, ‖spectralPrimitiveKernelValue R r s‖^2*s^11 := by
      rw [radialPressureMeasure_integral R hR,intervalIntegral.integral_of_le hR,
        integral_Icc_eq_integral_Ioc]
    _ = ∫ s in Icc (0 : ℝ) R, (Icc r R).indicator (fun t => (t^11)⁻¹) s := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s _
      by_cases hs : s ∈ Icc r R
      · have hs0 : 0 < s := hr.trans_le hs.1
        simp only [spectralPrimitiveKernelValue,indicator_of_mem hs,norm_inv,norm_pow,
          Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs0]
        field_simp
      · simp [spectralPrimitiveKernelValue,hs]
    _ = ∫ s in Icc r R, (s^11)⁻¹ := by
      rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
      have hi : Icc r R ∩ Icc (0 : ℝ) R=Icc r R :=
        inter_eq_left.mpr (fun _ hs => ⟨hr.le.trans hs.1,hs.2⟩)
      rw [hi]
    _ = _ := by
      rw [intervalIntegral.integral_of_le hrR]
      exact integral_Icc_eq_integral_Ioc

theorem spectralPrimitiveKernel_norm_sq_bound (R r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ‖spectralPrimitiveKernel R r hr‖^2 ≤ (r^10)⁻¹/10 := by
  rw [spectralPrimitiveKernel_norm_sq R r hr hrR]
  have hzero : (0 : ℝ) ∉ uIcc r R := by
    rw [uIcc_of_le hrR]
    intro h
    exact (not_le_of_gt hr) h.1
  have he := integral_zpow (a := r) (b := R) (n := (-11 : ℤ))
    (Or.inr ⟨by norm_num,hzero⟩)
  norm_num only [show (-11 : ℤ)+1 = -10 by norm_num,Int.cast_neg,Int.cast_ofNat,
    zpow_neg,zpow_ofNat] at he
  rw [he]
  have hnonneg : 0 ≤ (R^10)⁻¹ := inv_nonneg.mpr (pow_nonneg (hr.le.trans hrR) _)
  linarith

end DefocusingNLS

end OAI
