import Mathlib
import OAI.Probability.SKBarriers.Scalar.DyadicCDFStability
import OAI.Probability.SKBarriers.Parisi.CDFAtomicRepresentation

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdfPenalty_integrable {α : ℝ → ℝ} (hαm : Monotone α) :
    IntegrableOn (fun s => s*α s) (Icc (0:ℝ) 1) :=
  IntegrableOn.continuousOn_mul continuousOn_id (MonotoneOn.integrableOn_isCompact isCompact_Icc (hαm.monotoneOn _)) isCompact_Icc

theorem cdfPenalty_lipschitz {α γ : ℝ → ℝ} (hαm : Monotone α) (hγm : Monotone γ) :
    |(∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s)| ≤
      ∫ s in Icc (0:ℝ) 1, |α s-γ s| := by
  rw [← integral_sub (cdfPenalty_integrable hαm) (cdfPenalty_integrable hγm)]
  calc
    _ ≤ ∫ s in Icc (0:ℝ) 1, |s*α s-s*γ s| := abs_integral_le_integral_abs
    _ ≤ _ := setIntegral_mono_on ((cdfPenalty_integrable hαm).sub (cdfPenalty_integrable hγm)).abs
      ((MonotoneOn.integrableOn_isCompact isCompact_Icc (hαm.monotoneOn _)).sub (MonotoneOn.integrableOn_isCompact isCompact_Icc (hγm.monotoneOn _))).abs measurableSet_Icc (by
        intro s hs
        rw [← mul_sub,abs_mul,abs_of_nonneg hs.1]
        exact mul_le_of_le_one_left (abs_nonneg _) hs.2)

theorem scalarCDFParisi_cdf_lipschitz (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ) :
    |scalarCDFParisi β α-scalarCDFParisi β γ| ≤
      (scalarTimeMassConstant β+β^2/2)*(∫ s in Icc (0:ℝ) 1, |α s-γ s|) := by
  have H := scalarCDFValue_cdf_lipschitz β hα hαm hγ hγm 0 1 le_rfl 0
  simp only [NNReal.coe_one,zero_add,intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] at H
  unfold scalarCDFParisi
  calc
    _ = |(scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0)-
        (β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))| := by congr 1; ring
    _ ≤ |scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0|+
        (β^2/2)*|(∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s)| := by
      calc
        _ ≤ |scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0|+
            |(β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))| := by
          simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le
            (scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0) 0
            ((β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))))
        _ = _ := by rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ β^2/2)]
    _ ≤ scalarTimeMassConstant β*(∫ s in Icc (0:ℝ) 1, |α s-γ s|)+
        (β^2/2)*(∫ s in Icc (0:ℝ) 1, |α s-γ s|) :=
      add_le_add H (mul_le_mul_of_nonneg_left (cdfPenalty_lipschitz hαm hγm) (by positivity))
    _ = _ := by ring

theorem scalarCDFParisi_tendsto_of_L1 (β : ℝ) {α : ℝ → ℝ} {αs : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hs : ∀ n z, αs n z ∈ Icc (0:ℝ) 1) (hsm : ∀ n, Monotone (αs n))
    (ht : Tendsto (fun n => ∫ z in Icc (0:ℝ) 1, |αs n z-α z|) atTop (𝓝 0)) :
    Tendsto (fun n => scalarCDFParisi β (αs n)) atTop (𝓝 (scalarCDFParisi β α)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := squeeze_zero (fun _ => abs_nonneg _)
    (fun n => scalarCDFParisi_cdf_lipschitz β (hs n) (hsm n) hα hαm)
    (by simpa only [mul_zero] using ht.const_mul (scalarTimeMassConstant β+β^2/2))
  simpa only [mul_zero,Real.norm_eq_abs] using H

end SK.Analytic

end
end

end OAI
