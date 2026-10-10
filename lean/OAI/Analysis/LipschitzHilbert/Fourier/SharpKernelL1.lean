import OAI.Analysis.LipschitzHilbert.Estimates.SharpTimeMoment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The long-time kernel has its exact logarithmic L1 mass. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_l1 (r R : ℝ) (hr : 0<r) (hrR : r≤R) :
    (∫ t, ‖sharpTimeKernel r R t‖)=2*Real.log (R/r) := by
  let A := (Ioo r R).indicator (fun t : ℝ => t⁻¹)
  have hA : Integrable A := by
    apply (integrable_indicator_iff measurableSet_Ioo).2
    apply Measure.integrableOn_of_bounded (by simp)
      (show AEStronglyMeasurable (fun t : ℝ => t⁻¹) volume from by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs,abs_inv,abs_of_pos (hr.trans ht.1)]
    exact (inv_le_inv₀ (hr.trans ht.1) hr).2 ht.1.le
  have hAI : (∫ t, A t)=Real.log (R/r) := by
    rw [integral_indicator measurableSet_Ioo,←integral_Ioc_eq_integral_Ioo,
      ←intervalIntegral.integral_of_le hrR]
    exact integral_inv_of_pos hr (hr.trans_le hrR)
  have heq (t : ℝ) : ‖sharpTimeKernel r R t‖=A t+A (-t) := by
    change ‖sharpTimeKernel r R t‖=(Ioo r R).indicator (fun t : ℝ => t⁻¹) t+
      (Ioo r R).indicator (fun t : ℝ => t⁻¹) (-t)
    by_cases ht : 0≤t
    · have hn : -t∉Ioo r R := by intro h; linarith [h.1]
      rw [Set.indicator_of_notMem hn,add_zero]
      by_cases h : t∈Ioo r R
      · rw [Set.indicator_of_mem h]
        rw [sharpTimeKernel,ite_eq_left (show r< |t| ∧ |t|<R by
          simpa only [abs_of_nonneg ht,Set.mem_Ioo] using h)]
        simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
      · rw [Set.indicator_of_notMem h]
        simp only [sharpTimeKernel,abs_of_nonneg ht,ite_eq_right (show ¬(r<t ∧ t<R) by simpa only [Set.mem_Ioo] using h),norm_zero]
    · have hn : t∉Ioo r R := by intro h; linarith [h.1]
      rw [Set.indicator_of_notMem hn,zero_add]
      have ht' : t<0 := lt_of_not_ge ht
      by_cases h : -t∈Ioo r R
      · rw [Set.indicator_of_mem h]
        rw [sharpTimeKernel,ite_eq_left (show r< |t| ∧ |t|<R by
          simpa only [abs_of_neg ht',Set.mem_Ioo] using h)]
        simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_neg ht']
      · rw [Set.indicator_of_notMem h]
        simp only [sharpTimeKernel,abs_of_neg ht',ite_eq_right (show ¬(r< -t ∧ -t<R) by simpa only [Set.mem_Ioo] using h),norm_zero]
  simp_rw [heq]
  rw [integral_add hA hA.comp_neg]
  have hn : (∫ t, A (-t))=∫ t, A t := by
    simpa using Measure.integral_comp_mul_left A (-1)
  rw [hn,hAI]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
