import OAI.Analysis.LipschitzHilbert.Fourier.SharpKernelL1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! The actual sharp kernel integral is exactly the positive-time
symmetric quotient, including its sign and both endpoints. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.PacketRepresentation

theorem sharpKernel_symmetrize (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t, sharpTimeKernel epsilon R t*F t)=
      ∫ t in epsilon..R, (t:ℂ)⁻¹*(F t-F (-t)) := by
  let G := fun t : ℝ => (t:ℂ)⁻¹*F t
  let H := fun t : ℝ => (t:ℂ)⁻¹*F (-t)
  have hinv : ContinuousOn (fun t : ℝ => (t:ℂ)⁻¹) (uIcc epsilon R) := by
    apply (Complex.continuous_ofReal.continuousOn).inv₀
    intro t ht
    rw [uIcc_of_le heR] at ht
    exact_mod_cast (he.trans_le ht.1).ne'
  have hG : IntervalIntegrable G volume epsilon R :=
    (hinv.mul hF.continuousOn).intervalIntegrable
  have hH : IntervalIntegrable H volume epsilon R :=
    (hinv.mul (hF.comp continuous_neg).continuousOn).intervalIntegrable
  let A := (Ioo epsilon R).indicator G
  let B := (Ioo epsilon R).indicator H
  have hA : Integrable A := (integrable_indicator_iff measurableSet_Ioo).mpr
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le heR).mp hG)
  have hB : Integrable B := (integrable_indicator_iff measurableSet_Ioo).mpr
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le heR).mp hH)
  have hAI : (∫ t, A t)=∫ t in epsilon..R, G t := by
    rw [integral_indicator measurableSet_Ioo,←integral_Ioc_eq_integral_Ioo,
      ←intervalIntegral.integral_of_le heR]
  have hBI : (∫ t, B t)=∫ t in epsilon..R, H t := by
    rw [integral_indicator measurableSet_Ioo,←integral_Ioc_eq_integral_Ioo,
      ←intervalIntegral.integral_of_le heR]
  have heq (t : ℝ) : sharpTimeKernel epsilon R t*F t=A t-B (-t) := by
    by_cases ht : 0≤t
    · have hn : -t∉Ioo epsilon R := by intro h; linarith only [h.1,he,ht]
      rw [show B (-t)=0 from Set.indicator_of_notMem hn H,sub_zero]
      by_cases hm : t∈Ioo epsilon R
      · have hc : epsilon < |t| ∧ |t|<R := by simpa only [abs_of_nonneg ht,mem_Ioo] using hm
        rw [show A t=G t from Set.indicator_of_mem hm G]
        simp only [sharpTimeKernel,ite_eq_left hc,G]
      · have hc : ¬(epsilon < |t| ∧ |t|<R) := by simpa only [abs_of_nonneg ht,mem_Ioo] using hm
        rw [show A t=0 from Set.indicator_of_notMem hm G]
        simp only [sharpTimeKernel,ite_eq_right hc,zero_mul]
    · have ht' : t<0 := lt_of_not_ge ht
      have hn : t∉Ioo epsilon R := by intro h; linarith only [h.1,he,ht']
      rw [show A t=0 from Set.indicator_of_notMem hn G]
      by_cases hm : -t∈Ioo epsilon R
      · have hc : epsilon < |t| ∧ |t|<R := by simpa only [abs_of_neg ht',mem_Ioo] using hm
        rw [show B (-t)=H (-t) from Set.indicator_of_mem hm H]
        simp only [sharpTimeKernel,ite_eq_left hc,H,neg_neg,Complex.ofReal_neg,inv_neg,neg_mul,zero_sub]
      · have hc : ¬(epsilon < |t| ∧ |t|<R) := by simpa only [abs_of_neg ht',mem_Ioo] using hm
        rw [show B (-t)=0 from Set.indicator_of_notMem hm H]
        simp only [sharpTimeKernel,ite_eq_right hc,zero_mul,sub_zero]
  simp_rw [heq]
  rw [integral_sub hA hB.comp_neg]
  have hneg : (∫ t, B (-t))=∫ t, B t := by simpa using Measure.integral_comp_mul_left B (-1)
  rw [hneg,hAI,hBI,←intervalIntegral.integral_sub hG hH]
  apply intervalIntegral.integral_congr
  intro t _
  change (t:ℂ)⁻¹*F t-(t:ℂ)⁻¹*F (-t)=(t:ℂ)⁻¹*(F t-F (-t))
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
