import OAI.Analysis.LipschitzHilbert.Fourier.KernelAverageL1
import OAI.Analysis.LipschitzHilbert.Estimates.ShortTimeAverageEnergy

namespace OAI

/-! Integrating a short-time linear error costs only the first absolute
moment of the time kernel, also in L1. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortTimeQuotient_l1 (F : ℝ×(ℝ×ℝ) → ℂ) (B : ℝ) (hB : 0≤B)
    (hF : ∀ t, |t|≤1/4 → Integrable (fun z => F (t,z)) planeMeasure)
    (hbound : ∀ t, |t|≤1/4 → (∫ z, ‖F (t,z)‖ ∂planeMeasure)≤B*|t|)
    (t : ℝ) :
    Integrable (fun z => shortTimeQuotient F (t,z)) planeMeasure ∧
      (∫ z, ‖shortTimeQuotient F (t,z)‖ ∂planeMeasure)≤B := by
  by_cases ht : |t|≤1/4
  · refine ⟨by simpa only [shortTimeQuotient,ite_eq_left ht] using
      (hF t ht).const_mul (t⁻¹:ℂ),?_⟩
    simp only [shortTimeQuotient,ite_eq_left ht,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs]
    rw [integral_const_mul]
    apply (mul_le_mul_of_nonneg_left (hbound t ht) (inv_nonneg.mpr (abs_nonneg t))).trans
    by_cases ht0 : t=0
    · simpa only [ht0,abs_zero,inv_zero,zero_mul] using hB
    · rw [mul_comm B |t|,←mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr ht0),one_mul]
  · simp only [shortTimeQuotient,ite_eq_right ht,norm_zero,integral_zero]
    exact ⟨integrable_zero _ _ _,hB⟩

theorem shortTimeAverage_l1 (K : ℝ → ℂ) (hKm : Measurable K)
    (hK1 : Integrable (fun t => |t| *‖K t‖))
    (F : ℝ×(ℝ×ℝ) → ℂ) (hFm : Measurable F) (B : ℝ) (hB : 0≤B)
    (hF : ∀ t, |t|≤1/4 → Integrable (fun z => F (t,z)) planeMeasure)
    (hbound : ∀ t, |t|≤1/4 → (∫ z, ‖F (t,z)‖ ∂planeMeasure)≤B*|t|) :
    Integrable (fun z => ∫ t, if |t|≤1/4 then K t*F (t,z) else 0) planeMeasure ∧
      (∫ z, ‖∫ t, if |t|≤1/4 then K t*F (t,z) else 0‖ ∂planeMeasure)≤
        (∫ t, |t| *‖K t‖)*B := by
  let K1 := fun t : ℝ => (t:ℂ)*K t
  have hK1m : Measurable K1 := measurable_id.complex_ofReal.mul hKm
  have hK1i : Integrable K1 := by
    apply hK1.mono' hK1m.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by
      simp only [K1,norm_mul,Complex.norm_real,Real.norm_eq_abs,le_refl]
  have heq (z : ℝ×ℝ) : (∫ t, K1 t*shortTimeQuotient F (t,z))=
      ∫ t, if |t|≤1/4 then K t*F (t,z) else 0 := by
    apply integral_congr_ae
    filter_upwards [volume.ae_ne (0:ℝ)] with t ht
    by_cases hshort : |t|≤1/4
    · simp only [shortTimeQuotient,ite_eq_left hshort,K1]
      have hc : (t:ℂ)≠0 := by exact_mod_cast ht
      field_simp
    · simp only [shortTimeQuotient,ite_eq_right hshort,mul_zero]
  have h := kernelAverage_l1 K1 hK1m hK1i (shortTimeQuotient F)
    (shortTimeQuotient_measurable F hFm) B
    (fun t => (shortTimeQuotient_l1 F B hB hF hbound t).1)
    (fun t => (shortTimeQuotient_l1 F B hB hF hbound t).2)
  simp only [heq] at h
  simpa only [K1,norm_mul,Complex.norm_real,Real.norm_eq_abs] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
