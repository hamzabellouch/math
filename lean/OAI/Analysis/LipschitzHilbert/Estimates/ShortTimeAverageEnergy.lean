import OAI.Analysis.LipschitzHilbert.Fourier.KernelAverageEnergy

namespace OAI

/-! Integrating a quadratic short-time error costs the first absolute
kernel moment. This avoids a factor from the number of time scales. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def shortTimeQuotient (F : ℝ×(ℝ×ℝ) → ℂ) (p : ℝ×(ℝ×ℝ)) : ℂ :=
  if |p.1|≤1/4 then (p.1⁻¹ : ℂ)*F p else 0

theorem shortTimeQuotient_measurable (F : ℝ×(ℝ×ℝ) → ℂ) (hF : Measurable F) :
    Measurable (shortTimeQuotient F) := by
  have hs : MeasurableSet {p : ℝ×(ℝ×ℝ) | |p.1|≤1/4} := by
    have hc : Continuous (fun p : ℝ×(ℝ×ℝ) => |p.1|) := by fun_prop
    exact (isClosed_le hc continuous_const).measurableSet
  unfold shortTimeQuotient
  exact ((measurable_fst.complex_ofReal.inv).mul hF).ite hs measurable_const

theorem shortTimeQuotient_energy (F : ℝ×(ℝ×ℝ) → ℂ) (B : ℝ) (hB : 0≤B)
    (hF : ∀ t, |t|≤1/4 → MemLp (fun z => F (t,z)) 2 planeMeasure)
    (henergy : ∀ t, |t|≤1/4 → (∫ z, ‖F (t,z)‖^2 ∂planeMeasure)≤B*t^2)
    (t : ℝ) :
    MemLp (fun z => shortTimeQuotient F (t,z)) 2 planeMeasure ∧
      (∫ z, ‖shortTimeQuotient F (t,z)‖^2 ∂planeMeasure)≤B := by
  by_cases ht : |t|≤1/4
  · have hm := (hF t ht).const_mul (t⁻¹ : ℂ)
    refine ⟨by simpa only [shortTimeQuotient,ite_eq_left ht] using hm,?_⟩
    simp only [shortTimeQuotient,ite_eq_left ht,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,mul_pow]
    rw [integral_const_mul]
    have hb := mul_le_mul_of_nonneg_left (henergy t ht) (sq_nonneg |t|⁻¹)
    apply hb.trans
    by_cases ht0 : t=0
    · simpa only [ht0,abs_zero,inv_zero,zero_pow (by decide : 2≠0),zero_mul] using hB
    · have htabs : |t|≠0 := abs_ne_zero.mpr ht0
      rw [inv_pow,←mul_assoc,←sq_abs t]
      rw [mul_comm (|t|^2)⁻¹ B,mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 htabs),mul_one]
  · simp only [shortTimeQuotient,ite_eq_right ht,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
    exact ⟨MemLp.zero',hB⟩

theorem shortTimeAverage_energy (K : ℝ → ℂ) (hKm : Measurable K)
    (hK1 : Integrable (fun t => |t| *‖K t‖))
    (F : ℝ×(ℝ×ℝ) → ℂ) (hFm : Measurable F) (B : ℝ) (hB : 0≤B)
    (hF : ∀ t, |t|≤1/4 → MemLp (fun z => F (t,z)) 2 planeMeasure)
    (henergy : ∀ t, |t|≤1/4 → (∫ z, ‖F (t,z)‖^2 ∂planeMeasure)≤B*t^2) :
    MemLp (fun z => ∫ t, if |t|≤1/4 then K t*F (t,z) else 0) 2 planeMeasure ∧
      (∫ z, ‖∫ t, if |t|≤1/4 then K t*F (t,z) else 0‖^2 ∂planeMeasure)≤
        (∫ t, |t| *‖K t‖)^2*B := by
  let K1 := fun t : ℝ => (t : ℂ)*K t
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
      have hc : (t : ℂ)≠0 := by exact_mod_cast ht
      field_simp
    · simp only [shortTimeQuotient,ite_eq_right hshort,mul_zero]
  have havg := kernelAverage_energy K1 hK1m hK1i (shortTimeQuotient F)
    (shortTimeQuotient_measurable F hFm) B hB
    (fun t => (shortTimeQuotient_energy F B hB hF henergy t).1)
    (fun t => (shortTimeQuotient_energy F B hB hF henergy t).2)
  simp only [heq] at havg
  simpa only [K1,norm_mul,Complex.norm_real,Real.norm_eq_abs] using havg

end LipschitzHilbert.PacketRepresentation

end

end OAI
