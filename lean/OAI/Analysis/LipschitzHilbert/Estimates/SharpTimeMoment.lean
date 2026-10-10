import OAI.Analysis.LipschitzHilbert.Fourier.SharpKernelComparison

namespace OAI

/-! A sharply truncated Hilbert kernel has first absolute moment at most
twice its outer radius, independently of the inner truncation. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_first_moment (r R : ℝ) (hr : 0<r) (hR : 0<R) :
    Integrable (fun t => |t| *‖sharpTimeKernel r R t‖) ∧
      (∫ t, |t| *‖sharpTimeKernel r R t‖)≤2*R := by
  let q := (Icc (-R) R).indicator (fun _ : ℝ => (1:ℝ))
  have hq : Integrable q := (integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const (by simp))
  have hm : Measurable (fun t => |t| *‖sharpTimeKernel r R t‖) :=
    (show Measurable (fun t : ℝ => |t|) from by fun_prop).mul (sharpTimeKernel_measurable r R).norm
  have hb (t : ℝ) : |t| *‖sharpTimeKernel r R t‖≤q t := by
    by_cases ht : r< |t| ∧ |t|<R
    · have hn : t≠0 := abs_pos.mp (hr.trans ht.1)
      have hmem : t∈Icc (-R) R := abs_le.mp ht.2.le
      simp only [sharpTimeKernel,ite_eq_left ht,q,indicator_of_mem hmem,norm_inv,
        Complex.norm_real,Real.norm_eq_abs,mul_inv_cancel₀ (abs_ne_zero.mpr hn),le_refl]
    · simp only [sharpTimeKernel,ite_eq_right ht,norm_zero,mul_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) t
  have hi := hq.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
      exact hb t)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t, q t := integral_mono hi hq hb
    _ = 2*R := by
      rw [integral_indicator_const 1 measurableSet_Icc]
      simp only [measureReal_def,Real.volume_Icc,smul_eq_mul,mul_one]
      rw [ENNReal.toReal_ofReal (by linarith)]
      ring

end LipschitzHilbert.PacketRepresentation

namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_integrable (r R : ℝ) (hr : 0<r) (hR : 0<R) :
    Integrable (sharpTimeKernel r R) := by
  have hi := (sharpTimeKernel_first_moment r R hr hR).1.const_mul r⁻¹
  apply hi.mono' (sharpTimeKernel_measurable r R).aestronglyMeasurable
  filter_upwards [] with t
  by_cases ht : r< |t| ∧ |t|<R
  · have h1 : 1≤r⁻¹*|t| := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (one_le_div hr).2 ht.1.le
    calc
      _ = 1*‖sharpTimeKernel r R t‖ := (one_mul _).symm
      _ ≤ (r⁻¹*|t|)*‖sharpTimeKernel r R t‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = _ := by ring
  · simp only [sharpTimeKernel,ite_eq_right ht,norm_zero,mul_zero,le_refl]

end LipschitzHilbert.PacketRepresentation

end

end OAI
