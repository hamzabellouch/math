import OAI.Analysis.LipschitzHilbert.Estimates.SharpTimeMoment

namespace OAI

/-! The principal-value kernel is not absolutely integrable, but its first
absolute moment is. This is the cancellation needed by the band-reassembly
commutator, without assuming any Hilbert-transform estimate. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def principalTimeKernel (R : ℝ) : ℝ → ℂ := sharpTimeKernel 0 R

theorem principalTimeKernel_measurable (R : ℝ) : Measurable (principalTimeKernel R) :=
  sharpTimeKernel_measurable 0 R

theorem principalTimeKernel_first_moment (R : ℝ) (hR : 0<R) :
    Integrable (fun t => |t| *‖principalTimeKernel R t‖) ∧
      (∫ t, |t| *‖principalTimeKernel R t‖)≤2*R := by
  let q := (Icc (-R) R).indicator (fun _ : ℝ => (1:ℝ))
  have hq : Integrable q := (integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const (by simp))
  have hm : Measurable (fun t => |t| *‖principalTimeKernel R t‖) :=
    (show Measurable (fun t : ℝ => |t|) from by fun_prop).mul (principalTimeKernel_measurable R).norm
  have hb (t : ℝ) : |t| *‖principalTimeKernel R t‖≤q t := by
    by_cases ht : 0< |t| ∧ |t|<R
    · have hn : t≠0 := abs_pos.mp ht.1
      have hmem : t∈Icc (-R) R := abs_le.mp ht.2.le
      simp only [principalTimeKernel,sharpTimeKernel,ite_eq_left ht,q,
        indicator_of_mem hmem,norm_inv,Complex.norm_real,Real.norm_eq_abs,
        mul_inv_cancel₀ (abs_ne_zero.mpr hn),le_refl]
    · simp only [principalTimeKernel,sharpTimeKernel,ite_eq_right ht,norm_zero,mul_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) t
  have hi := hq.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
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

end

end OAI
