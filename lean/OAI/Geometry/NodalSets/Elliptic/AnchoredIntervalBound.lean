import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

namespace Yau.Analysis
open MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section

lemma enorm_le_anchor_lintegral {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖f t‖ₑ ≤ ‖f 0‖ₑ + ∫⁻ u in Icc (-1 : ℝ) 1, ‖deriv f u‖ₑ := by
  have hd : ‖f t - f 0‖ₑ ≤ ∫⁻ u in Icc (-1 : ℝ) 1, ‖deriv f u‖ₑ := by
    by_cases h : 0 ≤ t
    · exact (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf.contDiffOn h).trans
        (lintegral_mono_set (Icc_subset_Icc (by norm_num) ht.2))
    · have h' := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf.contDiffOn (le_of_not_ge h)
      rw [enorm_sub_rev] at h'
      exact h'.trans (lintegral_mono_set (Icc_subset_Icc ht.1 (by norm_num)))
  calc
    ‖f t‖ₑ = ‖f 0 + (f t-f 0)‖ₑ := by congr 1; ring
    _ ≤ ‖f 0‖ₑ + ‖f t-f 0‖ₑ := enorm_add_le _ _
    _ ≤ _ := add_le_add_right hd _

end
end Yau.Analysis

end OAI
