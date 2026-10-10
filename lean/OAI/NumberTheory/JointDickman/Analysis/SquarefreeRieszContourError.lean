import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszCutIdentification
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszContourShift
import OAI.NumberTheory.JointDickman.Analysis.SquarefreePerronTruncation

namespace OAI

/-! # Combining the four contour errors with the local Riesz contribution -/
namespace JointDickman
open Complex MeasureTheory Set

theorem re_contour_error_le {P V J U D K a : ℂ} (he : V = a*(J+U-D)+K) :
    |P.re-K.re| ≤ ‖P-V‖ + ‖a‖*(‖J‖+‖U‖+‖D‖) := by
  have hid : P-K = (P-V)+a*(J+U-D) := by rw [he]; ring
  have hsum : ‖J+U-D‖ ≤ ‖J‖+‖U‖+‖D‖ := by
    linarith [norm_sub_le (J+U) D,norm_add_le J U]
  calc
    _ ≤ ‖P-K‖ := by simpa only [sub_re] using abs_re_le_norm (P-K)
    _ = ‖(P-V)+a*(J+U-D)‖ := by rw [hid]
    _ ≤ ‖P-V‖+‖a*(J+U-D)‖ := norm_add_le _ _
    _ ≤ ‖P-V‖+‖a‖*(‖J‖+‖U‖+‖D‖) := by
      rw [norm_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (norm_nonneg a))

theorem squarefreeRiesz_contour_error_le : ∃ r : ℝ, 0 < r ∧
    ∀ {z L δ c T : ℝ}, 0 ≤ z → z < 1 → 0 < δ → δ ≤ 1/4 → δ/4 < r →
      0 < c → c ≤ δ/4 → 1 < T →
      ∀ {f : ℂ → ℂ}, AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T)) → f 1 = 0 →
      (∀ s ∈ zetaOpenRectangle δ (2*T), exp (f s) = zetaPoleFactor s) →
      |(VerticalIntegral' (squarefreeNormalizedPerron z L) c).re -
        squarefreeRieszLocalHankel z (δ/4) L| ≤
      ‖VerticalIntegral' (squarefreeNormalizedPerron z L) c -
        (1/(2*(Real.pi:ℂ)*I))*VIntegral (squarefreeNormalizedPerron z L) c (-T) T‖ +
      (1/(2*Real.pi)) *
        (‖VIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) (-T) T‖ +
         ‖HIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) c T‖ +
         ‖HIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) c (-T)‖) := by
  obtain ⟨r,hr,hcut⟩ := squarefreeRiesz_cut_identification
  refine ⟨r,hr,?_⟩
  intro z L δ c T hz hz1 hδ hδ4 hδr hc hcδ hT f hf hf1 he
  have hs := squarefreeRiesz_finite_contour_shift (L := L) hz hz1 hδ hδ4 hc hcδ hT hf hf1 he
  have hb := re_contour_error_le (P := VerticalIntegral' (squarefreeNormalizedPerron z L) c) hs
  rw [hcut hδ (by linarith : 0 < 2*T) hδr hf hf1 he z L,perron_normalization_norm] at hb
  exact hb

end JointDickman

end OAI
