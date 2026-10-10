import OAI.NumberTheory.CubicMoment.Estimates.HeightConvolution
import OAI.NumberTheory.CubicMoment.Estimates.NormMellinMoments

namespace OAI

/-! A height bound on the central Mellin window and the actual moment
tail of the Mellin weight suffice for the averaged convolution. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma integrable_height_convolution_mean {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (fun s => f s*dyadicHeightMean (fun t => G (t+u+s)) T) := by
  have hp := integrable_height_convolution_interval hf hfi hG hbound u
    (by linarith : T ≤ 2*T)
  have hn := integrable_height_convolution_interval hf hfi hG hbound u
    (by linarith : -2*T ≤ -T)
  convert (hp.add hn).div_const T using 1
  funext s
  dsimp [dyadicHeightMean]
  ring

theorem dyadicHeightMean_convolution_window {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hf0 : ∀ s, 0 ≤ f s)
    (hG : Continuous G) {M B S T : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hS : 0 < S) (hT : 0 < T) (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) (n : ℕ)
    (hfm : Integrable (fun s => ‖s‖^n*f s))
    (hsmall : ∀ s, ‖s‖ ≤ S →
      dyadicHeightMean (fun t => G (t+u+s)) T ≤ B) :
    dyadicHeightMean (fun t => ∫ s : ℝ, f s*G (t+u+s)) T ≤
      B*(∫ s : ℝ, f s)+(2*M)/S^n*(∫ s : ℝ, ‖s‖^n*f s) := by
  let H := fun s => dyadicHeightMean (fun t => G (t+u+s)) T
  have hglobal (s : ℝ) : H s ≤ 2*M := by
    apply dyadicHeightMean_le_const (hG.comp (by fun_prop)) hT
    intro t _
    exact (le_abs_self _).trans (hbound (t+u+s))
  rw [dyadicHeightMean_convolution hf hfi hG hbound u hT]
  calc
    _ ≤ ∫ s : ℝ, B*f s+((2*M)/S^n)*(‖s‖^n*f s) := by
      apply integral_mono (integrable_height_convolution_mean hf hfi hG hbound u hT)
        ((hfi.const_mul B).add (hfm.const_mul ((2*M)/S^n)))
      intro s
      have hh := mellin_window_majorant hB (by positivity : 0 ≤ 2*M) hS n hglobal hsmall s
      calc
        _ ≤ f s*(B+(2*M)/S^n*‖s‖^n) := mul_le_mul_of_nonneg_left hh (hf0 s)
        _ = _ := by dsimp only [Pi.add_apply]; ring
    _ = _ := by rw [integral_add (hfi.const_mul B) (hfm.const_mul ((2*M)/S^n)),
      integral_const_mul,integral_const_mul]

end CubicFirstMoment

end

end OAI
