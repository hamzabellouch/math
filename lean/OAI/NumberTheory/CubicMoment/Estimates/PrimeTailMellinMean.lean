import OAI.NumberTheory.CubicMoment.Estimates.HeightConvolutionBound
import OAI.NumberTheory.CubicMoment.Estimates.ZeroMellinDecay

namespace OAI

/-! The full Mellin envelope preserves a translated height mean.
Only a bounded shift range is needed; the complement uses an actual moment
of the smooth Mellin weight and the coarse polynomial bound. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem complex_mellin_height_mean {P F w : ℝ → ℂ}
    (hP : Continuous P) (hF : Continuous F) (hw : Integrable w)
    (hwn : Continuous (fun s => ‖w s‖))
    (he : ∀ t, F t = ∫ s : ℝ, w s*P (t-s))
    {M B S T : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hS : 0 < S) (hT : 0 < T)
    (hbound : ∀ t, ‖P t‖ ≤ M) (n : ℕ)
    (hmoment : Integrable (fun s : ℝ => |s|^n*‖w s‖))
    (hsmall : ∀ s, |s| ≤ S → dyadicHeightMean (fun t => ‖P (t+s)‖) T ≤ B) :
    dyadicHeightMean (fun t => ‖F t‖) T ≤
      B*(∫ s : ℝ, ‖w s‖)+(2*M)/S^n*(∫ s : ℝ, |s|^n*‖w s‖) := by
  let f := fun s => ‖w (-s)‖
  let G := fun t => ‖P t‖
  have hf : Continuous f := hwn.comp continuous_neg
  have hfi : Integrable f := hw.norm.comp_neg
  have hG : Continuous G := hP.norm
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by
    rw [Real.norm_of_nonneg (_root_.norm_nonneg _)]
    exact hbound t
  have hconv : Continuous (fun t => ∫ s : ℝ, f s*G (t+0+s)) :=
    continuous_height_convolution hf hfi hG hGb 0
  have hm : Integrable (fun s : ℝ => ‖s‖^n*f s) := by
    simpa only [f,Real.norm_eq_abs,abs_neg] using hmoment.comp_neg
  have hmajor (t : ℝ) : ‖F t‖ ≤ ∫ s : ℝ, f s*G (t+0+s) := by
    rw [he t]
    calc
      _ ≤ ∫ s : ℝ, ‖w s*P (t-s)‖ := norm_integral_le_integral_norm _
      _ = ∫ s : ℝ, f s*G (t+0+s) := by
        rw [←integral_neg_eq_self (fun s : ℝ => ‖w s*P (t-s)‖) volume]
        simp only [f,G,norm_mul,sub_neg_eq_add,add_zero]
  have hc := dyadicHeightMean_convolution_window hf hfi (fun _ => _root_.norm_nonneg _)
    hG hM hB hS hT hGb 0 n hm (fun s hs => by
      simpa only [G,add_zero] using hsmall s (by simpa only [Real.norm_eq_abs] using hs))
  have hzero : (∫ s : ℝ, f s) = ∫ s : ℝ, ‖w s‖ := by
    simpa only [f] using integral_neg_eq_self (fun s : ℝ => ‖w s‖) volume
  have hn : (∫ s : ℝ, ‖s‖^n*f s) = ∫ s : ℝ, |s|^n*‖w s‖ := by
    simpa only [f,Real.norm_eq_abs,abs_neg] using
      integral_neg_eq_self (fun s : ℝ => |s|^n*‖w s‖) volume
  exact (dyadicHeightMean_mono hF.norm hconv hT (fun t _ => hmajor t)).trans
    (by simpa only [hzero,hn] using hc)

noncomputable def zeroLineMellinMoment (W : ℝ → ℂ) (n : ℕ) : ℝ :=
  (1/(2*Real.pi))*(∫ s : ℝ, |s|^n*‖mellin W ((s:ℂ)*Complex.I)‖)

theorem zeroLineMellin_height_mean (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) {P F : ℝ → ℂ} (hP : Continuous P) (hF : Continuous F)
    (he : ∀ t, F t = ∫ s : ℝ, zeroLineMellinWeight W X s*P (t-s))
    {M B S T : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hS : 0 < S) (hT : 0 < T)
    (hbound : ∀ t, ‖P t‖ ≤ M) (n : ℕ)
    (hsmall : ∀ s, |s| ≤ S → dyadicHeightMean (fun t => ‖P (t+s)‖) T ≤ B) :
    dyadicHeightMean (fun t => ‖F t‖) T ≤
      B*zeroLineMellinMass W+(2*M)/S^n*zeroLineMellinMoment W n := by
  have hb := complex_mellin_height_mean hP hF
    (zeroLineMellinWeight_integrable W hW hpos hsm hX)
    (continuous_norm_zeroLineMellinWeight W hW hpos hsm hX) he hM hB hS hT hbound n
    (zeroLineMellinWeight_moment_integrable W hW hpos hsm hX n) hsmall
  rw [zeroLineMellinWeight_mass W hX,zeroLineMellinWeight_moment W hX n] at hb
  exact hb

end CubicFirstMoment

end

end OAI
