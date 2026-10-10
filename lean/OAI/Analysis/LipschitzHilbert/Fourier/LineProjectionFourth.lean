import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionFourth
import OAI.Analysis.LipschitzHilbert.Fourier.LineProjectionLipschitz

namespace OAI

/-! Uniform fourth-power estimates for one or two scaled smooth cutoffs. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem norm_add_fourth_le (x y : ℂ) : ‖x+y‖^4≤8*(‖x‖^4+‖y‖^4) := by
  calc
    _ ≤ (‖x‖+‖y‖)^4 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 4
    _ ≤ _ := by simpa only [show (4:ℕ)-1=3 from rfl,show (2:ℝ)^3=8 by norm_num] using
      add_pow_le (norm_nonneg x) (norm_nonneg y) 4

theorem norm_sub_fourth_le (x y : ℂ) : ‖x-y‖^4≤8*(‖x‖^4+‖y‖^4) := by
  simpa only [sub_eq_add_neg,norm_neg] using norm_add_fourth_le x (-y)

theorem lineSchwartzProjection_fourth (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖lineSchwartzProjection q W hW.ne' f x‖^4)≤
      (∫ t, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖)^4*(∫ x, ‖f x‖^4) := by
  have hh := (lineConvolution_fourth_bound (lineProjectionKernel q W hW.ne')
    (lineProjectionKernel q W hW.ne').integrable
    (lineProjectionKernel q W hW.ne').continuous.measurable f).2
  simp_rw [←lineSchwartzProjection_eq_convolution q W hW.ne' f] at hh
  rwa [lineProjectionKernel_l1 q W hW] at hh

theorem lineSchwartzProjection_difference_fourth (q : SchwartzMap ℝ ℂ)
    (A B : ℝ) (hA : 0<A) (hB : 0<B) (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖(lineSchwartzProjection q A hA.ne' f-
      lineSchwartzProjection q B hB.ne' f) x‖^4)≤
      16*(∫ t, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖)^4*(∫ x, ‖f x‖^4) := by
  let u := lineSchwartzProjection q A hA.ne' f
  let v := lineSchwartzProjection q B hB.ne' f
  have hu : Integrable (fun x => ‖u x‖^4) := (u.memLp 4 volume).integrable_norm_pow (by decide)
  have hv : Integrable (fun x => ‖v x‖^4) := (v.memLp 4 volume).integrable_norm_pow (by decide)
  have hd : Integrable (fun x => ‖(u-v) x‖^4) := ((u-v).memLp 4 volume).integrable_norm_pow (by decide)
  have hh := integral_mono hd ((hu.add hv).const_mul 8) (fun x => norm_sub_fourth_le (u x) (v x))
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add hu hv] at hh
  have ha := lineSchwartzProjection_fourth q A hA f
  have hb := lineSchwartzProjection_fourth q B hB f
  change (∫ x, ‖(u-v) x‖^4)≤_
  change (∫ x, ‖u x‖^4)≤_ at ha
  change (∫ x, ‖v x‖^4)≤_ at hb
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
