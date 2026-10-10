import OAI.Analysis.LipschitzHilbert.Fourier.LineSmoothCarleson
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicSmoothCutoff
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineNesting

namespace OAI

/-! The smooth Carleson condition for the actual binary line projections,
first on intervals and then on the nested dyadic line cells. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def dyadicCarlesonConstant : ℝ :=
  72+4*(∫ t : ℝ, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)^2

theorem dyadicCarlesonConstant_pos : 0<dyadicCarlesonConstant := by
  unfold dyadicCarlesonConstant
  positivity

theorem dyadic_projection_carleson_interval (N : ℕ) (a b : ℝ) (hab : a<b)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B) :
    (∑ n∈Finset.range N, ∫ x in Icc a b,
      ‖lineConvolution (lineProjectionKernel dyadicDifference ((b-a)/(2:ℝ)^n)
        (by positivity)) f x‖^2)≤dyadicCarlesonConstant*B^2*(b-a) := by
  simpa only [dyadicCarlesonConstant,show (6:ℝ)*12=72 by norm_num] using
    lineProjection_smooth_carleson dyadicDifference N a b hab 12 (by norm_num)
    (fun eta => dyadicDifference_inverse_square_sum (Finset.range N) (b-a) eta)
    f hfm B hB hfb

open DyadicLineGrid in
theorem dyadic_projection_carleson_cell (N : ℕ) (q j i : ℤ)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B) :
    (∑ n∈Finset.range N, ∫ x in cell q j i,
      ‖lineConvolution (lineProjectionKernel dyadicDifference (scale (j-(n:ℤ)))
        (scale_pos _).ne') f x‖^2)≤dyadicCarlesonConstant*B^2*scale j := by
  have hwidth : left q j (i+1)-left q j i=scale j := by
    unfold left
    push_cast
    ring
  have hab : left q j i<left q j (i+1) := by
    have hs := scale_pos j
    linarith
  have hscale (n : ℕ) : (left q j (i+1)-left q j i)/(2:ℝ)^n=scale (j-(n:ℤ)) := by
    rw [hwidth]
    simp only [scale,zpow_sub₀ (by norm_num : (2:ℝ)≠0),zpow_natCast]
  have h := dyadic_projection_carleson_interval N (left q j i) (left q j (i+1))
    hab f hfm B hB hfb
  simp_rw [hscale] at h
  simpa only [integral_Icc_eq_integral_Ico,hwidth,cell] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
