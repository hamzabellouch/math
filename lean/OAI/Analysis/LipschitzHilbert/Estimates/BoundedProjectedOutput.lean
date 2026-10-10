import OAI.Analysis.LipschitzHilbert.Fourier.BoundedVerticalMultiplier
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalHorizontalCutoff

namespace OAI

/-! A band projection of a bounded input can be reproduced on L2 as
soon as that projected output is known to belong to L2. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzVerticalProjection_dilate (p : SchwartzMap ℝ ℂ) (d W : ℝ)
    (hd : d≠0) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    schwartzVerticalProjection (dilatedSlopeWindow p d hd) W 0 f=
      schwartzVerticalProjection p (d*W) 0 f := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [schwartzVerticalProjection_fourier,sub_zero,dilatedSlopeWindow_apply]
  rw [mul_assoc]

theorem verticalL2Projection_on_projected_bounded (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ x, p x*q x=q x) (W : ℝ) (hW : 0<W)
    (F : (ℝ×ℝ) → ℂ) (hFm : Measurable F) (B : ℝ) (hFb : ∀ z, ‖F z‖≤B)
    (hG : MemLp (verticalConvolution (verticalProfileKernel q W 0) F) 2 planeMeasure) :
    verticalL2Projection p W (hG.toLp (verticalConvolution (verticalProfileKernel q W 0) F))=
      hG.toLp (verticalConvolution (verticalProfileKernel q W 0) F) := by
  let G := verticalConvolution (verticalProfileKernel q W 0) F
  have hGm : Measurable G := verticalConvolution_measurable _
    (verticalProfileKernel_continuous q W 0).measurable F hFm
  rw [verticalL2Projection_eq_profile p W hW,verticalProfileLp,
    verticalConvolutionLp_toLp _ _ _ G hGm hG]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (verticalConvolution_energy_bound
    (verticalProfileKernel p W 0) (verticalProfileKernel_integrable p W 0 hW)
    (verticalProfileKernel_continuous p W 0).measurable G hGm hG).1,hG.coeFn_toLp] with z hz hz'
  rw [hz,hz']
  exact verticalProjection_bounded_absorb p q hpq W hW F hFm B hFb z

end LipschitzHilbert.PacketRepresentation

end

end OAI
