import OAI.Analysis.LipschitzHilbert.Fourier.ScaledFrequencyWindows
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

/-! Exact Fourier coordinates of the normalized physical kernels.
The Jacobian is derived by two one-dimensional changes of variables. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem integral_packetCoordinates (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta : ℝ) (hl : l≠0) (hW : W≠0) :
    (∫ z, F (packetCoordinates l W theta hl hW z) ∂planeMeasure)=
      |l*W| • (∫ z, F z ∂planeMeasure) := by
  let G := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (packetCoordinates l W theta hl hW) F
  have hi : Integrable (fun z => F (packetCoordinates l W theta hl hW z)) planeMeasure := G.integrable
  have hs (x : ℝ) : (∫ y : ℝ, F (x/l,(y-theta*x)/W))=
      |W| • (∫ y : ℝ, F (x/l,y)) := by
    rw [integral_sub_right_eq_self (fun y : ℝ => F (x/l,y/W)) (theta*x)]
    exact Measure.integral_comp_div (fun y : ℝ => F (x/l,y)) W
  calc
    _ = ∫ x : ℝ, ∫ y : ℝ, F (x/l,(y-theta*x)/W) := integral_prod _ hi
    _ = ∫ x : ℝ, |W| • (∫ y : ℝ, F (x/l,y)) :=
      integral_congr_ae (Filter.Eventually.of_forall hs)
    _ = |W| • (∫ x : ℝ, ∫ y : ℝ, F (x/l,y)) := integral_smul _ _
    _ = |W| • (|l| • (∫ x : ℝ, ∫ y : ℝ, F (x,y))) := by
      rw [Measure.integral_comp_div (fun x : ℝ => ∫ y : ℝ, F (x,y)) l]
    _ = _ := by
      rw [smul_smul, ← integral_prod _ F.integrable, abs_mul, mul_comm]

theorem normalizedSpatialKernel_fourier (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ) :
    planarFourier (normalizedSpatialKernel F l W theta (2*Real.pi*center) hl.ne' hW.ne') (xi,eta)=
      planarFourier F (symbolX l xi eta theta,symbolY W eta center) := by
  let X := symbolX l xi eta theta
  let Y := symbolY W eta center
  let G := modulatedFrequencyWindow F (-X) (-Y) 0
  have hpoint (z : ℝ×ℝ) :
      Real.fourierChar (-(z.1*xi+z.2*eta)) •
        normalizedSpatialKernel F l W theta (2*Real.pi*center) hl.ne' hW.ne' z=
      (l*W:ℂ)⁻¹*G (packetCoordinates l W theta hl.ne' hW.ne' z) := by
    simp only [normalizedSpatialKernel, smul_apply, smul_eq_mul, physicalPlanarPacket_apply,
      sub_zero, G, modulatedFrequencyWindow_apply]
    change (Real.fourierChar (-(z.1*xi+z.2*eta)):ℂ)*
      ((l*W:ℂ)⁻¹*(Complex.exp (((2*Real.pi*center)*(z.2-theta*z.1):ℝ)*Complex.I)*
        F (z.1/l,(z.2-theta*z.1)/W)))=
      (l*W:ℂ)⁻¹*((Real.fourierChar ((-X)*(z.1/l)+(-Y)*((z.2-theta*z.1)/W)+0):ℂ)*
        F (z.1/l,(z.2-theta*z.1)/W))
    have hp : (Real.fourierChar (-(z.1*xi+z.2*eta)):ℂ)*
        Complex.exp (((2*Real.pi*center)*(z.2-theta*z.1):ℝ)*Complex.I)=
        (Real.fourierChar ((-X)*(z.1/l)+(-Y)*((z.2-theta*z.1)/W)+0):ℂ) := by
      rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add]
      congr 1
      dsimp [X,Y,symbolX,symbolY]
      push_cast
      field_simp [show (l:ℂ)≠0 by exact_mod_cast hl.ne', show (W:ℂ)≠0 by exact_mod_cast hW.ne']
      ring
    calc
      _ = (l*W:ℂ)⁻¹*((Real.fourierChar (-(z.1*xi+z.2*eta)):ℂ)*
          Complex.exp (((2*Real.pi*center)*(z.2-theta*z.1):ℝ)*Complex.I))*
            F (z.1/l,(z.2-theta*z.1)/W) := by ring
      _ = _ := by rw [hp]; ring
  have hint : (∫ z, G z ∂planeMeasure)=planarFourier F (X,Y) := by
    unfold planarFourier
    apply integral_congr_ae
    filter_upwards [] with z
    rw [modulatedFrequencyWindow_apply]
    change (Real.fourierChar ((-X)*z.1+(-Y)*z.2+0):ℂ)*F z=
      (Real.fourierChar (-(z.1*X+z.2*Y)):ℂ)*F z
    have he : (-X)*z.1+(-Y)*z.2+0= -(z.1*X+z.2*Y) := by ring
    rw [he]
  unfold planarFourier
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul,
    integral_packetCoordinates G l W theta hl.ne' hW.ne', abs_of_pos (mul_pos hl hW)]
  rw [Complex.real_smul, ← mul_assoc, Complex.ofReal_mul,
    inv_mul_cancel₀ (show (l:ℂ)*(W:ℂ)≠0 by exact_mod_cast (mul_pos hl hW).ne'), one_mul]
  exact hint

theorem scaledFrequencyWindow_apply (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ) :
    scaledFrequencyWindow F l W theta (2*Real.pi*center) hl.ne' hW.ne' (xi,eta)=
      planarFourier F (symbolX l xi eta theta,symbolY W eta center) := by
  rw [scaledFrequencyWindow, planarFourierSchwartz_apply]
  exact normalizedSpatialKernel_fourier F l W theta center hl hW xi eta

end LipschitzHilbert.PacketRepresentation

end

end OAI
