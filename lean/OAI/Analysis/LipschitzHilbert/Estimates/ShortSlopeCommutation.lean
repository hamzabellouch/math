import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeOperator
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSlopeCommutation
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteBinCommutator

namespace OAI

/-! Identifying the estimated time average with the actual commutator of
the vertical bin and the horizontally localized operator. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def shortTimeKernel (K : ℝ → ℂ) (t : ℝ) : ℂ := if |t|≤1/4 then K t else 0

theorem shortTimeKernel_measurable (K : ℝ → ℂ) (hK : Measurable K) :
    Measurable (shortTimeKernel K) := by
  have hc : Continuous (fun t : ℝ => |t|) := by fun_prop
  exact hK.ite (isClosed_le hc continuous_const).measurableSet measurable_const

theorem shortTimeKernel_integrable (K : ℝ → ℂ) (hK : Integrable K) :
    Integrable (shortTimeKernel K) := by
  have hc : Continuous (fun t : ℝ => |t|) := by fun_prop
  exact hK.indicator (isClosed_le hc continuous_const).measurableSet

theorem shortSlopeOperator_eq_kernel (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f : (ℝ×ℝ) → ℂ) :
    shortSlopeOperator K u f=slopeKernelOperator (shortTimeKernel K) u f := by
  funext z
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp only [shortTimeKernel]
  split_ifs <;> simp

theorem shortSlopeCommutator_eq (K T : ℝ → ℂ)
    (hKm : Measurable K) (hK : Integrable K) (hT : Integrable T)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    verticalConvolution K (shortSlopeOperator T u f) z-
      shortSlopeOperator T u (verticalConvolution K f) z=
        ∫ t, if |t|≤1/4 then T t*verticalSamplingCommutator K u t f z else 0 := by
  rw [shortSlopeOperator_eq_kernel,shortSlopeOperator_eq_kernel,
    verticalSlopeCommutator_eq K (shortTimeKernel T) hKm hK
      (shortTimeKernel_integrable T hT) u hum f z]
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp only [shortTimeKernel]
  split_ifs <;> simp

theorem finiteActualBinCommutator_eq (k q : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength W center : ℝ) (htop : 0<topLength) (hW : 0<W)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    (fun z => verticalConvolution (verticalProfileKernel q W center)
        (shortSlopeOperator (finiteTimeKernel k N topLength) u f) z-
      shortSlopeOperator (finiteTimeKernel k N topLength) u
        (verticalConvolution (verticalProfileKernel q W center) f) z)=
      finiteBinError k q N topLength W center u f := by
  have hqm : Measurable (verticalProfileKernel q W center) := by
    unfold verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((FourierTransform.fourierInv q : SchwartzMap ℝ ℂ).continuous.comp
        (by fun_prop)))).measurable
  funext z
  exact shortSlopeCommutator_eq _ _ hqm
    (modulatedTimeKernel_integrable (FourierTransform.fourierInv q) W center hW)
    (finiteTimeKernel_integrable k N topLength htop) u hum f z

end LipschitzHilbert.PacketRepresentation

end

end OAI
