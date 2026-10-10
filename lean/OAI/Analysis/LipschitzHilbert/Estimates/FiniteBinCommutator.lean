import OAI.Analysis.LipschitzHilbert.Fourier.VerticalCommutatorAverage
import OAI.Analysis.LipschitzHilbert.Fourier.FiniteTimeKernelMoment

namespace OAI

/-! The integrated bin commutator for the actual finite dyadic time kernel.
The bound is uniform in the number of scales and in the bin carrier. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def finiteBinError (k q : SchwartzMap ℝ ℂ) (N : ℕ) (topLength W center : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ t, if |t|≤1/4 then finiteTimeKernel k N topLength t*
    verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0

theorem finiteBinCommutator_energy (k q : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength W center : ℝ) (htop : 0<topLength) (hW : 0<W)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0≤R)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤R) :
    MemLp (fun z => ∫ t, if |t|≤1/4 then finiteTimeKernel k N topLength t*
      verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0)
        2 planeMeasure ∧
    (∫ z, ‖∫ t, if |t|≤1/4 then finiteTimeKernel k N topLength t*
      verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0‖^2
        ∂planeMeasure)≤
      4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant q*(topLength*W*R)^2*
        (∫ z, ‖f z‖^2 ∂planeMeasure) := by
  obtain ⟨hKi,hKb⟩ := finiteTimeKernel_moment1 k N topLength htop
  obtain ⟨hmem,he⟩ := verticalProfileCommutator_average_energy q W center hW u hu
    f R hR hband (finiteTimeKernel k N topLength)
    (finiteTimeKernel_measurable k N topLength) hKi
  refine ⟨hmem,he.trans ?_⟩
  have hs := pow_le_pow_left₀
    (integral_nonneg fun t => mul_nonneg (abs_nonneg t) (norm_nonneg _)) hKb 2
  have hconst : 0≤verticalProfileCommutatorConstant q*(W*R)^2*
      (∫ z, ‖f z‖^2 ∂planeMeasure) := by
    exact mul_nonneg (mul_nonneg (verticalProfileCommutatorConstant_nonneg q) (sq_nonneg _))
      (integral_nonneg fun _ => sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hs hconst
  convert hb using 1 <;> ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
