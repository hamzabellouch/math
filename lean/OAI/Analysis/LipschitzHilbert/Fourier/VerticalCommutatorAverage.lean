import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinCommutator
import OAI.Analysis.LipschitzHilbert.Estimates.ShortTimeAverageEnergy

namespace OAI

/-! A first-moment bound for the actual bin/sampling commutator, integrated
over the short times allowed by the horizontal localization. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSamplingCommutator_joint_measurable (K : ℝ → ℂ) (hKm : Measurable K)
    (hK : Integrable K) (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Measurable (fun p : ℝ×(ℝ×ℝ) => verticalSamplingCommutator K u p.1 f p.2) := by
  have hm : Measurable (fun p : (ℝ×(ℝ×ℝ))×ℝ =>
      K p.2*verticalSamplingDifference f u p.1.1 p.2 p.1.2) := by
    change Measurable (fun p : (ℝ×(ℝ×ℝ))×ℝ => K p.2 *
      (f (p.1.2.1-p.1.1,p.1.2.2-p.2-p.1.1*u (p.1.2.1,p.1.2.2-p.2))-
        f (p.1.2.1-p.1.1,p.1.2.2-p.2-p.1.1*u p.1.2)))
    fun_prop
  have heq : (fun p : ℝ×(ℝ×ℝ) => verticalSamplingCommutator K u p.1 f p.2)=
      (fun p => ∫ s, K s*verticalSamplingDifference f u p.1 s p.2) := by
    funext p
    exact verticalSamplingCommutator_eq K hK u hum p.1 f p.2
  rw [heq]
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem verticalProfileCommutator_average_energy (q : SchwartzMap ℝ ℂ)
    (W center : ℝ) (hW : 0<W) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0≤R)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤R)
    (K : ℝ → ℂ) (hKm : Measurable K) (hK1 : Integrable (fun t => |t| *‖K t‖)) :
    MemLp (fun z => ∫ t, if |t|≤1/4 then
      K t*verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0)
        2 planeMeasure ∧
    (∫ z, ‖∫ t, if |t|≤1/4 then
      K t*verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0‖^2
        ∂planeMeasure)≤
      (∫ t, |t| *‖K t‖)^2*verticalProfileCommutatorConstant q*(W*R)^2*
        (∫ z, ‖f z‖^2 ∂planeMeasure) := by
  have hqm : Measurable (verticalProfileKernel q W center) := by
    unfold verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((FourierTransform.fourierInv q : SchwartzMap ℝ ℂ).continuous.comp
        (by fun_prop)))).measurable
  have hqi := modulatedTimeKernel_integrable (FourierTransform.fourierInv q) W center hW
  let B := verticalProfileCommutatorConstant q*(W*R)^2*
    (∫ z, ‖f z‖^2 ∂planeMeasure)
  have hB : 0≤B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg (verticalProfileCommutatorConstant_nonneg q) (sq_nonneg _))
      (integral_nonneg fun _ => sq_nonneg _)
  have h := shortTimeAverage_energy K hKm hK1
    (fun p => verticalSamplingCommutator (verticalProfileKernel q W center) u p.1 f p.2)
    (verticalSamplingCommutator_joint_measurable _ hqm hqi u hu.continuous.measurable f)
    B hB (fun t ht => (verticalProfileCommutator_energy q W center hW u hu t ht f R hR hband).1)
    (fun t ht => by
      have he := (verticalProfileCommutator_energy q W center hW u hu t ht f R hR hband).2
      convert he using 1; dsimp only [B]; ring)
  refine ⟨h.1,h.2.trans_eq ?_⟩
  dsimp only [B]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
