import OAI.Analysis.LipschitzHilbert.Estimates.PrincipalTimeMoment
import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeCommutation
import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram

namespace OAI

/-! The actual vertical-profile commutator has a bound independent of the
inner cutoff. Its principal-time integral has the same bound. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def sharpVerticalCommutator (q : SchwartzMap ℝ ℂ) (W center epsilon R : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) : (ℝ×ℝ) → ℂ :=
  verticalConvolution (verticalProfileKernel q W center)
    (shortSlopeOperator (sharpTimeKernel epsilon R) u f)-
  shortSlopeOperator (sharpTimeKernel epsilon R) u
    (verticalConvolution (verticalProfileKernel q W center) f)

def principalVerticalCommutator (q : SchwartzMap ℝ ℂ) (W center R : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ t, if |t|≤1/4 then principalTimeKernel R t*
    verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0

theorem profileTimeCommutator_energy (q : SchwartzMap ℝ ℂ) (W center R : ℝ)
    (hW : 0<W) (_hR : 0≤R) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (F : ℝ) (hF : 0≤F)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤F)
    (K : ℝ → ℂ) (hKm : Measurable K)
    (hKi : Integrable (fun t => |t| *‖K t‖)) (hK : (∫ t, |t| *‖K t‖)≤2*R) :
    MemLp (fun z => ∫ t, if |t|≤1/4 then K t*
      verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0)
      2 planeMeasure ∧
    (∫ z, ‖∫ t, if |t|≤1/4 then K t*
      verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0‖^2
      ∂planeMeasure)≤4*R^2*verticalProfileCommutatorConstant q*(W*F)^2*
        (∫ z, ‖f z‖^2 ∂planeMeasure) := by
  obtain ⟨hm,he⟩ := verticalProfileCommutator_average_energy q W center hW u hu f F hF hband K hKm hKi
  refine ⟨hm,he.trans ?_⟩
  have hc : 0≤verticalProfileCommutatorConstant q*(W*F)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) :=
    mul_nonneg (mul_nonneg (verticalProfileCommutatorConstant_nonneg q) (sq_nonneg _))
      (integral_nonneg fun _ => sq_nonneg _)
  have hp := pow_le_pow_left₀ (integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)) hK 2
  have h := mul_le_mul_of_nonneg_right hp hc
  convert h using 1 <;> ring

theorem sharpVerticalCommutator_eq (q : SchwartzMap ℝ ℂ) (W center epsilon R : ℝ)
    (hW : 0<W) (he : 0<epsilon) (hR : 0<R) (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    sharpVerticalCommutator q W center epsilon R u f=
      fun z => ∫ t, if |t|≤1/4 then sharpTimeKernel epsilon R t*
        verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0 := by
  funext z
  exact shortSlopeCommutator_eq (verticalProfileKernel q W center) (sharpTimeKernel epsilon R)
    (by
      unfold verticalProfileKernel modulatedTimeKernel scaledTimeKernel
      exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
        (continuous_const.mul ((FourierTransform.fourierInv q : SchwartzMap ℝ ℂ).continuous.comp
          (by fun_prop)))).measurable)
    (modulatedTimeKernel_integrable _ W center hW) (sharpTimeKernel_integrable epsilon R he hR)
    u hum f z

theorem sharpVerticalCommutator_energy (q : SchwartzMap ℝ ℂ) (W center epsilon R : ℝ)
    (hW : 0<W) (he : 0<epsilon) (hR : 0<R)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (F : ℝ) (hF : 0≤F)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤F) :
    MemLp (sharpVerticalCommutator q W center epsilon R u f) 2 planeMeasure ∧
    (∫ z, ‖sharpVerticalCommutator q W center epsilon R u f z‖^2 ∂planeMeasure)≤
      4*R^2*verticalProfileCommutatorConstant q*(W*F)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  rw [sharpVerticalCommutator_eq q W center epsilon R hW he hR u hu.continuous.measurable f]
  exact profileTimeCommutator_energy q W center R hW hR.le u hu f F hF hband
    (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_first_moment epsilon R he hR).1 (sharpTimeKernel_first_moment epsilon R he hR).2

theorem principalVerticalCommutator_energy (q : SchwartzMap ℝ ℂ) (W center R : ℝ)
    (hW : 0<W) (hR : 0<R) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (F : ℝ) (hF : 0≤F)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤F) :
    MemLp (principalVerticalCommutator q W center R u f) 2 planeMeasure ∧
    (∫ z, ‖principalVerticalCommutator q W center R u f z‖^2 ∂planeMeasure)≤
      4*R^2*verticalProfileCommutatorConstant q*(W*F)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) :=
  profileTimeCommutator_energy q W center R hW hR.le u hu f F hF hband
    (principalTimeKernel R) (principalTimeKernel_measurable R)
    (principalTimeKernel_first_moment R hR).1 (principalTimeKernel_first_moment R hR).2

end LipschitzHilbert.PacketRepresentation

end

end OAI
