import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatTimeDerivative
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! Integration by parts transfers Gaussian derivatives to bounded smooth data. -/

noncomputable section
namespace ForcedComputation.PlaneHeat
open Real MeasureTheory Set Filter ShearFlows
open scoped Topology ContDiff

theorem oneDimSecond_integrable {t : ℝ} (ht : 0 < t) : Integrable (oneDimSecond t) := by
  have hm : Integrable (fun x => x^2 * oneDim t x) := by
    convert! (timeMomentTwo_integrable ht).const_mul (timeCoefficient t) using 1
    funext x
    dsimp [timeCoefficient, timeCore, oneDim]
    ring
  convert! (hm.div_const (4*t^2)).sub ((oneDim_integrable ht).const_mul (1/(2*t)))
    using 1
  funext x
  dsimp [oneDimSecond]
  ring

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integrable_weight_smul {w : ℝ → ℝ} (hw : Integrable w) {f : ℝ → F}
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => w x • f x) := by
  apply (hw.norm.mul_const C).mono' (hw.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    change ‖w x • f x‖ ≤ ‖w x‖ * C
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

theorem gaussian_integral_by_parts {t : ℝ} (ht : 0 < t) {f f' : ℝ → F}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (C D : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖f' x‖ ≤ D) :
    (∫ x, oneDimDerivative t x • f x) = -(∫ x, oneDim t x • f' x) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have he := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (u := oneDim t) (v := f) (u' := oneDimDerivative t) (v' := f')
    (fun x _ => oneDim_hasDerivAt ht x) (fun x _ => hf x)
    (integrable_weight_smul F (oneDim_integrable ht) hf' D hD)
    (integrable_weight_smul F (oneDimDerivative_integrable ht) hc C hC)
    (integrable_weight_smul F (oneDim_integrable ht) hc C hC)
  change (∫ x, oneDim t x • f' x) = -(∫ x, oneDimDerivative t x • f x) at he
  simpa only [neg_neg] using congrArg Neg.neg he.symm

theorem gaussian_second_integral_by_parts {t : ℝ} (ht : 0 < t) {f f' f'' : ℝ → F}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') (C D E : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖f' x‖ ≤ D) (hE : ∀ x, ‖f'' x‖ ≤ E) :
    (∫ x, oneDimSecond t x • f x) = ∫ x, oneDim t x • f'' x := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hc' : Continuous f' := continuous_iff_continuousAt.mpr fun x => (hf' x).continuousAt
  have he := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (u := oneDimDerivative t) (v := f) (u' := oneDimSecond t) (v' := f')
    (fun x _ => oneDimDerivative_hasDerivAt ht x) (fun x _ => hf x)
    (integrable_weight_smul F (oneDimDerivative_integrable ht) hc' D hD)
    (integrable_weight_smul F (oneDimSecond_integrable ht) hc C hC)
    (integrable_weight_smul F (oneDimDerivative_integrable ht) hc C hC)
  change (∫ x, oneDimDerivative t x • f' x) = -(∫ x, oneDimSecond t x • f x) at he
  have hb := gaussian_integral_by_parts F ht hf' hf'' D E hD hE
  rw [hb] at he
  exact neg_injective he.symm

end ForcedComputation.PlaneHeat

end

end OAI
