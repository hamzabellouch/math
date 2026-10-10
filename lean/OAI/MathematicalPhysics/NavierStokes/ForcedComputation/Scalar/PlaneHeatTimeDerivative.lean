import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatEquation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatTimeContinuity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatSmoothing

namespace OAI

/-! Time differentiation of Gaussian convolution on bounded continuous data. -/

noncomputable section
namespace ForcedComputation.PlaneHeat

open Real MeasureTheory Set Filter ShearFlows
open scoped Topology ContDiff BigOperators

def timeSecondEnvelope (a b : ℝ) (j : Fin 2) (y : Plane) : ℝ :=
  (y j ^ 2 / (4*a^2) + 1/(2*a)) * timeEnvelope a b y

theorem kernelSecond_time_le {a b s : ℝ} (ha : 0 < a) (has : a ≤ s)
    (hsb : s ≤ b) (j : Fin 2) (y : Plane) :
    |kernelSecond s j y| ≤ timeSecondEnvelope a b j y := by
  have hs : 0 < s := ha.trans_le has
  have hq : y j ^ 2 / (4*s^2) ≤ y j ^ 2 / (4*a^2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith
  have hr : 1/(2*s) ≤ 1/(2*a) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [kernelSecond, abs_mul, abs_of_nonneg (kernel_nonneg _ _)]
  apply mul_le_mul _ (kernel_time_le ha has hsb y) (kernel_nonneg _ _) (by positivity)
  calc
    _ ≤ |y j ^ 2 / (4*s^2)| + |1/(2*s)| := abs_sub _ _
    _ = y j ^ 2 / (4*s^2) + 1/(2*s) := by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ _ := add_le_add hq hr

theorem timeMomentTwo_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : ℝ => y^2 * timeCore b y) := by
  simpa only [Real.rpow_two, timeCore] using
    (integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < (4*b)⁻¹)
      (by norm_num : (-1:ℝ) < 2))

theorem timeSecondEnvelope_integrable (a : ℝ) {b : ℝ} (hb : 0 < b) (j : Fin 2) :
    Integrable (timeSecondEnvelope a b j) := by
  have hm : Integrable (fun y : Plane => y j ^ 2 * timeEnvelope a b y) := by
    fin_cases j
    · convert! (product_integrable (fun y => y^2 * timeCore b y) (timeCore b)
        (timeMomentTwo_integrable hb) (timeCore_integrable hb)).const_mul
        (timeCoefficient a ^ 2) using 1
      funext y
      dsimp [timeEnvelope]
      ring
    · convert! (product_integrable (timeCore b) (fun y => y^2 * timeCore b y)
        (timeCore_integrable hb) (timeMomentTwo_integrable hb)).const_mul
        (timeCoefficient a ^ 2) using 1
      funext y
      dsimp [timeEnvelope]
      ring
  convert! (hm.div_const (4*a^2)).add ((timeEnvelope_integrable a hb).const_mul (1/(2*a)))
    using 1
  funext y
  dsimp [timeSecondEnvelope]
  ring

theorem kernelSecond_continuous (t : ℝ) (j : Fin 2) : Continuous (kernelSecond t j) := by
  unfold kernelSecond
  exact (((continuous_apply j).pow 2).div_const _ |>.sub continuous_const).mul
    (kernel_smooth t).continuous

theorem kernelSecond_integrable {t : ℝ} (ht : 0 < t) (j : Fin 2) :
    Integrable (kernelSecond t j) := by
  apply (timeSecondEnvelope_integrable t ht j).mono'
    (kernelSecond_continuous t j).aestronglyMeasurable
  exact ae_of_all _ fun y => by
    simpa only [Real.norm_eq_abs] using kernelSecond_time_le ht le_rfl le_rfl j y

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem timeIntegrand_integrable {t : ℝ} (ht : 0 < t) (f : Plane → F)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : Plane) :
    Integrable (fun y => kernel t (x-y) • f y) := by
  have hi := BoundedKernel.integrand_integrable Plane F volume (kernel t) f
    (kernel_integrable ht) hf C hC x
  convert! hi.comp_sub_left x using 1
  simp only [sub_sub_self]

theorem hasDerivAt_heatConvolution {t : ℝ} (ht : 0 < t) (f : Plane → F)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : Plane) :
    HasDerivAt (fun s => heatConvolution F s f x)
      (∫ y, (∑ j : Fin 2, kernelSecond t j (x-y)) • f y) t := by
  let a := t/2
  let b := 2*t
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hI : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds hat htb
  have hc (s : ℝ) : Continuous (fun y => (∑ j : Fin 2, kernelSecond s j (x-y)) • f y) :=
    (continuous_finsetSum _ (fun j _ =>
      (kernelSecond_continuous s j).comp (continuous_const.sub continuous_id))).smul hf
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Ioo a b)
    (F' := fun s y => (∑ j : Fin 2, kernelSecond s j (x-y)) • f y)
    (bound := fun y => (∑ j : Fin 2, timeSecondEnvelope a b j (x-y)) * C)
    hI ?_ (timeIntegrand_integrable F ht f hf C hC x)
    (hc t).aestronglyMeasurable ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s =>
      (((kernel_smooth s).continuous.comp (continuous_const.sub continuous_id)).smul hf).aestronglyMeasurable
  · exact ae_of_all _ fun y s hs => by
      rw [norm_smul]
      apply mul_le_mul _ (hC y) (norm_nonneg _) (by
        apply Finset.sum_nonneg
        intro j _
        dsimp [timeSecondEnvelope, timeEnvelope, timeCoefficient, timeCore]
        positivity)
      calc
        ‖∑ j : Fin 2, kernelSecond s j (x-y)‖ ≤
            ∑ j : Fin 2, ‖kernelSecond s j (x-y)‖ := norm_sum_le _ _
        _ ≤ _ := Finset.sum_le_sum fun j _ => by
          simpa only [Real.norm_eq_abs] using
            kernelSecond_time_le ha hs.1.le hs.2.le j (x-y)
  · exact ((integrable_finsetSum _ (fun j _ =>
      (timeSecondEnvelope_integrable a hb j).comp_sub_left x))).mul_const C
  · exact ae_of_all _ fun y s hs =>
      (kernel_time_hasDerivAt (ha.trans hs.1) (x-y)).smul_const (f y)

end ForcedComputation.PlaneHeat

end

end OAI
