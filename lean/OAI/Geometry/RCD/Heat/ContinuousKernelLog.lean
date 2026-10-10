import OAI.Geometry.RCD.Transport.PositiveExponentialTilt
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Continuous logarithmic transforms on compact endpoint supports

The endpoint measures are probabilities. A uniformly positive continuous
kernel sends every continuous logarithmic weight to a continuous finite
logarithmic weight. These are the maps used for the scaling fixed point.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [CompactSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure Y) [IsProbabilityMeasure μ]

theorem continuous_exp_integrable (g : C(Y, ℝ)) : Integrable (fun y => Real.exp (g y)) μ := by
  have h := bounded_exp_mul_integrable μ (integrable_const (1 : ℝ)) g.continuous.measurable
    (M := ‖g‖₊) (fun y => g.norm_coe_le_norm y) 1
  simpa only [one_mul,mul_one] using h

theorem continuous_exp_integral_pos (g : C(Y, ℝ)) : 0 < ∫ y, Real.exp (g y) ∂μ := by
  have h := exponential_tilt_mass_pos μ (integrable_const (1 : ℝ))
    (Eventually.of_forall fun _ => zero_le_one)
    (show (0 : ℝ) < ∫ _ : Y, (1 : ℝ) ∂μ by simp)
    g.continuous.measurable (M := ‖g‖₊) (fun y => g.norm_coe_le_norm y) 1
  simpa only [one_mul,mul_one] using h

theorem continuous_kernel_exp_integral_pos (K : C(X × Y, ℝ)) (g : C(Y, ℝ))
    {m : ℝ} (hm : 0 < m) (hK : ∀ x y, m ≤ K (x,y)) (x : X) :
    0 < ∫ y, K (x,y)*Real.exp (g y) ∂μ := by
  have hki : Integrable (fun y => K (x,y)*Real.exp (g y)) μ :=
    (continuous_exp_integrable μ g).bdd_mul
      (K.continuous.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable
      (Eventually.of_forall fun y => K.norm_coe_le_norm (x,y))
  have hh := integral_mono_ae ((continuous_exp_integrable μ g).const_mul m) hki
    (Eventually.of_forall fun y =>
      mul_le_mul_of_nonneg_right (hK x y) (Real.exp_pos _).le)
  rw [integral_const_mul] at hh
  exact (mul_pos hm (continuous_exp_integral_pos μ g)).trans_le hh

def continuousKernelLog (K : C(X × Y, ℝ)) {m : ℝ} (hm : 0 < m)
    (hK : ∀ x y, m ≤ K (x,y)) (g : C(Y, ℝ)) : C(X, ℝ) where
  toFun x := Real.log (∫ y, K (x,y)*Real.exp (g y) ∂μ)
  continuous_toFun := by
    have hc : Continuous (fun x => ∫ y, K (x,y)*Real.exp (g y) ∂μ) := by
      have h := continuous_parametric_integral_of_continuous (μ := μ)
        (f := fun x y => K (x,y)*Real.exp (g y))
        (by
          exact K.continuous.mul
            (Real.continuous_exp.comp (g.continuous.comp continuous_snd))) isCompact_univ
      simpa only [Measure.restrict_univ] using h
    exact hc.log (fun x => (continuous_kernel_exp_integral_pos μ K g hm hK x).ne')

end RegularPointCoordinates

end

end OAI
