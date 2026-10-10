import Mathlib
import OAI.Probability.SKSupport.Backward.BackwardGradientSqJointBound
import OAI.Probability.SKSupport.Foundations.MeasurableSpatialDeriv

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma backward_gradient_mild {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (x : ℝ) :
    deriv (backward c b f a) x = varianceHeat (b-a) (deriv f) x+
      c*(∫ r in a..b, varianceHeat (r-a)
        (fun z => deriv (backward c b f r) z*deriv (deriv (backward c b f r)) z) x) := by
  let U : ℝ → ℝ → ℝ := fun r => deriv (backward c b f r)
  let W : ℝ → ℝ → ℝ := fun r => deriv (deriv (backward c b f r))
  have hreg (r : ℝ) : RegularDatum (backward c b f r) := regularDatum_varianceLogHeat hf hLip hc (b-r)
  have hUr (r : ℝ) : BoundedSmooth (U r) := (hreg r).deriv_bounded
  have hUm : Measurable (fun p : ℝ × ℝ => U p.1 p.2) :=
    measurable_spatial_deriv (measurable_backward hf.smooth.continuous.measurable c b)
      (fun r => (hreg r).smooth.differentiable (by simp))
  have hub (r z : ℝ) : |U r z| ≤ 1 := (backward_verificationData hf hLip hc b).gradient_bound r z
  obtain ⟨C,hC⟩ := uniform_varianceLogHeat_derivative_bounds hf hLip hc 1
  have hwb (r z : ℝ) : |W r z| ≤ C := by
    change |deriv (deriv (backward c b f r)) z| ≤ C
    rw [show backward c b f r = varianceLogHeat c (b-r) f from rfl]
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hC (b-r) z
  have hsqreg (r : ℝ) : BoundedSmooth (fun z => (U r z)^2) := by
    simpa only [pow_two] using (hUr r).mul (hUr r)
  have hsqder (r : ℝ) : deriv (fun z => (U r z)^2) = fun z => 2*(U r z*W r z) := by
    funext z
    have hd := ((hUr r).smooth.differentiable (by simp) z).hasDerivAt.pow 2
    convert hd.deriv using 1
    simp only [Nat.cast_ofNat]
    ring
  have hsqbound (r z : ℝ) : |(U r z)^2| ≤ (1:ℝ≥0) := by
    rw [abs_pow]; norm_num only [NNReal.coe_one]
    nlinarith [hub r z,abs_nonneg (U r z)]
  have hsqdb (r z : ℝ) : |deriv (fun z => (U r z)^2) z| ≤ (2*C:ℝ≥0) := by
    rw [hsqder]
    norm_num only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),NNReal.coe_mul,NNReal.coe_ofNat]
    have hh := mul_le_mul (hub r z) (hwb r z) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    nlinarith
  have hDt := hasDerivAt_integral_varianceHeat (hUm.pow_const 2) hsqreg hsqbound hsqdb a b x
  have hHt : HasDerivAt (varianceHeat (b-a) f) (varianceHeat (b-a) (deriv f) x) x :=
    hasDerivAt_scaled_space (hf.smooth.of_le (by simp)) (exponentialBound_of_lipschitz hLip)
      (ExponentialBound.of_bounded (A := 1) (fun z => by
        simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀ := z) hLip)) (Real.sqrt (b-a)) x
  have heFun : backward c b f a = fun z => varianceHeat (b-a) f z+
      (c/2)*(∫ r in a..b, varianceHeat (r-a) (fun y => (U r y)^2) z) :=
    funext (backward_mild hf hLip hc ha hab)
  have hdR : deriv (fun z => varianceHeat (b-a) f z+
      (c/2)*(∫ r in a..b, varianceHeat (r-a) (fun y => (U r y)^2) z)) x =
      varianceHeat (b-a) (deriv f) x+(c/2)*(∫ r in a..b, varianceHeat (r-a) (deriv (fun y => (U r y)^2)) x) :=
    (hHt.add (hDt.const_mul (c/2))).deriv
  rw [heFun,hdR]
  simp_rw [hsqder,varianceHeat_const_mul]
  rw [intervalIntegral.integral_const_mul]
  change varianceHeat (b-a) (deriv f) x + c/2*(2*_) = varianceHeat (b-a) (deriv f) x+c*_
  ring

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
