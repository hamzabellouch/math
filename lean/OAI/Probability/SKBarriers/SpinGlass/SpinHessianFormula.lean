import Mathlib
import OAI.Probability.SKBarriers.Scalar.PrefixAlgebra
import OAI.Probability.SKBarriers.Scalar.PathExponentialAverage
import OAI.Probability.SKBarriers.Interpolation.PenaltyGradientBound

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def rootPair (n : ℕ) (m : Fin n → ℝ) (f : ParameterSpace n → ℝ)
    (z : ParameterSpace n) : ℝ :=
  rootGradient n f z*rootGradient n (hierarchyPenalty n m 1 f) z

theorem rootPair_continuous (n : ℕ) (m : Fin n → ℝ) {f : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) : Continuous (rootPair n m f) :=
  (rootGradient_continuous n hf).mul
    (rootGradient_continuous n (hierarchyPenalty_boundedDerivs n m 1 f hf))

theorem rootPair_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (z : ParameterSpace n) : |rootPair n m f z|≤1 := by
  rw [rootPair,abs_mul]
  simpa only [one_mul] using mul_le_mul (h.bounds z).1
    (rootGradient_penalty_bound n m ⟨zero_le_one,le_rfl⟩ (fun i => (hm i).1)
      (fun i => (hm i).2) hmono hf h z) (by positivity) zero_le_one

theorem rootPair_shift_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (z : ParameterSpace n) (t : ℝ) :
    |rootPair n m f (z+t • parameterAxis n)-rootPair n m f z|≤2*|t| := by
  let P := rootGradient n (hierarchyPenalty n m 1 f)
  have hP (w) : |P w|≤1 := rootGradient_penalty_bound n m ⟨zero_le_one,le_rfl⟩
    (fun i => (hm i).1) (fun i => (hm i).2) hmono hf h w
  have hdP : |P (z+t • parameterAxis n)-P z|≤|t| := by
    simpa only [one_mul] using rootGradient_penalty_shift_bound n m ⟨zero_le_one,le_rfl⟩
      (fun i => (hm i).1) (fun i => (hm i).2) hmono hf h z t
  change |rootGradient n f (z+t • parameterAxis n)*P (z+t • parameterAxis n)-
    rootGradient n f z*P z|≤_
  calc
    _ = |(rootGradient n f (z+t • parameterAxis n)-rootGradient n f z)*P (z+t • parameterAxis n)+
        rootGradient n f z*(P (z+t • parameterAxis n)-P z)| := by congr 1; ring
    _ ≤ |(rootGradient n f (z+t • parameterAxis n)-rootGradient n f z)*P (z+t • parameterAxis n)|+
        |rootGradient n f z*(P (z+t • parameterAxis n)-P z)| := abs_add_le _ _
    _ ≤ |t| *1+1*|t| := by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_mul (rootShift_gradient_bound n hf h z t) (hP _) (by positivity) (abs_nonneg _))
        (mul_le_mul (h.bounds z).1 hdP (by positivity) zero_le_one)
    _ = _ := by ring

theorem hierarchyPressure_rootHessian_spin_formula (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (he : ∀ z, rootHessian n f z=1-(rootGradient n f z)^2) (x : ℝ) :
    rootHessian 0 (hierarchyPressure n m f) x=
      1-∫ z, rootPair n m f z ∂hierarchyPathLaw n m f x := by
  have hc := rootPair_continuous n m hf
  have hb := rootPair_bound n m hm hmono hf h
  have hbR : HasExpGrowth (fun z => 1-rootPair n m f z) := HasExpGrowth.of_bounded (by norm_num : (0:ℝ)≤2)
    (fun z => by
      rw [Real.norm_eq_abs]
      calc |1-rootPair n m f z|≤|1|+|rootPair n m f z| := abs_sub _ _
           _ ≤ 2 := by rw [abs_one]; linarith [hb z])
  have hR : rootResponse n m 1 f=fun z => 1-rootPair n m f z := by
    funext z
    rw [rootResponse,he z,rootPair]
    ring
  have hcR : Continuous (fun z => 1-rootPair n m f z) := continuous_const.sub hc
  rw [hierarchyPressure_rootHessian n m 1 hf,hR,
    hierarchyAverage_eq_integral_exp n m f hf _ hcR hbR]
  have iP := hierarchyPathLaw_integrable n m f (rootPair n m f) hf
    hc (fun z => by simpa only [Real.norm_eq_abs] using hb z) x
  let := hierarchyPathLaw_probability n m f hf x
  rw [integral_sub (integrable_const _) iP,integral_const]
  simp

end SK.Analytic

end
end

end OAI
