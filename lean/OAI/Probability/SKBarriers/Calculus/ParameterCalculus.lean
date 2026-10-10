import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterSpace

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

def parameter : (n : ℕ) → ParameterSpace n →L[ℝ] ℝ
  | 0 => ContinuousLinearMap.id ℝ ℝ
  | n+1 => (parameter n).comp (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)

def parameterAxis : (n : ℕ) → ParameterSpace n
  | 0 => 1
  | n+1 => (parameterAxis n, 0)

@[simp] theorem parameter_axis (n : ℕ) : parameter n (parameterAxis n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

@[simp] theorem coordinateSquare_axis (n : ℕ) : coordinateSquare n (parameterAxis n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [coordinateSquare, parameterAxis, pow_two, mul_zero, add_zero] using ih

def cubeIntegral : (n : ℕ) → (ParameterSpace n → ℝ) → ℝ → ℝ → ℝ → ℝ
  | 0, f, _, _ => f
  | n+1, f, a, b => cubeIntegral n (fun x => ∫ y in a..b, f (x,y)) a b

def parameterDerivative (n : ℕ) (f : ParameterSpace n → ℝ) (z : ParameterSpace n) : ℝ :=
  fderiv ℝ f z (parameterAxis n)

theorem contDiff_cubeIntegral (n r : ℕ) (f : ParameterSpace n → ℝ)
    (hf : ContDiff ℝ r f) (a b : ℝ) : ContDiff ℝ r (cubeIntegral n f a b) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih _ (contDiff_intervalIntegral r f hf a b)

theorem parameterDerivative_intervalIntegral (n : ℕ) (f : ParameterSpace (n+1) → ℝ)
    (hf : ContDiff ℝ 1 f) (a b : ℝ) (x : ParameterSpace n) :
    parameterDerivative n (fun x => ∫ y in a..b, f (x,y)) x =
      ∫ y in a..b, parameterDerivative (n+1) f (x,y) := by
  let f₁ : ParameterSpace n × ℝ → ParameterSpace n →L[ℝ] ℝ := fun z =>
    (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ (ParameterSpace n) ℝ)
  have hf₁ : Continuous f₁ := (hf.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hd (x : ParameterSpace n) (y : ℝ) : HasFDerivAt (fun z => f (z,y)) (f₁ (x,y)) x := by
    exact (hf.differentiable (by norm_num) (x,y)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
  have hI := hasFDerivAt_intervalIntegral (fun x y => f (x,y)) (fun x y => f₁ (x,y))
    hf.continuous hf₁ hd a b x
  have hInt : IntervalIntegrable (fun y => f₁ (x,y)) volume a b :=
    (hf₁.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  rw [parameterDerivative, hI.fderiv, ContinuousLinearMap.intervalIntegral_apply hInt]
  rfl

theorem hasDerivAt_cubeIntegral (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : ContDiff ℝ 1 f) (a b x : ℝ) :
    HasDerivAt (cubeIntegral n f a b) (cubeIntegral n (parameterDerivative n f) a b x) x := by
  induction n with
  | zero => exact (hf.differentiable (by norm_num) x).hasFDerivAt.hasDerivAt
  | succ n ih =>
    have hh := ih (fun z => ∫ y in a..b, f (z,y)) (contDiff_intervalIntegral 1 f hf a b)
    have he : parameterDerivative n (fun z => ∫ y in a..b, f (z,y)) =
        fun z => ∫ y in a..b, parameterDerivative (n+1) f (z,y) := by
      funext z
      exact parameterDerivative_intervalIntegral n f hf a b z
    rw [he] at hh
    exact hh

end SK.Analytic

end
end
end
end
end

end OAI
