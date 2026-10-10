import Mathlib
import OAI.Probability.SKBarriers.Calculus.MarginalPotential

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

@[reducible] def ParameterSpace : ℕ → Type
  | 0 => ℝ
  | n+1 => ParameterSpace n × ℝ

instance parameterNormedGroup : (n : ℕ) → NormedAddCommGroup (ParameterSpace n)
  | 0 => inferInstanceAs (NormedAddCommGroup ℝ)
  | n+1 => letI := parameterNormedGroup n; inferInstanceAs (NormedAddCommGroup (ParameterSpace n × ℝ))

instance parameterNormedSpace : (n : ℕ) → NormedSpace ℝ (ParameterSpace n)
  | 0 => inferInstanceAs (NormedSpace ℝ ℝ)
  | n+1 => letI := parameterNormedSpace n; inferInstanceAs (NormedSpace ℝ (ParameterSpace n × ℝ))

instance parameterFiniteDimensional : (n : ℕ) → FiniteDimensional ℝ (ParameterSpace n)
  | 0 => inferInstanceAs (FiniteDimensional ℝ ℝ)
  | n+1 => letI := parameterFiniteDimensional n; inferInstanceAs (FiniteDimensional ℝ (ParameterSpace n × ℝ))

def coordinateSquare : (n : ℕ) → ParameterSpace n → ℝ
  | 0, _ => 0
  | n+1, z => coordinateSquare n z.1 + z.2^2

@[simp] theorem coordinateSquare_zero (n : ℕ) : coordinateSquare n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change coordinateSquare n (0 : ParameterSpace n) + (0 : ℝ)^2 = 0
    rw [ih]
    norm_num

theorem coordinateSquare_nonneg (n : ℕ) (z : ParameterSpace n) :
    0 ≤ coordinateSquare n z := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact add_nonneg (ih z.1) (sq_nonneg z.2)

def cubePotential : (n : ℕ) → (ParameterSpace n → ℝ) → ℝ → ℝ → ℝ → ℝ
  | 0, V, _, _ => V
  | n+1, V, a, b => cubePotential n (marginalPotential V a b) a b

theorem cubePotential_hessian_lower (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {c : ℝ} (hc : 0 < c)
    (hH : ∀ z u, c * coordinateSquare n u ≤ Hessian V z u u)
    {a b : ℝ} (hab : a < b) :
    ContDiff ℝ 2 (cubePotential n V a b) ∧
      ∀ x u, 0 ≤ Hessian (cubePotential n V a b) x u u := by
  induction n with
  | zero =>
    refine ⟨hV, ?_⟩
    intro x u
    change 0 ≤ Hessian V x u u
    simpa only [coordinateSquare, mul_zero] using hH x u
  | succ n ih =>
    apply ih (marginalPotential V a b) (contDiff_marginalPotential V 2 hV hab)
    intro z u
    apply marginal_hessian_lower V hV (coordinateSquare n) (coordinateSquare_zero n) hc
      (fun z u s => hH z (u,s)) hab

end SK.Analytic

end
end
end
end
end

end OAI
