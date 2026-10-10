import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open Real MeasureTheory
open scoped BigOperators BoundedContinuousFunction

lemma scalarVariance_cosh (y : ℝ) : (1-tanh y^2)*cosh y^2=1 := by
  rw [tanh_eq_sinh_div_cosh]
  field_simp
  exact cosh_sq_sub_sinh_sq y

lemma square_le_sinh_square (y : ℝ) : y^2 ≤ sinh y^2 := by
  by_cases hy : 0 ≤ y
  · have h := (self_le_sinh_iff).2 hy
    have hs := (sinh_nonneg_iff).2 hy
    nlinarith
  · have h := (sinh_le_self_iff).2 (le_of_not_ge hy)
    have hs := (sinh_nonpos_iff).2 (le_of_not_ge hy)
    nlinarith

lemma scalarVariance_weight_bound (y : ℝ) : (1+y^2)*(1-tanh y^2) ≤ 1 := by
  have hv : 0 ≤ 1-tanh y^2 := sub_nonneg.mpr (tanh_sq_lt_one y).le
  have hb : 1+y^2 ≤ cosh y^2 := by linarith [square_le_sinh_square y,cosh_sq_sub_sinh_sq y]
  have h := mul_le_mul_of_nonneg_right hb hv
  rw [mul_comm (cosh y^2),scalarVariance_cosh] at h
  exact h

lemma weightedScalarMoment_bound (k l : Fin 3) (y : ℝ) :
    |y^(k:ℕ)*tanh y^(l:ℕ)*(1-tanh y^2)| ≤ 1 := by
  have hv : 0 ≤ 1-tanh y^2 := sub_nonneg.mpr (tanh_sq_lt_one y).le
  have ht : |tanh y|^(l:ℕ) ≤ 1 := pow_le_one₀ (abs_nonneg _) (abs_tanh_lt_one y).le
  have hy : |y|^(k:ℕ) ≤ 1+y^2 := by
    fin_cases k
    · simp only [pow_zero]; nlinarith [sq_nonneg y]
    · simp only [pow_one]
      nlinarith [sq_nonneg (|y|-1),sq_abs y]
    · simp only [pow_two,← sq_abs y]; nlinarith [sq_abs y]
  calc
    _ = (|y|^(k:ℕ)*|tanh y|^(l:ℕ))*(1-tanh y^2) := by
      rw [abs_mul,abs_mul,abs_pow,abs_pow,abs_of_nonneg hv]
    _ ≤ (1+y^2)*(1-tanh y^2) := by
      apply mul_le_mul_of_nonneg_right _ hv
      exact (mul_le_mul_of_nonneg_left ht (by positivity)).trans (by simpa using hy)
    _ ≤ 1 := scalarVariance_weight_bound y

def weightedScalarMoment (k l : Fin 3) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => y^(k:ℕ)*tanh y^(l:ℕ)*(1-tanh y^2)) (by
      have ht : Continuous tanh := by
        change Continuous (fun y => tanh y)
        simp_rw [tanh_eq_sinh_div_cosh]
        exact continuous_sinh.div continuous_cosh (fun y => (cosh_pos y).ne')
      fun_prop) (1:ℝ) (fun y => by
        simpa only [Real.norm_eq_abs] using weightedScalarMoment_bound k l y)

lemma continuous_weightedScalarMoment_integral (k l : Fin 3) :
    Continuous (fun P : ProbabilityMeasure ℝ => ∫ y, weightedScalarMoment k l y ∂P) :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction _

end SKGap
end
end

end OAI
