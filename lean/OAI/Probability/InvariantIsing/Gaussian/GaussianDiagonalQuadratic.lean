import OAI.Probability.InvariantIsing.Gaussian.GaussianFourthMoment

namespace OAI

/-! Exact mean and variance of a diagonal Gaussian quadratic form. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing

def gaussianDiagonalQuadratic {N : ℕ} (a : Fin N → ℝ) (g : Fin N → ℝ) : ℝ := ∑ i, a i*(g i)^2

lemma gaussianDiagonalQuadratic_memLp {N : ℕ} (a : Fin N → ℝ) :
    MemLp (gaussianDiagonalQuadratic a) 2 (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := by
  exact memLp_finsetSum Finset.univ (fun i _ =>
    (gaussianReal_square_memLp.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i)).const_mul (a i))

lemma gaussianDiagonalQuadratic_integrable {N : ℕ} (a : Fin N → ℝ) :
    Integrable (gaussianDiagonalQuadratic a) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := by
  apply integrable_finsetSum
  intro i _
  exact ((gaussianReal_square_memLp.comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i)).const_mul (a i)).integrable (by norm_num)

lemma gaussianDiagonalQuadratic_mean {N : ℕ} (a : Fin N → ℝ) :
    (∫ g, gaussianDiagonalQuadratic a g ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) = ∑ i, a i := by
  unfold gaussianDiagonalQuadratic
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    have h := (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).hasLaw.integral_comp
      (f := fun x : ℝ => x^2) (by fun_prop)
    simpa only [Function.comp_def,Function.eval,gaussianReal_second_moment,mul_one] using
      congrArg (fun x : ℝ => a i*x) h
  · intro i _
    exact ((gaussianReal_square_memLp.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i)).const_mul (a i)).integrable (by norm_num)

lemma gaussianDiagonalQuadratic_variance {N : ℕ} (a : Fin N → ℝ) :
    variance (gaussianDiagonalQuadratic a) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      2*∑ i, (a i)^2 := by
  have h := variance_sum_pi (μ := fun _ : Fin N => gaussianReal 0 1)
    (X := fun i x => a i*x^2) (fun i => gaussianReal_square_memLp.const_mul (a i))
  have he : (∑ i : Fin N, fun g : Fin N → ℝ => a i*(g i)^2) = gaussianDiagonalQuadratic a := by
    funext g
    simp only [Finset.sum_apply,gaussianDiagonalQuadratic]
  rw [he] at h
  rw [h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [variance_const_mul,gaussianReal_square_variance]
  ring

end InvariantIsing

end

end OAI
