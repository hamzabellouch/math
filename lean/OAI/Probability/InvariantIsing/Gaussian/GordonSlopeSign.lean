import OAI.Probability.InvariantIsing.Gaussian.GordonCovariance
import OAI.Probability.InvariantIsing.Gaussian.GordonValueBound

namespace OAI

/-! The sign of the Gaussian two-level Gibbs slope when row covariances agree. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

lemma gordon_gaussian_mean_nonpos {d : ℕ} (A C : U × V → Fin (d+1) → ℝ)
    (hrow : ∀ x u, gaussianCross A C x (u,x.2) = 0)
    (hoff : ∀ x y, gaussianCross A C x y ≤ 0) :
    (∫ g, gordonMean (fun y => linearGaussian C g y) (fun y => linearGaussian A g y)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) ≤ 0 := by
  simp_rw [gordonMean_eq_sum]
  rw [integral_finsetSum _ (fun x _ => by
    simpa only [mul_comm] using integrable_gordon_linear A C x)]
  apply Finset.sum_nonpos
  intro x _
  simp only [mul_comm (gordonWeight _ x)]
  rw [gordon_gaussian_covariance_insertion]
  apply integral_nonpos
  intro g
  dsimp only
  have hd : gaussianCross A C x x = 0 := by simpa using hrow x x.1
  have hr : (∑ u, gordonInner (fun y => linearGaussian C g y) u x.2 *
      gaussianCross A C x (u,x.2)) = 0 := by simp only [hrow,mul_zero,Finset.sum_const_zero]
  rw [hd,hr,mul_zero,sub_zero,zero_add]
  apply mul_nonpos_of_nonneg_of_nonpos (gordonWeight_nonneg _ x)
  exact Finset.sum_nonpos (fun y _ =>
    mul_nonpos_of_nonneg_of_nonpos (gordonWeight_nonneg _ y) (hoff x y))

end InvariantIsing

end

end OAI
