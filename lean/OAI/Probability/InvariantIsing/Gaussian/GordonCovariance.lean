import OAI.Probability.InvariantIsing.Gaussian.GordonGaussianInsertion

namespace OAI

/-! Covariance contraction of the two-level Gaussian integration-by-parts identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

omit [Nonempty U] [Fintype V] [Nonempty V] in
lemma gordonRowMean_linear_sum {d : ℕ} (H : U × V → ℝ) (C : U × V → Fin d → ℝ)
    (a : Fin d → ℝ) (v : V) :
    (∑ i, a i*gordonRowMean H (fun y => C y i) v) =
      ∑ u, gordonInner H u v*(∑ i, a i*C (u,v) i) := by
  simp only [gordonRowMean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Nonempty U] [Nonempty V] in
lemma gordonMean_linear_sum {d : ℕ} (H : U × V → ℝ) (C : U × V → Fin d → ℝ)
    (a : Fin d → ℝ) :
    (∑ i, a i*gordonMean H (fun y => C y i)) =
      ∑ y, gordonWeight H y*(∑ i, a i*C y i) := by
  simp only [gordonMean_eq_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Nonempty U] [Nonempty V] in
lemma gordon_covariance_contraction {d : ℕ} (H : U × V → ℝ)
    (A C : U × V → Fin d → ℝ) (x : U × V) :
    (∑ i, A x i*(gordonWeight H x*(C x i-2*gordonRowMean H (fun y => C y i) x.2+
      gordonMean H (fun y => C y i)))) =
    gordonWeight H x*(gaussianCross A C x x-
      2*(∑ u, gordonInner H u x.2*gaussianCross A C x (u,x.2))+
      ∑ y, gordonWeight H y*gaussianCross A C x y) := by
  calc
    _ = gordonWeight H x * ∑ i, (A x i*C x i-
        2*(A x i*gordonRowMean H (fun y => C y i) x.2)+
        A x i*gordonMean H (fun y => C y i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = gordonWeight H x*((∑ i, A x i*C x i)-
        2*(∑ i, A x i*gordonRowMean H (fun y => C y i) x.2)+
        ∑ i, A x i*gordonMean H (fun y => C y i)) := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    _ = _ := by rw [gordonRowMean_linear_sum,gordonMean_linear_sum]; rfl

theorem gordon_gaussian_covariance_insertion {d : ℕ} (A C : U × V → Fin (d+1) → ℝ)
    (x : U × V) :
    (∫ g, linearGaussian A g x*gordonWeight (fun y => linearGaussian C g y) x
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) =
    ∫ g, gordonWeight (fun y => linearGaussian C g y) x*(gaussianCross A C x x-
      2*(∑ u, gordonInner (fun y => linearGaussian C g y) u x.2*gaussianCross A C x (u,x.2))+
      ∑ y, gordonWeight (fun y => linearGaussian C g y) y*gaussianCross A C x y)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  rw [gordon_gaussian_insertion]
  exact integral_congr_ae (ae_of_all _ (fun g => gordon_covariance_contraction _ A C x))

end InvariantIsing

end

end OAI
