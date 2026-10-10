import OAI.Probability.InvariantIsing.Gaussian.GordonBounds

namespace OAI

/-! Gaussian integration by parts for the joint minimum--maximum Gibbs weight. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

lemma gordon_gaussian_insertion {d : ℕ} (A C : U × V → Fin (d+1) → ℝ) (x : U × V) :
    (∫ g, linearGaussian A g x * gordonWeight (fun y => linearGaussian C g y) x
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) =
    ∫ g, ∑ i, A x i * (gordonWeight (fun y => linearGaussian C g y) x *
      (C x i-2*gordonRowMean (fun y => linearGaussian C g y) (fun y => C y i) x.2+
        gordonMean (fun y => linearGaussian C g y) (fun y => C y i)))
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  let H := fun g : Fin (d+1) → ℝ => fun y => linearGaussian C g y
  have hH (y : U × V) : Continuous (fun g => H g y) := by dsimp [H,linearGaussian]; fun_prop
  have hw : Measurable (fun g => gordonWeight (H g) x) := (continuous_gordonWeight H hH x).measurable
  have hd (i : Fin (d+1)) : Continuous (fun g => gordonWeight (H g) x *
      (C x i-2*gordonRowMean (H g) (fun y => C y i) x.2+gordonMean (H g) (fun y => C y i))) := by
    exact (continuous_gordonWeight H hH x).mul
      ((continuous_const.sub (continuous_const.mul
        (continuous_gordonRowMean H (fun _ y => C y i) hH (fun _ => continuous_const) x.2))).add
          (continuous_gordonMean H (fun _ y => C y i) hH (fun _ => continuous_const)))
  apply gaussian_pi_linear_insertion (A x) hw (fun i => (hd i).measurable)
  · intro i g t
    exact gordonWeight_hasDerivAt (fun y => hasDerivAt_linearGaussian_insert C i g y t) x
  · intro g
    rw [abs_of_nonneg (gordonWeight_nonneg (H g) x)]
    exact gordonWeight_le_one (H g) x
  · intro i g
    apply gordonWeight_derivative_bound (H g) (fun y => C y i) (∑ y, |C y i|)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    intro y
    exact Finset.single_le_sum (fun z _ => abs_nonneg (C z i)) (Finset.mem_univ y)

end InvariantIsing

end

end OAI
