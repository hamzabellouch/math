import OAI.Probability.InvariantIsing.Gaussian.IndexedGaussianMinmax
import OAI.Probability.InvariantIsing.Gaussian.BilinearGaussianComparison

namespace OAI

/-! Gordon's finite rectangular Gaussian matrix comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

theorem bilinear_gaussian_minmax_comparison {N m : ℕ}
    (u : U → EuclideanSpace ℝ (Fin N)) (v : V → EuclideanSpace ℝ (Fin m))
    (hu : ∀ a, ‖u a‖ = 1) (hv : ∀ b, ‖v b‖ = 1) :
    (∫ g, finiteMinmax (fun x : U × V => ∑ i,
      bilinearVectorCoefficient (fun x : U × V => u x.1) (fun x => v x.2) x i*g i)
      ∂Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)) ≤
    ∫ g, finiteMinmax (fun x : U × V => ∑ i,
      bilinearMatrixCoefficient (fun x : U × V => u x.1) (fun x => v x.2) x i*g i)
      ∂Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1) := by
  apply indexed_gaussian_minmax_comparison
  · intro x y
    simp only [Fintype.sum_sum_type,bilinearMatrixCoefficient,bilinearVectorCoefficient,
      mul_zero,zero_mul,Finset.sum_const_zero,zero_add]
  · intro x a
    rw [bilinearVector_covariance,bilinearMatrix_covariance]
    simp only [real_inner_self_eq_norm_sq,hv,one_pow,mul_one]
    ring
  · intro x y
    rw [bilinearVector_covariance,bilinearMatrix_covariance]
    have ha : ⟪u x.1,u y.1⟫ ≤ 1 := by
      simpa only [hu,mul_one] using real_inner_le_norm (u x.1) (u y.1)
    have hb : ⟪v x.2,v y.2⟫ ≤ 1 := by
      simpa only [hv,mul_one] using real_inner_le_norm (v x.2) (v y.2)
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

end InvariantIsing

end

end OAI
