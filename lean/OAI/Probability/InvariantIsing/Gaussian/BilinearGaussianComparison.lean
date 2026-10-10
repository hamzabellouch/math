import OAI.Probability.InvariantIsing.Gaussian.IndexedGaussianMaximum
import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternEuclideanNorm

namespace OAI

/-! The finite bilinear Gaussian comparison behind the sharp rectangular upper edge. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

abbrev BilinearGaussianIndex (N m : ℕ) := ((Fin N × Fin m) ⊕ Unit) ⊕ (Fin N ⊕ Fin m)

def bilinearMatrixCoefficient {X : Type*} {N m : ℕ}
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m))
    (x : X) : BilinearGaussianIndex N m → ℝ
  | .inl (.inl (i,j)) => u x i*v x j
  | .inl (.inr _) => 1
  | .inr _ => 0

def bilinearVectorCoefficient {X : Type*} {N m : ℕ}
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m))
    (x : X) : BilinearGaussianIndex N m → ℝ
  | .inl _ => 0
  | .inr (.inl i) => u x i
  | .inr (.inr j) => v x j

lemma bilinearMatrix_covariance {X : Type*} {N m : ℕ}
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m)) (x y : X) :
    (∑ i, bilinearMatrixCoefficient u v x i*bilinearMatrixCoefficient u v y i) =
      1 + ⟪u x,u y⟫*⟪v x,v y⟫ := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,bilinearMatrixCoefficient,
    mul_zero,one_mul,Finset.sum_const_zero,Fintype.sum_unique,add_zero]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bilinearVector_covariance {X : Type*} {N m : ℕ}
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m)) (x y : X) :
    (∑ i, bilinearVectorCoefficient u v x i*bilinearVectorCoefficient u v y i) =
      ⟪u x,u y⟫+⟪v x,v y⟫ := by
  simp only [Fintype.sum_sum_type,bilinearVectorCoefficient,zero_mul,Finset.sum_const_zero,zero_add,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,mul_comm]

theorem bilinear_gaussian_maximum_comparison {X : Type*} [Fintype X] [Nonempty X] {N m : ℕ}
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ x, ‖v x‖ = 1) :
    (∫ g, indexedGaussianMaximum (bilinearMatrixCoefficient u v) g
      ∂Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)) ≤
    ∫ g, indexedGaussianMaximum (bilinearVectorCoefficient u v) g
      ∂Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1) := by
  apply indexed_gaussian_maximum_comparison
  · intro x y
    simp only [Fintype.sum_sum_type,bilinearMatrixCoefficient,bilinearVectorCoefficient,
      mul_zero,zero_mul,Finset.sum_const_zero,zero_add]
  · intro x
    rw [bilinearVector_covariance,bilinearMatrix_covariance]
    simp only [real_inner_self_eq_norm_sq,hu,hv,one_pow,one_mul]
  · intro x y
    rw [bilinearVector_covariance,bilinearMatrix_covariance]
    have ha : ⟪u x,u y⟫ ≤ 1 := by
      simpa only [hu,mul_one] using real_inner_le_norm (u x) (u y)
    have hb : ⟪v x,v y⟫ ≤ 1 := by
      simpa only [hv,mul_one] using real_inner_le_norm (v x) (v y)
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

end InvariantIsing

end

end OAI
