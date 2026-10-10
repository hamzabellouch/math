import OAI.Probability.SignedSweeps.EvenDensity
import OAI.Probability.SignedSweeps.WordTensorBasis

namespace OAI

noncomputable section
namespace SignedSweeps.EvenColorDensity
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) evenMeanSumDecidableEq {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _
variable {C J : Type*} [Fintype C] [Fintype J] [Nonempty J]

def mean (R : J → EvenColorDensity C) : EvenColorDensity C where
  even := Complex.ofReal ((Fintype.card J : ℝ)⁻¹) • ∑ j, (R j).even
  odd := Complex.ofReal ((Fintype.card J : ℝ)⁻¹) • ∑ j, (R j).odd
  even_positive := (Matrix.posSemidef_sum _ (fun j _ => (R j).even_positive)).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _)))
  odd_positive := (Matrix.posSemidef_sum _ (fun j _ => (R j).odd_positive)).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _)))
  trace_one := by
    simp only [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]
    rw [← mul_add, ← Finset.sum_add_distrib]
    simp only [EvenColorDensity.trace_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma mean_matrix (R : J → EvenColorDensity C) :
    (mean R).matrix = (Fintype.card J : ℂ)⁻¹ • ∑ j, (R j).matrix := by
  ext i k
  cases i <;> cases k <;>
    simp [mean, matrix, Matrix.smul_apply, Matrix.sum_apply, Complex.ofReal_inv]

lemma matrix_trace (R : EvenColorDensity C) : R.matrix.trace.re = 1 := by
  simpa [Matrix.trace, Fintype.sum_sum_type, matrix, Complex.add_re] using R.trace_one

lemma matrix_trace_linear (R : EvenColorDensity C) :
    (LinearMap.trace ℂ (EuclideanSpace ℂ (C ⊕ C)) R.matrix.toEuclideanLin).re = 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (C ⊕ C) ℂ).toBasis]
  change (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (C ⊕ C) ℂ)
    R.matrix.toEuclideanLin).trace.re = 1
  rw [matrix_orthonormal_coordinates, matrix_trace]

lemma mean_linear (R : J → EvenColorDensity C) :
    (mean R).matrix.toEuclideanLin = densityMean (fun j => (R j).matrix.toEuclideanLin) := by
  rw [mean_matrix]
  change (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (C ⊕ C) ℂ)).symm
      ((Fintype.card J : ℂ)⁻¹ • ∑ j, (R j).matrix) = _
  rw [map_smul, map_sum]
  rfl

end SignedSweeps.EvenColorDensity
end

end OAI
