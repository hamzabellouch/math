import Mathlib
import OAI.Analysis.AffineBernstein.CapCovariance
import OAI.Analysis.AffineBernstein.QuadraticIntegration

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ConstantHessianQuadratic

lemma second_fderiv_bilinear_eq_sum {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : Space n) :
    fderiv ℝ (fderiv ℝ u) x v w = ∑ i, ∑ j, v i*hessian u x i j*w j := by
  calc
    _ = fderiv ℝ (fderiv ℝ u) x (∑ i, v i • coordinateVector n i)
        (∑ j, w j • coordinateVector n j) := by rw [sum_coordinateVector,sum_coordinateVector]
    _ = _ := by
      simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hessian_eq_second hu]
      ring

lemma quadratic_of_constant_hessian {n : ℕ} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hH : ∀ x y, hessian u x=hessian u y) :
    ∀ x, u x = (1/2:ℝ)*(∑ i, ∑ j, x i*hessian u 0 i j*x j)+fderiv ℝ u 0 x+u 0 := by
  have he : fderiv ℝ (fderiv ℝ u) = fun _ => fderiv ℝ (fderiv ℝ u) 0 := by
    funext x
    ext v w
    rw [second_fderiv_bilinear_eq_sum hu.contDiffAt,second_fderiv_bilinear_eq_sum hu.contDiffAt,hH x 0]
  have ht (x : Space n) : fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x=0 := by
    rw [he]
    simp
  intro x
  rw [quadratic_of_third_fderiv_zero u (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)) ht x,second_fderiv_eq_sum hu.contDiffAt]

lemma continuousLinearMap_coordinate_sum {n : ℕ} (L : Space n →L[ℝ] ℝ) (x : Space n) :
    L x=∑ i, L (coordinateVector n i)*x i := by
  calc
    _ = L (∑ i, x i • coordinateVector n i) := by rw [sum_coordinateVector]
    _ = _ := by simp only [map_sum,map_smul,smul_eq_mul,mul_comm]

end ConstantHessianQuadratic


end
end AffineBernstein
end

end OAI
