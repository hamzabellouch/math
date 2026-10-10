import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace OAI

/-! The exact Euclidean determinant bound for two real covectors on the
complex plane, with constant one. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

 theorem complexCovector_apply (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg L hz
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul]

 theorem complexCovector_dualVector_norm_le (L : ℂ →L[ℝ] ℝ) :
    ‖(L 1 : ℂ) + (L Complex.I : ℂ) * Complex.I‖ ≤ ‖L‖ := by
  let z : ℂ := (L 1 : ℂ) + (L Complex.I : ℂ) * Complex.I
  have hzre : z.re = L 1 := by simp [z]
  have hzim : z.im = L Complex.I := by simp [z]
  have hnorm : ‖z‖ ^ 2 = (L 1) ^ 2 + (L Complex.I) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    ring
  have hval : L z = ‖z‖ ^ 2 := by
    rw [complexCovector_apply, hzre, hzim, hnorm]
    ring
  have hle := L.le_opNorm z
  rw [hval, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hle
  by_cases hz : ‖z‖ = 0
  · change ‖z‖ ≤ ‖L‖
    rw [hz]
    exact norm_nonneg _
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖z‖ ≤ ‖L‖
    nlinarith

 theorem complexCovector_wedge_bound (A B : ℂ →L[ℝ] ℝ) :
    |A 1 * B Complex.I - A Complex.I * B 1| ≤ ‖A‖ * ‖B‖ := by
  let z : ℂ := (B 1 : ℂ) + (B Complex.I : ℂ) * Complex.I
  let w : ℂ := -Complex.I * z
  have hwre : w.re = B Complex.I := by simp [w, z]
  have hwim : w.im = -B 1 := by simp [w, z]
  have hval : A w = A 1 * B Complex.I - A Complex.I * B 1 := by
    rw [complexCovector_apply, hwre, hwim]
    ring
  have hwnorm : ‖w‖ = ‖z‖ := by simp only [w, norm_mul, norm_neg, Complex.norm_I, one_mul]
  calc
    _ = ‖A w‖ := by rw [hval, Real.norm_eq_abs]
    _ ≤ ‖A‖ * ‖w‖ := A.le_opNorm w
    _ = ‖A‖ * ‖z‖ := by rw [hwnorm]
    _ ≤ ‖A‖ * ‖B‖ := mul_le_mul_of_nonneg_left
      (complexCovector_dualVector_norm_le B) (norm_nonneg _)

end CircleDomainRigidity

end

end OAI
