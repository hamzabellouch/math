import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.SharedBinSupportCollision

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Matrix

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def coneJacobianMatrix (u : ι → ℝ) (r s : ℝ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  let U : Matrix ι Unit ℝ := replicateCol Unit u
  let q := ∑ i, (u i)^2
  fromBlocks ((r*s) • 1 - (r/(4*s)) • (U * U.transpose))
    (s • U) ((-r) • U.transpose) ((1-q/2) • 1)

lemma coneJacobianMatrix_det (u : ι → ℝ) {r s : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hsq : s^2 = 1-(∑ i, (u i)^2)/4) :
    (coneJacobianMatrix u r s).det = (r*s)^(Fintype.card ι) / s^2 := by
  let U : Matrix ι Unit ℝ := replicateCol Unit u
  let q : ℝ := ∑ i, (u i)^2
  let a : ℝ := 1-q/2
  let c : ℝ := s-a/(4*s)
  let L : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
    fromBlocks 1 ((-1/(4*s)) • U) 0 1
  let R : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
    fromBlocks 1 ((-c/(r*s)) • U) 0 1
  have hL : L.det = 1 := by simp [L]
  have hR : R.det = 1 := by simp [R]
  have hq : U.transpose * U = q • (1 : Matrix Unit Unit ℝ) := by
    ext i j
    simp [U,q,Matrix.mul_apply, pow_two]
  have hLT : L * coneJacobianMatrix u r s =
      fromBlocks ((r*s) • (1 : Matrix ι ι ℝ)) (c • U)
        ((-r) • U.transpose) (a • (1 : Matrix Unit Unit ℝ)) := by
    change fromBlocks 1 ((-1/(4*s)) • U) 0 1 *
      fromBlocks ((r*s) • 1 - (r/(4*s)) • (U*U.transpose)) (s • U)
        ((-r) • U.transpose) (a • 1) = _
    rw [fromBlocks_multiply]
    congr 1
    · simp only [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hcoef : (-r) * (-1 / (4*s)) = r/(4*s) := by ring
      rw [hcoef, sub_add_cancel]
    · simp only [Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
      rw [← add_smul]
      congr 1
      dsimp [c]
      ring
    · simp
    · simp
  have hlast : a + (-r) * (-c/(r*s)) * q = 1/s^2 := by
    dsimp [a,c]
    have he : s^2 = 1-q/4 := hsq
    field_simp
    nlinarith [he]
  have hprod : L * coneJacobianMatrix u r s * R =
      fromBlocks ((r*s) • (1 : Matrix ι ι ℝ)) (0 : Matrix ι Unit ℝ)
        ((-r) • U.transpose) ((1/s^2) • (1 : Matrix Unit Unit ℝ)) := by
    rw [hLT]
    dsimp only [R]
    rw [fromBlocks_multiply]
    congr 1
    · simp
    · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
      have hc : (-c/(r*s)) * (r*s) = -c := by field_simp
      rw [hc]
      module
    · simp
    · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hq]
      rw [← add_smul]
      congr 1
      linear_combination hlast
  have hd := congrArg Matrix.det hprod
  rw [det_mul, det_mul, hL, hR, one_mul, mul_one,
    det_fromBlocks_zero₁₂, det_smul, det_one, mul_one, det_smul, det_one] at hd
  simpa [div_eq_mul_inv] using hd

end
end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
