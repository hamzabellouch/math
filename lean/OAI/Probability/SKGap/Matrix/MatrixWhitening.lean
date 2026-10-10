import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype κ] in
lemma positive_sqrt_data {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    ∃ R : Matrix ι ι ℝ, R.IsHermitian ∧ R*R=S ∧ IsUnit R.det := by
  let R := CFC.sqrt S
  have hR : R.IsHermitian := (CFC.sqrt_nonneg S).posSemidef.isHermitian
  have hsq : R*R=S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hu : IsUnit R := isUnit_of_mul_isUnit_left (hsq.symm ▸ hS.isUnit)
  exact ⟨R,hR,hsq,(Matrix.isUnit_iff_isUnit_det R).mp hu⟩

omit [Fintype κ] in

theorem positive_whitening_gram {S : Matrix ι ι ℝ} (hS : S.PosDef)
    (D : Matrix ι ι ℝ) (hD : D.IsHermitian) (V : Matrix ι κ ℝ) :
    ∃ R : Matrix ι ι ℝ, R.IsHermitian ∧ R*R=S ∧ IsUnit R.det ∧
      (R⁻¹*D*V)ᵀ*(R⁻¹*D*V)=Vᵀ*D*S⁻¹*D*V := by
  obtain ⟨R,hR,hsq,hu⟩ := positive_sqrt_data hS
  refine ⟨R,hR,hsq,hu,?_⟩
  have ht : Rᵀ=R := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.eq
  have htD : Dᵀ=D := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.eq
  have hi : R⁻¹*R⁻¹=S⁻¹ := by rw [← hsq,Matrix.mul_inv_rev]
  simp only [Matrix.transpose_mul,Matrix.transpose_nonsing_inv,ht,htD,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc R⁻¹ R⁻¹,hi]

theorem positive_unwhitening {S R D : Matrix ι ι ℝ} (hR : R.IsHermitian)
    (hD : D.IsHermitian) (hRR : R*R=S) (hu : IsUnit R.det)
    (V : Matrix ι κ ℝ) (C : Matrix κ κ ℝ) (δ : ℝ)
    (hpos : ((1-δ) • (1 : Matrix ι ι ℝ)-
      (R⁻¹*D*V)*C*(R⁻¹*D*V)ᵀ).PosDef) :
    ((1-δ) • S-D*V*C*Vᵀ*D).PosDef := by
  have ht : Rᵀ=R := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.eq
  have htD : Dᵀ=D := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.eq
  have hinj : Function.Injective R.mulVec := by
    intro x y hxy
    have h := congrArg (fun z => R⁻¹*ᵥz) hxy
    simpa only [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hu,Matrix.one_mulVec] using h
  have hp := hpos.conjTranspose_mul_mul_same hinj
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial,ht,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hRR] at hp
  convert hp using 1
  congr 1
  simp only [Matrix.transpose_mul,Matrix.transpose_nonsing_inv,ht,htD,Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc R R⁻¹,Matrix.mul_nonsing_inv _ hu,Matrix.one_mul]
  simp only [← Matrix.mul_assoc,Matrix.nonsing_inv_mul_cancel_right _ _ hu]

end SKGap
end
end

end OAI
