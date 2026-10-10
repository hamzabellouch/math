import OAI.Probability.InvariantIsing.Gaussian.GaussianGramResolvent

namespace OAI

/-! The positive rank-one inverse identity used by the Gaussian leave-one-column resolvent. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma positive_rankOne_inverse {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef)
    (x : Fin N → ℝ) :
    (A+vecMulVec x x)⁻¹ = A⁻¹-(1+x ⬝ᵥ (A⁻¹ *ᵥ x))⁻¹ •
      vecMulVec (A⁻¹ *ᵥ x) (A⁻¹ *ᵥ x) := by
  let R := A⁻¹
  let u := R *ᵥ x
  let q := x ⬝ᵥ u
  have hq : 0 < 1+q := by
    have h := hA.inv.posSemidef.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at h
    change 0 ≤ q at h
    linarith
  have hR : Rᵀ = R := by
    simpa only [R,Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hA.inv.isHermitian
  have hxR : x ᵥ* R = u := by
    calc
      _ = x ᵥ* Rᵀ := congrArg (fun M => x ᵥ* M) hR.symm
      _ = _ := Matrix.vecMul_transpose R x
  have hAR : A*R = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hAx : A *ᵥ u = x := by
    change A *ᵥ (R *ᵥ x) = x
    rw [Matrix.mulVec_mulVec,hAR,Matrix.one_mulVec]
  have h₁ : (A+vecMulVec x x)*R = 1+vecMulVec x u := by
    rw [add_mul,hAR,Matrix.vecMulVec_mul,hxR]
  have h₂ : (A+vecMulVec x x)*vecMulVec u u = (1+q) • vecMulVec x u := by
    rw [add_mul,Matrix.mul_vecMulVec,hAx,Matrix.vecMulVec_mul_vecMulVec,Matrix.vecMulVec_smul]
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
    dsimp only [q]
    ring
  apply Matrix.inv_eq_right_inv
  change (A+vecMulVec x x)*(R-(1+q)⁻¹ • vecMulVec u u) = 1
  rw [mul_sub,mul_smul_comm,h₁,h₂,smul_smul,inv_mul_cancel₀ hq.ne',one_smul]
  exact add_sub_cancel_right 1 (vecMulVec x u)

end InvariantIsing

end

end OAI
