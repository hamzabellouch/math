import Mathlib

namespace OAI

/-! Matrix Trace Inequalities. -/

section

 

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace KaehlerCalculus
variable {n : ℕ}

lemma weighted_trace_cauchy (G E : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosSemidef) :
    ‖(E*G).trace‖^2 ≤ G.trace.re * (E*Eᴴ*G).trace.re := by
  let : SeminormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup G hG
  let : InnerProductSpace ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixInnerProductSpace G hG
  have h := norm_inner_le_norm (𝕜 := ℂ) Eᴴ (1 : Matrix (Fin n) (Fin n) ℂ)
  have hn := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr h
  rw [mul_pow, ← inner_self_eq_norm_sq (𝕜 := ℂ) Eᴴ, ← inner_self_eq_norm_sq (𝕜 := ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)] at hn
  change ‖(1*G*(Eᴴ)ᴴ).trace‖^2 ≤ (Eᴴ*G*(Eᴴ)ᴴ).trace.re *
    ((1 : Matrix (Fin n) (Fin n) ℂ)*G*(1 : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace.re at hn
  simpa only [conjTranspose_conjTranspose,one_mul,conjTranspose_one,mul_one,
    Matrix.trace_mul_comm G E,← Matrix.mul_assoc,
    Matrix.trace_mul_cycle Eᴴ G E,mul_comm] using hn

lemma trace_mul_psd_nonneg {G R : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.PosSemidef) (hR : R.PosSemidef) : 0 ≤ (R*G).trace.re := by
  obtain ⟨B,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg
  have h := (hR.mul_mul_conjTranspose_same B).trace_nonneg
  change 0 ≤ (R*(Bᴴ*B)).trace.re
  rw [Matrix.trace_mul_comm R (Bᴴ*B)]
  rw [Matrix.trace_mul_cycle] at h
  exact (Complex.nonneg_iff.mp h).1

lemma trace_inverse_cycle {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (Z : Matrix (Fin n) (Fin n) ℂ) : (G⁻¹*Z*G).trace = Z.trace := by
  rw [Matrix.trace_mul_cycle,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (ne_of_gt hG.det_pos)),one_mul]

lemma trace_square_completion {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ((X-G⁻¹*Y)*(X-G⁻¹*Y)ᴴ*G).trace =
      (X*Xᴴ*G).trace-(X*Yᴴ).trace-(Xᴴ*Y).trace+(Yᴴ*G⁻¹*Y).trace := by
  have hInv : G⁻¹*G = 1 := Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (ne_of_gt hG.det_pos))
  have he : (X-G⁻¹*Y)*(X-G⁻¹*Y)ᴴ*G =
      X*Xᴴ*G-X*Yᴴ-(G⁻¹*(Y*Xᴴ))*G+G⁻¹*(Y*Yᴴ) := by
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_nonsing_inv,hG.isHermitian.eq]
    simp only [sub_mul,mul_sub,Matrix.mul_assoc,hInv,mul_one]
    noncomm_ring
  rw [he,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_sub,trace_inverse_cycle hG]
  rw [Matrix.trace_mul_comm Y Xᴴ,← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle G⁻¹ Y Yᴴ]

lemma trace_gradient_square_bound {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ‖(Y-X*G).trace‖^2 ≤ G.trace.re *
      ((X*Xᴴ*G).trace.re-(X*Yᴴ).trace.re-(Xᴴ*Y).trace.re+(Yᴴ*G⁻¹*Y).trace.re) := by
  have h := weighted_trace_cauchy G (X-G⁻¹*Y) hG.posSemidef
  rw [trace_square_completion hG,Complex.add_re,Complex.sub_re,Complex.sub_re] at h
  have he : ((X-G⁻¹*Y)*G).trace = -(Y-X*G).trace := by
    rw [sub_mul,Matrix.trace_sub,trace_inverse_cycle hG,Matrix.trace_sub]
    ring
  rw [he,norm_neg] at h
  exact h

end KaehlerCalculus

end
end

end OAI
