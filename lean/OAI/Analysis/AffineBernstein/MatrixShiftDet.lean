import Mathlib
import OAI.Analysis.AffineBernstein.MatrixShiftBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma det_le_det_add_one {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : A.det ≤ (A+1).det := by
  let Q : Matrix ι ι ℝ := hA.1.eigenvectorUnitary
  let d : ι → ℝ := hA.1.eigenvalues
  have hQ : Q*Qᵀ = 1 := by
    simpa only [Q,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Unitary.coe_mul_star_self hA.1.eigenvectorUnitary)
  have hspec : A = Q * Matrix.diagonal d * Qᵀ := by
    simpa [Q,d,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hA.1.spectral_theorem
  have hdetQ : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] using hh
  have hsum : A+1 = Q * Matrix.diagonal (fun i => d i+1) * Qᵀ := by
    have he : Matrix.diagonal (fun i => d i+1) = Matrix.diagonal d+1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal,hij]
    rw [he,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,← hspec,hQ]
  rw [hsum,hspec,Matrix.det_mul,Matrix.det_mul,Matrix.det_mul,Matrix.det_mul,
    Matrix.det_transpose,Matrix.det_diagonal,Matrix.det_diagonal]
  have he (a : ℝ) : Q.det * a * Q.det = a := by
    calc
      _ = (Q.det*Q.det)*a := by ring
      _ = a := by rw [hdetQ,one_mul]
  rw [he,he]
  exact Finset.prod_le_prod₀ (fun index _ => hA.eigenvalues_nonneg index)
    (fun _ _ => by linarith)

lemma det_mul_one_add_trace_inv_le {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    A.det * (1 + A⁻¹.trace) ≤ ((Fintype.card ι:ℝ)+1)*(A+1).det := by
  have hne := hA.det_pos.ne'
  have he : A.det * A⁻¹.trace = A.adjugate.trace := by
    rw [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.trace_smul,
      smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hne,one_mul]
  rw [mul_add,mul_one,he]
  have h1 := det_le_det_add_one hA.posSemidef
  have h2 := trace_adjugate_le_card_mul_det_add_one hA.posSemidef
  linarith

end AffineBernstein
end

end OAI
