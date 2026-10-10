import OAI.Probability.InvariantIsing.Cavity.CavityBaseReplacement
import OAI.Probability.InvariantIsing.Cavity.CavityRetainedStack

namespace OAI

/-! The replaced interaction preserves retained eigenvectors, gives the
special axes their assigned eigenvalues, and annihilates the cavity. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavityBaseReplacement_retained {r s d : ℕ} {ι : Type*} [Fintype ι]
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) (R : Matrix (Fin r) ι ℝ) (L : Matrix ι ι ℝ)
    (hJR : J * R = R * L) (hWR : W.transpose * R = 0) :
    cavityBaseReplacement J W D B A₀ * R = R * L := by
  simp only [cavityBaseReplacement, Matrix.add_mul, Matrix.sub_mul, Matrix.transpose_mul,
    Matrix.mul_assoc, hWR, Matrix.mul_zero, sub_zero, add_zero, hJR]

lemma cavityBaseReplacement_special {r s d : ℕ}
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hJW : J * W = W * D) (hW : W.transpose * W = 1) (hB : B.transpose * B = 1) :
    cavityBaseReplacement J W D B A₀ * (W * B) = (W * B) * A₀ := by
  have hJB : J * (W * B) = W * D * B := by rw [← Matrix.mul_assoc, hJW]
  have hWB : W.transpose * (W * B) = B := by rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  have hBB : (W * B).transpose * (W * B) = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hWB, hB]
  rw [cavityBaseReplacement, Matrix.add_mul, Matrix.sub_mul, hJB,
    Matrix.mul_assoc (W * D) W.transpose (W * B), hWB, sub_self, zero_add,
    Matrix.mul_assoc (W * B * A₀) (W * B).transpose (W * B), hBB, Matrix.mul_one]

lemma cavityBaseReplacement_cavity {r s d n : ℕ}
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (E : Matrix (Fin s) (Fin n) ℝ) (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hJW : J * W = W * D) (hW : W.transpose * W = 1) (hBE : B.transpose * E = 0) :
    cavityBaseReplacement J W D B A₀ * (W * E) = 0 := by
  have hJE : J * (W * E) = W * D * E := by rw [← Matrix.mul_assoc, hJW]
  have hWE : W.transpose * (W * E) = E := by rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  have hBB : (W * B).transpose * (W * E) = 0 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hWE, hBE]
  rw [cavityBaseReplacement, Matrix.add_mul, Matrix.sub_mul, hJE,
    Matrix.mul_assoc (W * D) W.transpose (W * E), hWE, sub_self, zero_add,
    Matrix.mul_assoc (W * B * A₀) (W * B).transpose (W * E), hBB, Matrix.mul_zero]

lemma cavityBaseReplacement_conjugate {r s d : ℕ}
    (J U : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    cavityBaseReplacement (U * J * U.transpose) (U * W) D B A₀ =
      U * cavityBaseReplacement J W D B A₀ * U.transpose := by
  simp only [cavityBaseReplacement, Matrix.transpose_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

end InvariantIsing

end

end OAI
