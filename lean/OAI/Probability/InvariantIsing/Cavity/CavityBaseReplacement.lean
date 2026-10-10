import OAI.Probability.InvariantIsing.Cavity.CavityRetainedFrame
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalFactor

namespace OAI

/-! Exact removal and replacement of the small spectral block. The base
matrix is defined without choosing bases in the retained eigenspaces. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityPhysicalChange_sub_special {r d n : ℕ}
    (V : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (A A₀ : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    cavityPhysicalChange V E (A - A₀) L C =
      cavityPhysicalChange V E A L C - V * A₀ * V.transpose := by
  simp only [cavityPhysicalChange, Matrix.mul_sub, Matrix.sub_mul]
  abel

lemma cavityPhysicalChange_pullback {r s d n : ℕ}
    (W : Matrix (Fin r) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (E : Matrix (Fin s) (Fin n) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    cavityPhysicalChange (W * B) (W * E) A L C =
      W * cavityPhysicalChange B E A L C * W.transpose := by
  simp only [cavityPhysicalChange, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc]

lemma cavityPhysicalChange_reconstruct {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (hD : D.transpose = D)
    (B : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (hBE : B * B.transpose + E * E.transpose = 1) :
    cavityPhysicalChange B E (B.transpose * D * B) (B.transpose * D * E)
      (E.transpose * D * E) = D := by
  calc
    _ = (B * B.transpose + E * E.transpose) * D *
        (B * B.transpose + E * E.transpose) := by
      simp only [cavityPhysicalChange, Matrix.transpose_mul, Matrix.transpose_transpose,
        hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      abel
    _ = D := by rw [hBE, Matrix.one_mul, Matrix.mul_one]

def cavityBaseReplacement {r s d : ℕ}
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  J - W * D * W.transpose + (W * B) * A₀ * (W * B).transpose

theorem cavityBaseReplacement_difference {r s d n : ℕ}
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (hD : D.transpose = D)
    (B : Matrix (Fin s) (Fin d) ℝ) (E : Matrix (Fin s) (Fin n) ℝ)
    (hBE : B * B.transpose + E * E.transpose = 1)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    J - cavityBaseReplacement J W D B A₀ =
      cavityPhysicalChange (W * B) (W * E) (B.transpose * D * B - A₀)
        (B.transpose * D * E) (E.transpose * D * E) := by
  rw [cavityPhysicalChange_sub_special, cavityPhysicalChange_pullback,
    cavityPhysicalChange_reconstruct D hD B E hBE, cavityBaseReplacement]
  abel

theorem cavityBaseReplacement_energy_difference {r s d n : ℕ}
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (hD : D.transpose = D)
    (B : Matrix (Fin s) (Fin d) ℝ) (E : Matrix (Fin s) (Fin n) ℝ)
    (hBE : B * B.transpose + E * E.transpose = 1)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) (x : Fin r → ℝ) (ε : Spin n)
    (hε : (W * E).transpose *ᵥ x = fun j => spinValue (ε j)) :
    cavityQuadratic J x - cavityQuadratic (cavityBaseReplacement J W D B A₀) x =
      cavityLogFactor (B.transpose * D * B - A₀) (B.transpose * D * E)
        (E.transpose * D * E) ((W * B).transpose *ᵥ x) ε := by
  rw [← cavityQuadratic_sub, cavityBaseReplacement_difference J W D hD B E hBE A₀]
  exact cavityPhysicalChange_factor _ _ _ _ _ x ε hε

end InvariantIsing

end

end OAI
