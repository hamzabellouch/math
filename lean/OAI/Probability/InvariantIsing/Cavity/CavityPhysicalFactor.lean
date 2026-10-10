import OAI.Probability.InvariantIsing.Cavity.CavityBlockFactor

namespace OAI

/-! The cavity exponent difference in the original coordinates. The
retained interaction cancels; only the special and cavity projections
enter the factor. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityQuadratic_dotProduct {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    cavityQuadratic A x = (1 / 2 : ℝ) * (x ⬝ᵥ (A *ᵥ x)) := by
  simp only [cavityQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma cavityQuadratic_add {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    cavityQuadratic (A + B) x = cavityQuadratic A x + cavityQuadratic B x := by
  simp only [cavityQuadratic, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma cavityQuadratic_transpose {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    cavityQuadratic A.transpose x = cavityQuadratic A x := by
  rw [cavityQuadratic_dotProduct, cavityQuadratic_dotProduct,
    Matrix.dotProduct_transpose_mulVec]

lemma cavityQuadratic_rectangular {r d n : ℕ}
    (V : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (K : Matrix (Fin d) (Fin n) ℝ) (x : Fin r → ℝ) :
    cavityQuadratic (V * K * E.transpose) x =
      (1 / 2 : ℝ) * ((V.transpose *ᵥ x) ⬝ᵥ (K *ᵥ (E.transpose *ᵥ x))) := by
  rw [cavityQuadratic_dotProduct]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

def cavityPhysicalChange {r d n : ℕ}
    (V : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  V * K * V.transpose + V * L * E.transpose +
    (V * L * E.transpose).transpose + E * C * E.transpose

theorem cavityPhysicalChange_factor {r d n : ℕ}
    (V : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (x : Fin r → ℝ)
    (ε : Spin n) (hε : E.transpose *ᵥ x = fun j => spinValue (ε j)) :
    cavityQuadratic (cavityPhysicalChange V E K L C) x =
      cavityLogFactor K L C (V.transpose *ᵥ x) ε := by
  simp only [cavityPhysicalChange, cavityQuadratic_add, cavityQuadratic_transpose]
  simp only [cavityQuadratic_rectangular, hε]
  rw [cavityLogFactor, cavityQuadratic_dotProduct, cavityQuadratic_dotProduct]
  have he : ((V.transpose *ᵥ x) ⬝ᵥ (L *ᵥ fun j => spinValue (ε j))) =
      ∑ i, ∑ j, (V.transpose *ᵥ x) i * L i j * spinValue (ε j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [he]
  ring

theorem cavityPhysicalChange_energy_difference {r d n : ℕ}
    (Jbase : Matrix (Fin r) (Fin r) ℝ)
    (V : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (x : Fin r → ℝ)
    (ε : Spin n) (hε : E.transpose *ᵥ x = fun j => spinValue (ε j)) :
    cavityQuadratic (Jbase + cavityPhysicalChange V E K L C) x -
      cavityQuadratic Jbase x = cavityLogFactor K L C (V.transpose *ᵥ x) ε := by
  rw [cavityQuadratic_add, add_sub_cancel_left]
  exact cavityPhysicalChange_factor V E K L C x ε hε

end InvariantIsing

end

end OAI
