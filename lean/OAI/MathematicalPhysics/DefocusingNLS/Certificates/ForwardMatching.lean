import OAI.MathematicalPhysics.DefocusingNLS.Certificates.MatchingColumns

namespace OAI

/-! # Forward matching with its exact scalar factors -/

open Matrix Polynomial

namespace DefocusingNLS

/-- The forward matrix before division by `t-M`. -/
noncomputable def forwardMatrix (M s t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![t, s; -t, t - M - s]

noncomputable def forwardProduct (M s q : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | K + 1 => forwardMatrix M s (q + K) * forwardProduct M s q K

theorem forwardMatrix_step (M s t B C B' C' : ℂ)
    (hB : (t - M) * B' = t * B + s * C) (hC : C' = C - B') :
    forwardMatrix M s t *ᵥ ![B, C] = (t - M) • ![B', C'] := by
  ext i
  fin_cases i
  · simp [forwardMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination -hB
  · simp [forwardMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hC]
    linear_combination hB

/-- Forward and backward matrices compose to precisely `t(t-M) I`. -/
theorem forwardMatrix_mul_backwardMatrix (M s t : ℂ) :
    forwardMatrix M s t * backwardMatrix M s t = (t * (t - M)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [forwardMatrix, backwardMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem backwardMatrix_mul_forwardMatrix (M s t : ℂ) :
    backwardMatrix M s t * forwardMatrix M s t = (t * (t - M)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [forwardMatrix, backwardMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_forwardMatrix (M s t : ℂ) : (forwardMatrix M s t).det = t * (t - M) := by
  simp [forwardMatrix, Matrix.det_fin_two]
  ring

theorem det_backwardMatrix (M s t : ℂ) : (backwardMatrix M s t).det = t * (t - M) := by
  simp [backwardMatrix, Matrix.det_fin_two]
  ring

/-- Iterating forward multiplies the terminal pair by `(q-M)_K`. -/
theorem forwardProduct_apply (M s q : ℂ) (B C : ℕ → ℂ)
    (hB : ∀ n, (q + n - M) * B (n + 1) = (q + n) * B n + s * C n)
    (hC : ∀ n, C (n + 1) = C n - B (n + 1)) (K : ℕ) :
    forwardProduct M s q K *ᵥ ![B 0, C 0] =
      (ascPochhammer ℂ K).eval (q - M) • ![B K, C K] := by
  induction K with
  | zero => simp [forwardProduct]
  | succ K ih =>
      rw [forwardProduct, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
        forwardMatrix_step M s (q + K) _ _ _ _ (hB K) (hC K), smul_smul,
        ascPochhammer_succ_eval]
      congr 1
      ring

end DefocusingNLS

end OAI
