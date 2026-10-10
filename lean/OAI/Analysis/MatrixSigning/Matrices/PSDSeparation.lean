import Mathlib

namespace OAI

section

namespace KS.W17

open Matrix

def psdCutNormal {n : ℕ} (q : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => -(q i * q j)

def psdCutEval {n : ℕ} (q : Fin n → ℚ) (M : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  -(q ⬝ᵥ (M *ᵥ q))

noncomputable def psdCutEvalReal {n : ℕ} (q : Fin n → ℚ) (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -((fun i => (q i : ℝ)) ⬝ᵥ (M *ᵥ (fun i => (q i : ℝ))))

theorem psdCutEvalReal_cast {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℚ) :
    psdCutEvalReal q (fun i j => (M i j : ℝ)) = (psdCutEval q M : ℝ) := by
  simp [psdCutEvalReal, psdCutEval, dotProduct, Matrix.mulVec,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_neg]

theorem psdCutEvalReal_eq_sum {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    psdCutEvalReal q M = ∑ i, ∑ j, (psdCutNormal q i j : ℝ) * M i j := by
  simp only [psdCutEvalReal, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [psdCutNormal, Rat.cast_neg, Rat.cast_mul]
  ring

theorem psdCutEvalReal_nonpos {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) :
    psdCutEvalReal q M ≤ 0 := by
  have h := hM.dotProduct_mulVec_nonneg (fun i => (q i : ℝ))
  simpa [psdCutEvalReal] using neg_nonpos.mpr h

theorem psdWitness_separates {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hneg : q ⬝ᵥ (M *ᵥ q) < 0) :
    0 < psdCutEvalReal q (fun i j => (M i j : ℝ)) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef → psdCutEvalReal q B ≤ 0 := by
  constructor
  · rw [psdCutEvalReal_cast]
    have hr : 0 < psdCutEval q M := neg_pos.mpr hneg
    exact_mod_cast hr
  · exact fun B hB => psdCutEvalReal_nonpos q B hB

end KS.W17

end

end OAI
