import OAI.MathematicalPhysics.DefocusingNLS.Certificates.MatchingHomotopy

namespace OAI

/-! # Forward transport of the homotopy cone -/

open Matrix Polynomial

namespace DefocusingNLS

theorem forwardProduct_mul_backwardProduct (M s q : ℂ) (K : ℕ) :
    forwardProduct M s q K * backwardProduct M s q K =
      ((ascPochhammer ℂ K).eval q * (ascPochhammer ℂ K).eval (q - M)) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  induction K with
  | zero => simp [forwardProduct, backwardProduct]
  | succ K ih =>
      calc
        _ = forwardMatrix M s (q + K) *
            (forwardProduct M s q K * backwardProduct M s q K) *
              backwardMatrix M s (q + K) := by
                simp only [forwardProduct, backwardProduct, Matrix.mul_assoc]
        _ = ((ascPochhammer ℂ K).eval q * (ascPochhammer ℂ K).eval (q - M)) •
            (forwardMatrix M s (q + K) * backwardMatrix M s (q + K)) := by
              rw [ih, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        _ = _ := by
          rw [forwardMatrix_mul_backwardMatrix, smul_smul,
            ascPochhammer_succ_eval, ascPochhammer_succ_eval]
          congr 1
          ring

theorem forward_backward_apply (M s q : ℂ) (K : ℕ) (v : Fin 2 → ℂ) :
    forwardProduct M s q K *ᵥ (backwardProduct M s q K *ᵥ v) =
      ((ascPochhammer ℂ K).eval q * (ascPochhammer ℂ K).eval (q - M)) • v := by
  rw [Matrix.mulVec_mulVec, forwardProduct_mul_backwardProduct, Matrix.smul_mulVec,
    Matrix.one_mulVec]

theorem forward_matchingHomotopyColumn (M K : ℕ) (s q : ℂ) (ρ : ℝ) :
    forwardProduct M s q K *ᵥ matchingHomotopyColumn M K s ρ q =
      ((ascPochhammer ℂ K).eval q * (ascPochhammer ℂ K).eval (q - M)) •
        ![(ρ : ℂ) * slowTailRatio q (M + 1) K s, 1] :=
  forward_backward_apply M s q K _

/-- The finite forward image of every homotopy column has nonpositive cone.
This is the input used by the counting-boundary Hermitian form. -/
theorem forward_matchingHomotopyColumn_cone (σ : ℝ) (ℓ K : ℕ) (q s : ℂ) (ρ : ℝ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hK : 3 ≤ K)
    (hq : q.re = σ + (ℓ : ℝ) / 2) (hsre : s.re = 0) (hsim : s.im ≠ 0)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    coneForm ((ℓ : ℝ) + 5) s
      ((forwardProduct (ℓ + 5) s q K *ᵥ matchingHomotopyColumn (ℓ + 5) K s ρ q) 0)
      ((forwardProduct (ℓ + 5) s q K *ᵥ matchingHomotopyColumn (ℓ + 5) K s ρ q) 1) ≤ 0 := by
  have h := forward_matchingHomotopyColumn (ℓ + 5) K s q ρ
  push_cast at h
  rw [h]
  change coneForm ((ℓ : ℝ) + 5) s
    (((ascPochhammer ℂ K).eval q * (ascPochhammer ℂ K).eval (q - ((ℓ : ℂ) + 5))) *
      ((ρ : ℂ) * slowTailRatio q (ℓ + 5 + 1) K s))
    (((ascPochhammer ℂ K).eval q * (ascPochhammer ℂ K).eval (q - ((ℓ : ℂ) + 5))) * 1) ≤ 0
  rw [coneForm_scale, show ℓ + 5 + 1 = ℓ + 6 by omega]
  exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _)
    (slowTailRatio_homotopy_cone σ ℓ K q s ρ hσ hK hq hsre hsim hρ hρ1)

/-- Avoiding the explicit forward/backward factors excludes a zero column,
without any assumption about the determinant of the two-channel problem. -/
theorem matchingHomotopyColumn_ne_zero_of_factors (M K : ℕ) (s q : ℂ) (ρ : ℝ)
    (h₁ : (ascPochhammer ℂ K).eval q ≠ 0)
    (h₂ : (ascPochhammer ℂ K).eval (q - M) ≠ 0) :
    matchingHomotopyColumn M K s ρ q ≠ 0 := by
  intro hz
  have h := forward_matchingHomotopyColumn M K s q ρ
  rw [hz, Matrix.mulVec_zero] at h
  have he := congrFun h 1
  change 0 = ((ascPochhammer ℂ K).eval q * (ascPochhammer ℂ K).eval (q - M)) * 1 at he
  rw [mul_one] at he
  exact (mul_ne_zero h₁ h₂) he.symm

end DefocusingNLS

end OAI
