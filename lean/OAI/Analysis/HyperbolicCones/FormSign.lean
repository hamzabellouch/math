import OAI.Analysis.HyperbolicCones.FormRigidity

namespace OAI

/-! The sign-vector coefficient identity for the Choi–Lam form. -/

noncomputable section

namespace Paper256

theorem form_sign_expansion
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (σ : Fin 3 → ℝ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    l σ σ = (∑ i, l (Pi.single i 1) (Pi.single i 1)) +
      (l (Pi.single 0 1) (Pi.single 1 1) + l (Pi.single 1 1) (Pi.single 0 1)) * σ 0 * σ 1 +
      (l (Pi.single 0 1) (Pi.single 2 1) + l (Pi.single 2 1) (Pi.single 0 1)) * σ 0 * σ 2 +
      (l (Pi.single 1 1) (Pi.single 2 1) + l (Pi.single 2 1) (Pi.single 1 1)) * σ 1 * σ 2 := by
  have hs (i : Fin 3) : σ i ^ 2 = 1 := by
    rcases hσ i with hi | hi <;> simp [hi]
  rw [form_bilinear_coordinates]
  simp [Fin.sum_univ_succ]
  linear_combination
    l (Pi.single 0 1) (Pi.single 0 1) * hs 0 +
    l (Pi.single 1 1) (Pi.single 1 1) * hs 1 +
    l (Pi.single 2 1) (Pi.single 2 1) * hs 2

theorem dominated_form_sign_relation
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y)
    (σ : Fin 3 → ℝ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    0 = (∑ i, l (Pi.single i 1) (Pi.single i 1)) +
      (l (Pi.single 0 1) (Pi.single 1 1) + l (Pi.single 1 1) (Pi.single 0 1)) * σ 0 * σ 1 +
      (l (Pi.single 0 1) (Pi.single 2 1) + l (Pi.single 2 1) (Pi.single 0 1)) * σ 0 * σ 2 +
      (l (Pi.single 1 1) (Pi.single 2 1) + l (Pi.single 2 1) (Pi.single 1 1)) * σ 1 * σ 2 := by
  rw [← form_sign_expansion l σ hσ]
  exact (dominated_form_sign_zero l h σ hσ).symm

end Paper256

end

end OAI
