import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ForwardConeTransport

namespace OAI

/-! # A finite-dimensional criterion excluding matching zeros

Positivity of the sum of forward cone forms excludes two dependent nonzero
matching columns with nonpositive individual forms.
-/

open Matrix

namespace DefocusingNLS

theorem matchingColumnDeterminant_eq_zero_imp_smul (u v : Fin 2 → ℂ)
    (hu : u ≠ 0) (hdet : matchingColumnDeterminant u v = 0) :
    ∃ a : ℂ, v = a • u := by
  change u 0 * v 1 - u 1 * v 0 = 0 at hdet
  by_cases h₀ : u 0 = 0
  · have h₁ : u 1 ≠ 0 := by
      intro hz
      apply hu
      ext i
      fin_cases i <;> simp [h₀, hz]
    have hv₀ : v 0 = 0 := by
      rw [h₀, zero_mul, zero_sub, neg_eq_zero] at hdet
      exact (mul_eq_zero.mp hdet).resolve_left h₁
    refine ⟨v 1 / u 1, ?_⟩
    ext i
    fin_cases i <;> simp [h₀, hv₀, h₁]
  · refine ⟨v 0 / u 0, ?_⟩
    ext i
    fin_cases i
    · simp [h₀]
    · change v 1 = (v 0 / u 0) * u 1
      field_simp [h₀]
      linear_combination hdet

noncomputable def matrixCone (M : ℝ) (s : ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℂ) : ℝ := coneForm M s ((T *ᵥ v) 0) ((T *ᵥ v) 1)

theorem matrixCone_smul (M : ℝ) (s a : ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℂ) : matrixCone M s T (a • v) = Complex.normSq a * matrixCone M s T v := by
  simp only [matrixCone, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  exact coneForm_scale M s a _ _

/-- A positive sum of forward forms is incompatible with two dependent
nonzero columns having nonpositive individual forms. -/
theorem matchingColumnDeterminant_ne_zero_of_forward_forms (M : ℝ) (s₁ s₂ : ℂ)
    (T₁ T₂ : Matrix (Fin 2) (Fin 2) ℂ) (u v : Fin 2 → ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (h₁ : matrixCone M s₁ T₁ u ≤ 0) (h₂ : matrixCone M s₂ T₂ v ≤ 0)
    (hpos : ∀ w : Fin 2 → ℂ, w ≠ 0 → 0 < matrixCone M s₁ T₁ w + matrixCone M s₂ T₂ w) :
    matchingColumnDeterminant u v ≠ 0 := by
  intro hdet
  obtain ⟨a, ha⟩ := matchingColumnDeterminant_eq_zero_imp_smul u v hu hdet
  have ha0 : a ≠ 0 := by intro hz; apply hv; simp [ha, hz]
  rw [ha, matrixCone_smul] at h₂
  have h₂' : matrixCone M s₂ T₂ u ≤ 0 := by
    by_contra hn
    have hp : 0 < Complex.normSq a * matrixCone M s₂ T₂ u :=
      mul_pos (Complex.normSq_pos.mpr ha0) (lt_of_not_ge hn)
    linarith
  exact (not_lt_of_ge (add_nonpos h₁ h₂')) (hpos u hu)

end DefocusingNLS

end OAI
