import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HorizontalMatchingExclusion

namespace OAI

/-! # A common upper and lower horizontal counting boundary -/

namespace DefocusingNLS

/-- Every sufficiently high horizontal line is free of homotopy zeros,
uniformly over the compact spectral strip and parameter box. -/
theorem exists_uniform_horizontal_exclusion (ell : ℕ) (R b₀ b₁ Z₀ Z₁ : ℝ)
    (hZ₀ : 0 < Z₀) :
    ∃ V : ℝ, 0 < V ∧ ∀ σ b Z v ρ : ℝ,
      σ ∈ Set.Icc (-(1 / 32 : ℝ)) R → b ∈ Set.Icc b₀ b₁ → Z ∈ Set.Icc Z₀ Z₁ →
      V < |v| → 0 ≤ ρ → ρ ≤ 1 →
      matchingColumnDeterminant
        (matchingHomotopyColumn (ell + 5) 8 ((1 : ℂ) * Complex.I * Z) ρ
          (horizontalQ ell 1 σ b v))
        (matchingHomotopyColumn (ell + 5) 8 ((-1 : ℂ) * Complex.I * Z) ρ
          (horizontalQ ell (-1) σ b v)) ≠ 0 := by
  obtain ⟨ε, hε, he⟩ := exists_horizontal_positive_neighborhood ell R b₀ b₁ Z₀ Z₁ hZ₀
  let V : ℝ := ε⁻¹ + |b₀| + |b₁| + 1
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨V, hV, ?_⟩
  intro σ b Z v ρ hσ hb hZ hv hρ hρ1
  have habs : |b| ≤ |b₀| + |b₁| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le b₀, abs_nonneg b₁, hb.1]
    · linarith [le_abs_self b₁, abs_nonneg b₀, hb.2]
  have hbv : |b| < |v| := by
    dsimp [V] at hv
    linarith [inv_pos.mpr hε]
  have hvpos : 0 < |v| := lt_of_le_of_lt (abs_nonneg b) hbv
  have hinv : |v⁻¹| < ε := by
    rw [abs_inv, inv_eq_one_div]
    apply (div_lt_iff₀ hvpos).mpr
    have hbound : 1 / ε < |v| := by
      dsimp [V] at hv
      rw [one_div]
      linarith [abs_nonneg b₀, abs_nonneg b₁]
    have hmul := (div_lt_iff₀ hε).mp hbound
    nlinarith
  apply matchingHomotopy_horizontal_ne_zero_of_form ell σ b Z v ρ hσ.1
    (ne_of_gt (lt_of_lt_of_le hZ₀ hZ.1)) hbv hρ hρ1
  intro B C hBC
  apply horizontalForm_positive_of_unit_sphere ell (v⁻¹) σ b Z _ B C hBC
  intro B' C' hunit
  exact he (v⁻¹) hinv (σ, b, Z, B', C') ⟨hσ, hb, hZ, hunit⟩

end DefocusingNLS

end OAI
