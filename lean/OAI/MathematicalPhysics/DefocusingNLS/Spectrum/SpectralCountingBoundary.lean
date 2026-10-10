import OAI.MathematicalPhysics.DefocusingNLS.Certificates.UniformHorizontalExclusion
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryMatchingExclusion

namespace OAI

/-! # A uniform zero-free counting boundary for the true tail homotopy -/

namespace DefocusingNLS

attribute [local irreducible] matchingHomotopyColumn matchingColumnDeterminant

noncomputable def spectralQ (ell : ℕ) (h b : ℝ) (z : ℂ) : ℂ :=
  z + (ell : ℂ) / 2 - (h : ℂ) * Complex.I * b

noncomputable def spectralHomotopyDeterminant (ell : ℕ) (b Z ρ : ℝ) (z : ℂ) : ℂ :=
  matchingColumnDeterminant
    (matchingHomotopyColumn (ell + 5) 8 (Complex.I * Z) ρ (spectralQ ell 1 b z))
    (matchingHomotopyColumn (ell + 5) 8 (-Complex.I * Z) ρ (spectralQ ell (-1) b z))

theorem spectralQ_eq_horizontal (ell : ℕ) (h b : ℝ) (z : ℂ) :
    spectralQ ell h b z = horizontalQ ell h z.re b z.im := by
  apply Complex.ext <;> simp [spectralQ, horizontalQ, Complex.mul_re, Complex.mul_im]

theorem spectralHomotopyDeterminant_horizontal (ell : ℕ) (b Z ρ : ℝ) (z : ℂ) :
    spectralHomotopyDeterminant ell b Z ρ z =
      matchingColumnDeterminant
        (matchingHomotopyColumn (ell + 5) 8 ((1 : ℂ) * Complex.I * Z) ρ
          (horizontalQ ell 1 z.re b z.im))
        (matchingHomotopyColumn (ell + 5) 8 ((-1 : ℂ) * Complex.I * Z) ρ
          (horizontalQ ell (-1) z.re b z.im)) := by
  simp only [spectralHomotopyDeterminant, spectralQ_eq_horizontal, one_mul, neg_mul]

theorem spectralHomotopyDeterminant_left (ell : Fin 4) (b Z ρ : ℝ) (z : ℂ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hz : z.re = -(1 / 32 : ℝ)) :
    spectralHomotopyDeterminant ell b Z ρ z ≠ 0 := by
  have hq (h : ℝ) : spectralQ ell h b z = BoundaryCertificate.boundaryQ ell (h * b) z.im := by
    apply Complex.ext <;>
      simp [spectralQ, BoundaryCertificate.boundaryQ, hz, Complex.mul_re, Complex.mul_im]
    all_goals ring
  simpa only [spectralHomotopyDeterminant, hq, one_mul, neg_one_mul] using
    BoundaryCertificate.matchingHomotopy_left_boundary_ne_zero ell b Z z.im ρ hb hZ hρ hρ1

theorem spectralHomotopyDeterminant_right (ell : Fin 4) (b Z ρ : ℝ) (z : ℂ)
    (hZ : Z ≠ 0) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hz : 8 ≤ z.re) :
    spectralHomotopyDeterminant ell b Z ρ z ≠ 0 := by
  have hbound : (ell : ℝ) < 4 := by exact_mod_cast ell.isLt
  have hq (h : ℝ) : (ell : ℝ) + 5 < (spectralQ ell h b z).re := by
    simp [spectralQ, Complex.mul_re, Complex.mul_im]
    linarith
  unfold spectralHomotopyDeterminant
  simpa only [neg_mul] using matchingHomotopy_right_ne_zero ell 8 (Complex.I * Z)
    (spectralQ ell 1 b z) (spectralQ ell (-1) b z) ρ (by decide) (by simp)
    (by simpa using hZ) (hq 1) (hq (-1)) hρ hρ1

/-- The same height controls every larger rectangle to the right, because
points beyond real part eight already lie in the excluded right half-plane. -/
theorem exists_spectral_counting_boundary (ell : Fin 4) :
    ∃ V : ℝ, 0 < V ∧ ∀ b Z ρ : ℝ, ∀ z : ℂ,
      |100000000 * b - 33477607| ≤ 2 → |100000000 * Z - 270506819| ≤ 2 →
      0 ≤ ρ → ρ ≤ 1 →
      (z.re = -(1 / 32 : ℝ) ∨ 8 ≤ z.re ∨
        (-(1 / 32 : ℝ) ≤ z.re ∧ V < |z.im|)) →
      spectralHomotopyDeterminant ell b Z ρ z ≠ 0 := by
  obtain ⟨V, hV, he⟩ := exists_uniform_horizontal_exclusion ell 8
    (33477605 / 100000000) (33477609 / 100000000)
    (270506817 / 100000000) (270506821 / 100000000) (by norm_num)
  refine ⟨V, hV, ?_⟩
  intro b Z ρ z hb hZ hρ hρ1 hedge
  have hb' : b ∈ Set.Icc (33477605 / 100000000 : ℝ) (33477609 / 100000000) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hb
    constructor <;> linarith
  have hZ' : Z ∈ Set.Icc (270506817 / 100000000 : ℝ) (270506821 / 100000000) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hZ
    constructor <;> linarith
  have hZ0 : Z ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hZ'.1)
  rcases hedge with hleft | hright | ⟨hlo, hheight⟩
  · exact spectralHomotopyDeterminant_left ell b Z ρ z hb hZ hρ hρ1 hleft
  · exact spectralHomotopyDeterminant_right ell b Z ρ z hZ0 hρ hρ1 hright
  · by_cases hright : 8 ≤ z.re
    · exact spectralHomotopyDeterminant_right ell b Z ρ z hZ0 hρ hρ1 hright
    · rw [spectralHomotopyDeterminant_horizontal]
      exact he z.re b Z z.im ρ ⟨hlo, (lt_of_not_ge hright).le⟩ hb' hZ' hheight hρ hρ1

end DefocusingNLS

end OAI
