import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HorizontalConeIdentity
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HorizontalHomogeneity

namespace OAI

/-! # Horizontal boundary exclusion from the uniform compactified form -/

open Matrix Polynomial

namespace DefocusingNLS

attribute [local irreducible] matchingHomotopyColumn normalizedForwardMatrix horizontalFormAt
  horizontalCone normalizedForwardJet horizontalState horizontalDifference

theorem horizontalQ_im (ell : ℕ) (h σ b v : ℝ) :
    (horizontalQ ell h σ b v).im = v - h * b := by simp [horizontalQ]

theorem horizontalQ_re (ell : ℕ) (h σ b v : ℝ) :
    (horizontalQ ell h σ b v).re = σ + (ell : ℝ) / 2 := by simp [horizontalQ]

theorem horizontalQ_im_ne_zero (ell : ℕ) (h σ b v : ℝ)
    (hh : |h| = 1) (hbv : |b| < |v|) : (horizontalQ ell h σ b v).im ≠ 0 := by
  rw [horizontalQ_im]
  intro hz
  have hvb : v = h * b := sub_eq_zero.mp hz
  rw [hvb, abs_mul, hh, one_mul] at hbv
  exact lt_irrefl _ hbv

theorem horizontalQ_sub_mass_add_ne_zero (ell : ℕ) (h σ b v : ℝ)
    (hh : |h| = 1) (hbv : |b| < |v|) (n : ℕ) :
    horizontalQ ell h σ b v + n - (ell + 5) ≠ 0 := by
  intro hz
  apply horizontalQ_im_ne_zero ell h σ b v hh hbv
  have he := congrArg Complex.im hz
  simpa using he

theorem horizontal_homotopyColumn_ne_zero (ell : ℕ) (h σ b Z v ρ : ℝ)
    (hh : |h| = 1) (hbv : |b| < |v|) :
    matchingHomotopyColumn (ell + 5) 8 ((h : ℂ) * Complex.I * Z) ρ
      (horizontalQ ell h σ b v) ≠ 0 := by
  apply matchingHomotopyColumn_ne_zero_of_factors (ell + 5) 8
    ((h : ℂ) * Complex.I * Z) (horizontalQ ell h σ b v) ρ
  · exact ascPochhammer_eval_ne_zero_of_im_ne_zero _ _
      (horizontalQ_im_ne_zero ell h σ b v hh hbv)
  · apply ascPochhammer_eval_ne_zero_of_im_ne_zero
    simpa using horizontalQ_im_ne_zero ell h σ b v hh hbv

theorem horizontal_homotopy_cone_nonpos (ell : ℕ) (h σ b Z v ρ : ℝ)
    (hh : |h| = 1) (hσ : -(1 / 32 : ℝ) ≤ σ) (hZ : Z ≠ 0)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    matrixCone ((ell : ℝ) + 5) ((h : ℂ) * Complex.I * Z)
      (normalizedForwardMatrix (ell + 5) ((h : ℂ) * Complex.I * Z)
        (horizontalQ ell h σ b v) 8)
      (matchingHomotopyColumn (ell + 5) 8 ((h : ℂ) * Complex.I * Z) ρ
        (horizontalQ ell h σ b v)) ≤ 0 := by
  have hs : ((h : ℂ) * Complex.I * Z).re = 0 := by simp
  have hsim : ((h : ℂ) * Complex.I * Z).im ≠ 0 := by
    have hh0 : h ≠ 0 := by intro hz; simp [hz] at hh
    simpa using mul_ne_zero hh0 hZ
  have he := matrixCone_normalizedForwardMatrix ((ell : ℝ) + 5)
    ((h : ℂ) * Complex.I * Z) (horizontalQ ell h σ b v) 8
    (matchingHomotopyColumn (ell + 5) 8 ((h : ℂ) * Complex.I * Z) ρ
      (horizontalQ ell h σ b v))
  push_cast at he
  rw [he]
  apply mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _)
  have hf := forward_matchingHomotopyColumn_cone σ ell 8
    (horizontalQ ell h σ b v) ((h : ℂ) * Complex.I * Z) ρ hσ (by decide)
    (horizontalQ_re ell h σ b v) hs hsim hρ hρ1
  simpa only [matrixCone, Nat.cast_add, Nat.cast_ofNat] using hf

theorem horizontal_forward_forms_pos (ell : ℕ) (σ b Z v : ℝ)
    (hbv : |b| < |v|)
    (hform : ∀ B C : ℂ, B ≠ 0 ∨ C ≠ 0 →
      0 < horizontalFormAt ell (v⁻¹, σ, b, Z, B, C))
    (w : Fin 2 → ℂ) (hw : w ≠ 0) :
    0 < matrixCone ((ell : ℝ) + 5) ((1 : ℂ) * Complex.I * Z)
      (normalizedForwardMatrix (ell + 5) ((1 : ℂ) * Complex.I * Z)
        (horizontalQ ell 1 σ b v) 8) w +
      matrixCone ((ell : ℝ) + 5) ((-1 : ℂ) * Complex.I * Z)
      (normalizedForwardMatrix (ell + 5) ((-1 : ℂ) * Complex.I * Z)
        (horizontalQ ell (-1) σ b v) 8) w := by
  have hv : v ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hbv
    linarith [abs_nonneg b]
  have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
  have he : ![w 0, (v : ℂ) * (((v⁻¹ : ℝ) : ℂ) * w 1)] = w := by
    funext i
    fin_cases i <;> simp [Complex.ofReal_inv, hvC]
  have hBC : w 0 ≠ 0 ∨ (((v⁻¹ : ℝ) : ℂ) * w 1) ≠ 0 := by
    by_contra hn
    push Not at hn
    have hw1 : w 1 = 0 := (mul_eq_zero.mp hn.2).resolve_left
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero hv))
    apply hw
    funext i
    fin_cases i <;> simp [hn.1, hw1]
  have hp := hform (w 0) (((v⁻¹ : ℝ) : ℂ) * w 1) hBC
  rw [horizontalFormAt_eq_cones ell σ b Z v _ _ hv
    (horizontalQ_sub_mass_add_ne_zero ell 1 σ b v (by norm_num) hbv)
    (horizontalQ_sub_mass_add_ne_zero ell (-1) σ b v (by norm_num) hbv)] at hp
  simpa only [horizontalCone, he, Complex.ofReal_one, Complex.ofReal_neg] using hp

/-- The finite positive form excludes horizontal homotopy zeros. Its uniform
positivity is supplied by `exists_horizontal_positive_neighborhood`. -/
theorem matchingHomotopy_horizontal_ne_zero_of_form (ell : ℕ) (σ b Z v ρ : ℝ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hZ : Z ≠ 0) (hbv : |b| < |v|)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hform : ∀ B C : ℂ, B ≠ 0 ∨ C ≠ 0 →
      0 < horizontalFormAt ell (v⁻¹, σ, b, Z, B, C)) :
    matchingColumnDeterminant
      (matchingHomotopyColumn (ell + 5) 8 ((1 : ℂ) * Complex.I * Z) ρ
        (horizontalQ ell 1 σ b v))
      (matchingHomotopyColumn (ell + 5) 8 ((-1 : ℂ) * Complex.I * Z) ρ
        (horizontalQ ell (-1) σ b v)) ≠ 0 := by
  exact matchingColumnDeterminant_ne_zero_of_forward_forms ((ell : ℝ) + 5)
    ((1 : ℂ) * Complex.I * Z) ((-1 : ℂ) * Complex.I * Z)
    (normalizedForwardMatrix (ell + 5) ((1 : ℂ) * Complex.I * Z) (horizontalQ ell 1 σ b v) 8)
    (normalizedForwardMatrix (ell + 5) ((-1 : ℂ) * Complex.I * Z) (horizontalQ ell (-1) σ b v) 8)
    _ _
    (by simpa using horizontal_homotopyColumn_ne_zero ell 1 σ b Z v ρ (by norm_num) hbv)
    (by simpa using horizontal_homotopyColumn_ne_zero ell (-1) σ b Z v ρ (by norm_num) hbv)
    (by simpa using horizontal_homotopy_cone_nonpos ell 1 σ b Z v ρ (by norm_num) hσ hZ hρ hρ1)
    (by simpa using horizontal_homotopy_cone_nonpos ell (-1) σ b Z v ρ (by norm_num) hσ hZ hρ hρ1)
    (horizontal_forward_forms_pos ell σ b Z v hbv hform)

end DefocusingNLS

end OAI
