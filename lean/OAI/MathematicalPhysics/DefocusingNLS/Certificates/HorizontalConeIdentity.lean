import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HorizontalForwardLink
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HorizontalContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RightMatchingExclusion

namespace OAI

/-! # Identification of the horizontal form with the two forward cones -/

open Matrix Polynomial

namespace DefocusingNLS

noncomputable def horizontalCone (ell : ℕ) (h σ b Z v : ℝ) (B C : ℂ) : ℝ :=
  matrixCone ((ell : ℝ) + 5) ((h : ℂ) * Complex.I * Z)
    (normalizedForwardMatrix (ell + 5) ((h : ℂ) * Complex.I * Z)
      (horizontalQ ell h σ b v) 8) ![B, (v : ℂ) * C]

theorem horizontalCone_eq_increment (ell : ℕ) (h σ b Z v : ℝ) (B C : ℂ)
    (hv : v ≠ 0) (hd : ∀ n : ℕ, horizontalQ ell h σ b v + n - (ell + 5) ≠ 0) :
    horizontalCone ell h σ b Z v B C =
      coneForm ((ell : ℝ) + 5) ((h : ℂ) * Complex.I * Z) B ((v : ℂ) * C) +
        horizontalIncrementSum ell h σ b Z v⁻¹ B C 8 := by
  have he := normalizedForwardJet_cone_sum ell 8 h σ b Z v hv hd B C
  simpa only [normalizedForwardJet_eq_mulVec, horizontalCone, matrixCone] using he

theorem horizontalFormAt_eq_cones (ell : ℕ) (σ b Z v : ℝ) (B C : ℂ) (hv : v ≠ 0)
    (hd₁ : ∀ n : ℕ, horizontalQ ell 1 σ b v + n - (ell + 5) ≠ 0)
    (hd₂ : ∀ n : ℕ, horizontalQ ell (-1) σ b v + n - (ell + 5) ≠ 0) :
    horizontalFormAt ell (v⁻¹, σ, b, Z, B, C) =
      horizontalCone ell 1 σ b Z v B C + horizontalCone ell (-1) σ b Z v B C := by
  rw [horizontalCone_eq_increment ell 1 σ b Z v B C hv hd₁,
    horizontalCone_eq_increment ell (-1) σ b Z v B C hv hd₂]
  have hi : coneForm ((ell : ℝ) + 5) ((1 : ℂ) * Complex.I * Z) B ((v : ℂ) * C) +
      coneForm ((ell : ℝ) + 5) ((-1 : ℂ) * Complex.I * Z) B ((v : ℂ) * C) =
      ((ell : ℝ) + 5) * Complex.normSq B := by
    simp [coneForm]
    ring
  change ((ell : ℝ) + 5) * Complex.normSq B + _ + _ = _
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one]
  linear_combination -hi

theorem ascPochhammer_eval_ne_zero_of_im_ne_zero (q : ℂ) (N : ℕ) (hq : q.im ≠ 0) :
    (ascPochhammer ℂ N).eval q ≠ 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ascPochhammer_succ_eval]
    apply mul_ne_zero ih
    intro h
    apply hq
    have hi := congrArg Complex.im h
    simpa using hi

end DefocusingNLS

end OAI
