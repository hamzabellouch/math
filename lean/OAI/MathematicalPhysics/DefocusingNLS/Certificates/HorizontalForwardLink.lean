import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HorizontalCompactification

namespace OAI

/-! # The compactified recurrence is the actual forward jet -/

open Matrix

namespace DefocusingNLS

noncomputable def horizontalQ (ell : ℕ) (h σ b v : ℝ) : ℂ :=
  ((σ + (ell : ℝ) / 2 : ℝ) : ℂ) + Complex.I * ((v - h * b : ℝ) : ℂ)

theorem horizontalDifference_forward (ell n : ℕ) (h σ b Z v : ℝ)
    (hv : v ≠ 0) (B C : ℂ) :
    horizontalDifference ell n h σ b Z v⁻¹ B ((v⁻¹ : ℝ) * C) =
      -(((ell : ℂ) + 5) * B + ((h : ℂ) * Complex.I * Z) * C) /
        (horizontalQ ell h σ b v + n - (ell + 5)) := by
  have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
  have hd : Complex.I + ((v⁻¹ : ℝ) : ℂ) *
      ((((σ + (ell : ℝ) / 2 + n - ((ell : ℝ) + 5) : ℝ) : ℂ)) -
        (h : ℂ) * Complex.I * b) =
      ((v⁻¹ : ℝ) : ℂ) * (horizontalQ ell h σ b v + n - (ell + 5)) := by
    simp only [horizontalQ]
    push_cast
    field_simp [hvC]
    ring
  rw [horizontalDifference, hd]
  have hn : -(((v⁻¹ : ℝ) : ℂ) * ((ell : ℂ) + 5) * B +
      (h : ℂ) * Complex.I * Z * (((v⁻¹ : ℝ) : ℂ) * C)) =
      ((v⁻¹ : ℝ) : ℂ) * -(((ell : ℂ) + 5) * B + (h : ℂ) * Complex.I * Z * C) := by ring
  rw [hn, mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hv))]

theorem horizontalState_forward (ell N : ℕ) (h σ b Z v : ℝ) (hv : v ≠ 0)
    (hd : ∀ n : ℕ, horizontalQ ell h σ b v + n - (ell + 5) ≠ 0) (B C : ℂ) :
    horizontalState ell h σ b Z v⁻¹ B C N =
      (normalizedForwardJet (ell + 5) ((h : ℂ) * Complex.I * Z)
        (horizontalQ ell h σ b v) ![B, (v : ℂ) * C] N 0,
       ((v⁻¹ : ℝ) : ℂ) * normalizedForwardJet (ell + 5) ((h : ℂ) * Complex.I * Z)
        (horizontalQ ell h σ b v) ![B, (v : ℂ) * C] N 1) := by
  let q := horizontalQ ell h σ b v
  let s := (h : ℂ) * Complex.I * Z
  let w : Fin 2 → ℂ := ![B, (v : ℂ) * C]
  have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
  induction N with
  | zero =>
    simp [horizontalState, normalizedForwardJet, Complex.ofReal_inv, hvC]
  | succ N ih =>
    rw [horizontalState, ih, horizontalDifference_forward ell N h σ b Z v hv]
    have hg : normalizedForwardJet (ell + 5) s q w N 0 -
        -(((ell : ℂ) + 5) * normalizedForwardJet (ell + 5) s q w N 0 +
          s * normalizedForwardJet (ell + 5) s q w N 1) / (q + N - (ell + 5)) =
        normalizedForwardJet (ell + 5) s q w (N + 1) 0 := by
      rw [normalizedForwardJet_succ_first]
      dsimp only [q, s, w]
      field_simp [hd N]
      ring
    change (_, _) = (_, _)
    apply Prod.ext
    · exact hg
    · rw [normalizedForwardJet_succ_second _ _ _ _ _ (hd N)]
      change ((v⁻¹ : ℝ) : ℂ) * normalizedForwardJet (ell + 5) s q w N 1 -
        ((v⁻¹ : ℝ) : ℂ) * _ = _
      rw [hg, mul_sub]

/-- The finite telescoping identity retains the exact cone weights. -/
theorem normalizedForwardJet_cone_sum (ell N : ℕ) (h σ b Z v : ℝ)
    (hv : v ≠ 0) (hd : ∀ n : ℕ, horizontalQ ell h σ b v + n - (ell + 5) ≠ 0)
    (B C : ℂ) :
    coneForm ((ell : ℝ) + 5) ((h : ℂ) * Complex.I * Z)
      (normalizedForwardJet (ell + 5) ((h : ℂ) * Complex.I * Z)
        (horizontalQ ell h σ b v) ![B, (v : ℂ) * C] N 0)
      (normalizedForwardJet (ell + 5) ((h : ℂ) * Complex.I * Z)
        (horizontalQ ell h σ b v) ![B, (v : ℂ) * C] N 1) =
    coneForm ((ell : ℝ) + 5) ((h : ℂ) * Complex.I * Z) B ((v : ℂ) * C) +
      horizontalIncrementSum ell h σ b Z v⁻¹ B C N := by
  induction N with
  | zero => simp [normalizedForwardJet, horizontalIncrementSum]
  | succ N ih =>
    let q := horizontalQ ell h σ b v
    let s := (h : ℂ) * Complex.I * Z
    let w : Fin 2 → ℂ := ![B, (v : ℂ) * C]
    have hi := normalizedForwardJet_increment ((ell : ℝ) + 5) s q w N
      (by simp [s, Complex.mul_re, Complex.mul_im])
      (by simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat] using hd N)
    have he : ((q + N).re - ((ell : ℝ) + 5) / 2) = σ + N - 5 / 2 := by
      simp [q, horizontalQ]
      ring
    rw [he] at hi
    have hs := horizontalState_forward ell N h σ b Z v hv hd B C
    have hg := horizontalDifference_forward ell N h σ b Z v hv
      (normalizedForwardJet (ell + 5) s q w N 0) (normalizedForwardJet (ell + 5) s q w N 1)
    have hdiff : horizontalDifference ell N h σ b Z v⁻¹
        (horizontalState ell h σ b Z v⁻¹ B C N).1
        (horizontalState ell h σ b Z v⁻¹ B C N).2 =
        normalizedForwardJet (ell + 5) s q w N 0 -
          normalizedForwardJet (ell + 5) s q w (N + 1) 0 := by
      rw [hs, hg, normalizedForwardJet_succ_first]
      dsimp only [q, s, w]
      field_simp [hd N]
      ring
    rw [horizontalIncrementSum, Finset.sum_range_succ, hdiff]
    change _ = _ + (horizontalIncrementSum ell h σ b Z v⁻¹ B C N + _)
    push_cast at hi
    linarith

end DefocusingNLS

end OAI
