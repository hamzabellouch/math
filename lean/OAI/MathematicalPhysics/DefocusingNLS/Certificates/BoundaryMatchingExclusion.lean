import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryForwardScaling

namespace OAI

/-! # Exclusion of matching zeros on the left counting boundary -/

open Polynomial Matrix

namespace DefocusingNLS.BoundaryCertificate

attribute [local irreducible] polynomialState

theorem boundary_forward_cones_pos (ell : Fin 4) (b Z v : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    (w : Fin 2 → ℂ) (hw : w ≠ 0) :
    0 < matrixCone (ell + 5) (Complex.I * Z)
      (forwardProduct (ell + 5) (Complex.I * Z) (boundaryQ ell b v) 8) w +
      matrixCone (ell + 5) (-Complex.I * Z)
      (forwardProduct (ell + 5) (-Complex.I * Z) (boundaryQ ell (-b) v) 8) w := by
  have hp := evaluated_boundary_cones_pos ell b Z v hb hZ w hw
  have h₁ : (fun i j => ((stateMatrix (polynomialState ell b Z 8)) i j).eval (v : ℂ)) =
      (((100000000 : ℝ) ^ 8 : ℝ) : ℂ) •
        forwardProduct (ell + 5) (Complex.I * Z) (boundaryQ ell b v) 8 := by
    apply Matrix.ext
    intro i j
    change _ = (((100000000 : ℝ) ^ 8 : ℝ) : ℂ) *
      forwardProduct (ell + 5) (Complex.I * Z) (boundaryQ ell b v) 8 i j
    simpa only [Complex.ofReal_pow, Complex.ofReal_ofNat] using
      polynomialState_eval_scaled ell b Z v 8 i j
  have h₂ : (fun i j => star (((stateMatrix (polynomialState ell b Z 8)) i j).eval
      ((-v : ℝ) : ℂ))) = (((100000000 : ℝ) ^ 8 : ℝ) : ℂ) •
        forwardProduct (ell + 5) (-Complex.I * Z) (boundaryQ ell (-b) v) 8 := by
    apply Matrix.ext
    intro i j
    change _ = (((100000000 : ℝ) ^ 8 : ℝ) : ℂ) *
      forwardProduct (ell + 5) (-Complex.I * Z) (boundaryQ ell (-b) v) 8 i j
    have hc := forwardProduct_conjugate (((ell : ℕ) : ℝ) + 5) (Complex.I * Z)
      (boundaryQ ell b (-v)) 8 i j
    push_cast at hc
    rw [polynomialState_eval_scaled, star_mul, hc, boundaryQ_conjugate]
    simp only [star_mul, star_pow, Complex.star_def, Complex.conj_ofNat,
      Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_pow, Complex.ofReal_ofNat]
    rw [mul_comm (Z : ℂ) (-Complex.I)]
    exact mul_comm (forwardProduct (ell + 5) (-Complex.I * Z) (boundaryQ ell (-b) v) 8 i j)
      ((100000000 : ℂ) ^ 8)
  have hM : scaledMass ell = (100000000 : ℝ) * ((ell : ℝ) + 5) := by
    simp [scaledMass]
  have hs : scaledShift Z = (100000000 : ℂ) * (Complex.I * Z) := by
    simp [scaledShift]
    ring
  have hs' : star (scaledShift Z) = (100000000 : ℂ) * (-Complex.I * Z) := by
    rw [hs]
    simp
  have hscale (s : ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ) :=
    matrixCone_real_scaling (100000000 : ℝ) ((100000000 : ℝ) ^ 8)
      ((ell : ℝ) + 5) s T w
  simp only [Complex.ofReal_ofNat] at hscale
  rw [h₁, h₂, hM, hs', hs, hscale, hscale] at hp
  have ha : 0 < (100000000 : ℝ) * ((100000000 : ℝ) ^ 8) ^ 2 := by positivity
  exact pos_of_mul_pos_right (by simpa only [mul_add] using hp) ha.le

theorem boundaryQ_add_nat_ne_zero (ell n : ℕ) (b v : ℝ) :
    boundaryQ ell b v + n ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [boundaryQ, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, zero_mul, mul_zero,
    sub_zero, Complex.zero_re] at hr
  have he : (16 : ℝ) * ell + 32 * n = 1 := by linarith
  have hi : (16 : ℤ) * ell + 32 * n = 1 := by exact_mod_cast he
  omega

theorem boundaryQ_sub_mass_add_nat_ne_zero (ell n : ℕ) (b v : ℝ) :
    boundaryQ ell b v - (ell + 5) + n ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [boundaryQ, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, zero_mul, mul_zero, sub_zero,
    Complex.zero_re] at hr
  norm_num at hr
  have he : (32 : ℝ) * n = 16 * ell + 161 := by linarith
  have hi : (32 : ℤ) * n = 16 * ell + 161 := by exact_mod_cast he
  omega

theorem boundaryQ_pochhammer_ne_zero (ell N : ℕ) (b v : ℝ) :
    (ascPochhammer ℂ N).eval (boundaryQ ell b v) ≠ 0 ∧
    (ascPochhammer ℂ N).eval (boundaryQ ell b v - (ell + 5)) ≠ 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [ascPochhammer_succ_eval, ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨ih.1, boundaryQ_add_nat_ne_zero ell N b v⟩,
      ⟨ih.2, boundaryQ_sub_mass_add_nat_ne_zero ell N b v⟩⟩

/-- No member of the actual tail homotopy has a matching zero on the left
counting boundary. The only assumptions are the certified parameter box and
the homotopy parameter interval. -/
theorem matchingHomotopy_left_boundary_ne_zero (ell : Fin 4) (b Z v ρ : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    matchingColumnDeterminant
      (matchingHomotopyColumn (ell + 5) 8 (Complex.I * Z) ρ (boundaryQ ell b v))
      (matchingHomotopyColumn (ell + 5) 8 (-Complex.I * Z) ρ (boundaryQ ell (-b) v)) ≠ 0 := by
  have hZ0 : Z ≠ 0 := by intro hz; rw [hz] at hZ; norm_num at hZ
  have hq (b' : ℝ) : (boundaryQ ell b' v).re = -(1 / 32 : ℝ) + (ell : ℝ) / 2 := by
    simp [boundaryQ]
    ring
  apply matchingColumnDeterminant_ne_zero_of_forward_forms (ell + 5)
    (Complex.I * Z) (-Complex.I * Z)
    (forwardProduct (ell + 5) (Complex.I * Z) (boundaryQ ell b v) 8)
    (forwardProduct (ell + 5) (-Complex.I * Z) (boundaryQ ell (-b) v) 8)
  · exact matchingHomotopyColumn_ne_zero_of_factors _ _ _ _ _
      (boundaryQ_pochhammer_ne_zero ell 8 b v).1
      (by simpa only [Nat.cast_add, Nat.cast_ofNat] using (boundaryQ_pochhammer_ne_zero ell 8 b v).2)
  · exact matchingHomotopyColumn_ne_zero_of_factors _ _ _ _ _
      (boundaryQ_pochhammer_ne_zero ell 8 (-b) v).1
      (by simpa only [Nat.cast_add, Nat.cast_ofNat] using (boundaryQ_pochhammer_ne_zero ell 8 (-b) v).2)
  · exact forward_matchingHomotopyColumn_cone (-(1 / 32)) ell 8 _ _ ρ (by rfl) (by decide)
      (hq b) (by simp) (by simpa using hZ0) hρ hρ1
  · exact forward_matchingHomotopyColumn_cone (-(1 / 32)) ell 8 _ _ ρ (by rfl) (by decide)
      (hq (-b)) (by simp) (by simpa using hZ0) hρ hρ1
  · exact boundary_forward_cones_pos ell b Z v hb hZ

end DefocusingNLS.BoundaryCertificate

end OAI
