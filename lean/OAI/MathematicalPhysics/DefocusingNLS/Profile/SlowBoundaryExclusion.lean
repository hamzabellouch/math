import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryMatchingExclusion

namespace OAI

/-! # The true outgoing determinant has no zero on the left boundary -/

namespace DefocusingNLS.BoundaryCertificate

theorem slowBoundary_left_determinant_ne_zero (ell : Fin 4) (b Z v : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2) :
    matchingColumnDeterminant
      (slowBoundaryColumn (boundaryQ ell b v) (ell + 6) (Complex.I * Z))
      (slowBoundaryColumn (boundaryQ ell (-b) v) (ell + 6) (-Complex.I * Z)) ≠ 0 := by
  have hZ0 : Z ≠ 0 := by intro hz; rw [hz] at hZ; norm_num at hZ
  have hq (b' : ℝ) : (boundaryQ ell b' v).re = -(1 / 32 : ℝ) + (ell : ℝ) / 2 := by
    simp [boundaryQ]
    ring
  have hq' (b' : ℝ) : -1 < (boundaryQ ell b' v).re := by
    rw [hq]
    linarith [Nat.cast_nonneg (α := ℝ) (ell : ℕ)]
  have hC₁ := (normalizedMatching_tail_disk (-(1 / 32)) ell 8
    (boundaryQ ell b v) (Complex.I * Z) le_rfl (by decide) (hq b)
    (by simp) (by simpa using hZ0)).1
  have hC₂ := (normalizedMatching_tail_disk (-(1 / 32)) ell 8
    (boundaryQ ell (-b) v) (-Complex.I * Z) le_rfl (by decide) (hq (-b))
    (by simp) (by simpa using hZ0)).1
  have he := matchingHomotopy_endpoint_determinant (ell + 5) 8 (Complex.I * Z)
    (-Complex.I * Z) (boundaryQ ell b v) (boundaryQ ell (-b) v)
    (by decide) (hq' b) (hq' (-b)) (by simp) (by simp)
    (by simpa using hZ0) (by simpa using hZ0)
    (by simpa only [show (ell : ℕ) + 5 + 1 = ell + 6 by omega] using hC₁)
    (by simpa only [show (ell : ℕ) + 5 + 1 = ell + 6 by omega] using hC₂)
  intro hz
  apply matchingHomotopy_left_boundary_ne_zero ell b Z v 1 hb hZ (by norm_num) le_rfl
  apply he.mpr
  simpa only [show (ell : ℕ) + 5 + 1 = ell + 6 by omega] using hz

end DefocusingNLS.BoundaryCertificate

end OAI
