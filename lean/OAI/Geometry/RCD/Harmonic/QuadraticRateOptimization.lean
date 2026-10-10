import OAI.Geometry.RCD.Heat.SpaceTimeSlopeRate

namespace OAI

/-! # Optimizing the positive spatial scale in the quadratic rate -/

namespace RegularPointCoordinates

theorem square_le_of_young_bounds {g C A : ℝ} (hg : 0 ≤ g) (hC : 0 ≤ C) (hA : 0 < A)
    (h : ∀ ell : ℝ, 0 < ell → g ≤ ell*C/2+A/(2*ell)) :
    g^2 ≤ A*C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let q := C+ε/A
  have hq : 0 < q := by dsimp [q]; positivity
  have hCq : C ≤ q := le_add_of_nonneg_right (div_nonneg hε.le hA.le)
  let ell := Real.sqrt (A/q)
  have hell : 0 < ell := Real.sqrt_pos.mpr (div_pos hA hq)
  have he : ell^2*q=A := by
    dsimp only [ell]
    rw [Real.sq_sqrt (div_nonneg hA.le hq.le)]
    field_simp
  have hb := (le_div_iff₀ (show 0 < 2*ell by positivity)).mp
    (show g ≤ (ell^2*C+A)/(2*ell) from by convert h ell hell using 1; field_simp)
  have hm := mul_le_mul_of_nonneg_left hCq (sq_nonneg ell)
  have hgle : g ≤ ell*q := by nlinarith only [hb,hm,he,hell]
  have hs := pow_le_pow_left₀ hg hgle 2
  have he' : (ell*q)^2=A*q := by rw [←he]; ring
  rw [he'] at hs
  have heq : A*q=A*C+ε := by dsimp [q]; field_simp
  rwa [heq] at hs

end RegularPointCoordinates

end OAI
