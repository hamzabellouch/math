import OAI.MeasureTheory.Falconer.Geometry.QuadraticChart

namespace OAI

/-!
# Differential of the quadratic-to-gnomonic coordinate change

The differential is a scalar multiple of the identity plus one radial
rank-one term. These are actual derivatives of the coordinate map, not
assumed Jacobian data.
-/

namespace Falconer

noncomputable def quadraticRadialFactor (s : ℝ) : ℝ :=
  Real.sqrt (1-s/4) / (1-s/2)

noncomputable def quadraticRadialDerivative (s : ℝ) : ℝ :=
  (6-s) / (16 * Real.sqrt (1-s/4) * (1-s/2)^2)

private theorem radial_derivative_algebra (s q a : ℝ) (hq : q ≠ 0)
    (ha : a ≠ 0) (has : a = 1-s/2) (hqs : q^2 = 1-s/4) :
    ((-1/4)/(2*q)*a - q*(-1/2))/a^2 = (6-s)/(16*q*a^2) := by
  field_simp [hq, ha]
  nlinarith

private theorem radial_eigenvalue_algebra (s q a : ℝ) (hq : q ≠ 0)
    (ha : a ≠ 0) (has : a = 1-s/2) (hqs : q^2 = 1-s/4) :
    q/a + 2*s*((6-s)/(16*q*a^2)) = 1/(q*a^2) := by
  field_simp [hq, ha]
  rw [has]
  ring_nf
  rw [hqs]
  ring

theorem quadraticRadialFactor_hasDerivAt {s : ℝ} (hs : s < 1) :
    HasDerivAt quadraticRadialFactor (quadraticRadialDerivative s) s := by
  have hq : 0 < Real.sqrt (1-s/4) := Real.sqrt_pos.mpr (by linarith)
  have ha : 0 < 1-s/2 := by linarith
  have hb : HasDerivAt (fun t : ℝ => 1-t/4) (-1/4) s := by
    convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).div_const 4) using 1 <;>
      first | rfl | norm_num
  have hc : HasDerivAt (fun t : ℝ => 1-t/2) (-1/2) s := by
    convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).div_const 2) using 1 <;>
      first | rfl | norm_num
  have hh := (hb.sqrt (by linarith : 1-s/4 ≠ 0)).div hc ha.ne'
  have he := radial_derivative_algebra s (Real.sqrt (1-s/4)) (1-s/2) hq.ne' ha.ne' rfl
    (Real.sq_sqrt (show 0 ≤ 1-s/4 by linarith))
  exact hh.congr_deriv he

noncomputable def quadraticCoordinateDifferential {n : ℕ} (u : Space n) :
    Space n →L[ℝ] Space n :=
  quadraticRadialFactor (‖u‖^2) • ContinuousLinearMap.id ℝ (Space n) +
    (2 * quadraticRadialDerivative (‖u‖^2)) • (innerSL ℝ u).smulRight u

theorem quadraticToGnomonic_hasFDerivAt {n : ℕ} {u : Space n} (hu : ‖u‖ < 1) :
    HasFDerivAt quadraticToGnomonic (quadraticCoordinateDifferential u) u := by
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have hφ := (quadraticRadialFactor_hasDerivAt hu2).hasFDerivAt.comp u
    (hasStrictFDerivAt_norm_sq u).hasFDerivAt
  have hF := hφ.smul (hasFDerivAt_id u)
  apply hF.congr_fderiv
  ext v
  simp [quadraticCoordinateDifferential,
    ContinuousLinearMap.toSpanSingleton_apply, smul_smul, mul_comm, mul_left_comm]

theorem quadratic_radial_eigenvalue {s : ℝ} (hs : s < 1) :
    quadraticRadialFactor s + 2*s*quadraticRadialDerivative s =
      1 / (Real.sqrt (1-s/4) * (1-s/2)^2) := by
  have hq : 0 < Real.sqrt (1-s/4) := Real.sqrt_pos.mpr (by linarith)
  have ha : 0 < 1-s/2 := by linarith
  exact radial_eigenvalue_algebra s (Real.sqrt (1-s/4)) (1-s/2) hq.ne' ha.ne' rfl
    (Real.sq_sqrt (show 0 ≤ 1-s/4 by linarith))

end Falconer

end OAI
