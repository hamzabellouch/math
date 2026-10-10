import OAI.Geometry.RCD.Metric.AnnularVolume

namespace OAI

/-! # Fixed volume losses for the actual radial fit -/

namespace RegularPointCoordinates

theorem quarter_volume_bounds {n : ℕ} {r omega V : ℝ} (hr : 0 < r) (homega : 0 < omega)
    (h : |V / (omega * r ^ n) - 1| ≤ 1 / 4) :
    0 < V ∧ (3 / 4 : ℝ) * omega * r ^ n ≤ V ∧ V ≤ (5 / 4 : ℝ) * omega * r ^ n := by
  have hd : 0 < omega * r ^ n := mul_pos homega (pow_pos hr _)
  have hb := abs_le.mp h
  have hlo : (3 / 4 : ℝ) ≤ V / (omega * r ^ n) := by linarith
  have hhi : V / (omega * r ^ n) ≤ (5 / 4 : ℝ) := by linarith
  have hl := (le_div_iff₀ hd).mp hlo
  have hh := (div_le_iff₀ hd).mp hhi
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- At the fixed radial testing fraction, the source normalization and
the averaging normalization differ by a dimensional constant. -/
theorem radial_testing_volume_ratio {n : ℕ} {s omega V : ℝ}
    (hs : 0 < s) (homega : 0 < omega)
    (h : |V / (omega * (s / 64) ^ n) - 1| ≤ 1 / 4) :
    s ^ (n : ℝ) / V ≤ (4 / (3 * omega)) * (64 : ℝ) ^ n := by
  obtain ⟨hV, hlo, _⟩ := quarter_volume_bounds (by positivity : 0 < s / 64) homega h
  apply (div_le_iff₀ hV).mpr
  have he : (4 / (3 * omega)) * (64 : ℝ) ^ n *
      ((3 / 4 : ℝ) * omega * (s / 64) ^ n) = s ^ (n : ℝ) := by
    rw [Real.rpow_natCast, div_pow]
    field_simp [homega.ne']
  rw [← he]
  exact mul_le_mul_of_nonneg_left hlo (by positivity)

/-- Both radius levels lie in the same quarter-error volume regime. -/
theorem radial_fraction_volume_ratio {n : ℕ} {r theta omega V W : ℝ}
    (hr : 0 < r) (htheta : 0 < theta) (homega : 0 < omega)
    (hV : |V / (omega * r ^ n) - 1| ≤ 1 / 4)
    (hW : |W / (omega * (theta * r) ^ n) - 1| ≤ 1 / 4) :
    V / W ≤ (5 / 3 : ℝ) * (theta ^ n)⁻¹ := by
  obtain ⟨_, _, hv⟩ := quarter_volume_bounds hr homega hV
  obtain ⟨hw0, hw, _⟩ := quarter_volume_bounds (mul_pos htheta hr) homega hW
  apply (div_le_iff₀ hw0).mpr
  have he : (5 / 3 : ℝ) * (theta ^ n)⁻¹ *
      ((3 / 4 : ℝ) * omega * (theta * r) ^ n) = (5 / 4 : ℝ) * omega * r ^ n := by
    rw [mul_pow]
    field_simp [htheta.ne']
  exact hv.trans (he.symm.trans_le (mul_le_mul_of_nonneg_left hw (by positivity)))

/-- The normalized integral error has size at most s*sqrt(P), with one
fixed coefficient. This is the error inserted into the dyadic fit step. -/
theorem radial_sqrt_error_bound {s V Q C D : ℝ}
    (hs : 0 ≤ s) (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hD : 0 ≤ D)
    {N : ℝ} (hratio : N / V ≤ D) :
    Real.sqrt (V⁻¹ * (C * s ^ 2 * (N * Q))) ≤ s * Real.sqrt (C * D) * Real.sqrt Q := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ C * s ^ 2 * Q)
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hC hD), Real.sq_sqrt hQ]
    convert hh using 1 <;> ring

/-- Dividing the fitted values by their own radii gives the strict
square-root contraction factor. The 64 is the fixed testing fraction. -/
theorem radial_fit_rescale {s theta Lambda A Q E F : ℝ}
    (hs : 0 < s) (htheta : 0 < theta)
    (hstep : F ≤ (Lambda + (1 / 2 : ℝ) * theta * Real.sqrt theta) *
      s * A * Real.sqrt Q + (1 / 2 : ℝ) * theta * Real.sqrt theta * E) :
    F / (theta * (s / 64)) ≤ (1 / 2 : ℝ) * Real.sqrt theta * (E / (s / 64)) +
      (64 / theta) * (Lambda + (1 / 2 : ℝ) * theta * Real.sqrt theta) * A * Real.sqrt Q := by
  apply (div_le_div_of_nonneg_right hstep (mul_pos htheta (by positivity)).le).trans_eq
  field_simp [hs.ne', htheta.ne']
  ring

/-- The actual normalized volume bound removes all scale dependence from
the affine-fit error. This is the scalar recurrence used by the envelope. -/
theorem radial_fit_natural_units {s theta V Lambda A D N Q E F W : ℝ}
    (hs : 0 < s) (htheta : 0 < theta) (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hVL : V ≤ Lambda) (hratio : N / W ≤ D)
    (hstep : F ≤ (V + (1 / 2 : ℝ) * theta * Real.sqrt theta) *
      Real.sqrt (W⁻¹ * (A * s ^ 2 * (N * Q))) +
        (1 / 2 : ℝ) * theta * Real.sqrt theta * E) :
    F / (theta * (s / 64)) ≤ (1 / 2 : ℝ) * Real.sqrt theta * (E / (s / 64)) +
      (64 / theta) * (Lambda + (1 / 2 : ℝ) * theta * Real.sqrt theta) *
        Real.sqrt (A * D) * Real.sqrt Q := by
  apply radial_fit_rescale hs htheta
  have hroot := radial_sqrt_error_bound hs.le hQ hA hD hratio
  have hterm := mul_le_mul (add_le_add hVL (le_refl _)) hroot (Real.sqrt_nonneg _)
    (by have := hV.trans hVL; positivity : 0 ≤ Lambda + (1 / 2 : ℝ) * theta * Real.sqrt theta)
  exact hstep.trans (by nlinarith [hterm])

end RegularPointCoordinates

end OAI
