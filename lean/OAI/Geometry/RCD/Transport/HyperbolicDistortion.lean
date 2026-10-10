import OAI.Geometry.RCD.Metric.LowerCurvatureVolume

namespace OAI

/-! # Sharp radial distortion on bounded annuli

The curvature-dimension coefficients retain their hyperbolic radial factor.
These scalar comparisons will be used with the actual transport plan to
compare annuli before integrating the radial volume density.
-/

open Set
open scoped ENNReal

namespace RegularPointCoordinates

theorem sinh_mul_cosh_sub_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.sinh x * Real.cosh x - x := by
  let f : ℝ → ℝ := fun y => Real.sinh y * Real.cosh y - y
  have hd (y : ℝ) : HasDerivAt f
      (Real.cosh y ^ 2 + Real.sinh y ^ 2 - 1) y := by
    convert ((Real.hasDerivAt_sinh y).mul (Real.hasDerivAt_cosh y)).sub
      (hasDerivAt_id y) using 1 <;> first | rfl | ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
    · exact ((Real.continuous_sinh.mul Real.continuous_cosh).sub continuous_id).continuousOn
    · intro y _
      exact (hd y).hasDerivWithinAt
    · intro y _
      nlinarith [Real.cosh_sq_sub_sinh_sq y, sq_nonneg (Real.sinh y)]
  simpa only [f, Real.sinh_zero, mul_zero, zero_mul, sub_zero] using hm (by simp) hx hx

theorem monotone_hyperbolic_radial_logDerivative :
    MonotoneOn (fun x : ℝ => x * Real.cosh x / Real.sinh x) (Ioi 0) := by
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x : ℝ => x * Real.cosh x / Real.sinh x)
        ((Real.sinh x * Real.cosh x - x) / Real.sinh x ^ 2) x := by
    convert (((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).div
      (Real.hasDerivAt_sinh x) (Real.sinh_pos_iff.mpr hx).ne') using 1
    · rfl
    have hh := Real.cosh_sq_sub_sinh_sq x
    simp only [id_eq, Pi.mul_apply]
    field_simp
    nlinarith [congrArg (fun z : ℝ => x * z) hh]
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi (0 : ℝ))
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (by simpa only [interior_Ioi, mem_Ioi] using hx)).hasDerivWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    exact div_nonneg (sinh_mul_cosh_sub_nonneg hx0.le) (sq_nonneg _)

theorem antitone_sinh_radial_ratio {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    AntitoneOn (fun x : ℝ => Real.sinh (t * x) / Real.sinh x) (Ioi 0) := by
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x : ℝ => Real.sinh (t * x) / Real.sinh x)
        ((t * Real.cosh (t * x) * Real.sinh x -
          Real.sinh (t * x) * Real.cosh x) / Real.sinh x ^ 2) x := by
    convert (((hasDerivAt_id x).const_mul t).sinh.div
      (Real.hasDerivAt_sinh x) (Real.sinh_pos_iff.mpr hx).ne') using 1
    · rfl
    · simp only [id_eq]
      ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi (0 : ℝ))
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (by simpa only [interior_Ioi, mem_Ioi] using hx)).hasDerivWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    have htx : 0 < t * x := mul_pos ht hx0
    have hm := monotone_hyperbolic_radial_logDerivative htx hx0
      (mul_le_of_le_one_left hx0.le ht1)
    have hs := Real.sinh_pos_iff.mpr hx0
    have hts := Real.sinh_pos_iff.mpr htx
    have hc := (div_le_div_iff₀ hts hs).mp hm
    have hc' : t * Real.cosh (t * x) * Real.sinh x ≤
        Real.sinh (t * x) * Real.cosh x := by
      apply (mul_le_mul_iff_right₀ hx0).mp
      nlinarith only [hc]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    linarith only [hc']

theorem sinh_radial_ratio_le_time {t x : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : 0 < x) : Real.sinh (t * x) / Real.sinh x ≤ t := by
  have hconv : ConvexOn ℝ (Ici 0) Real.sinh := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici (0 : ℝ))
      Real.continuous_sinh.continuousOn
      (fun x _ => (Real.hasDerivAt_sinh x).hasDerivWithinAt)
      (fun x _ => (Real.hasDerivAt_cosh x).hasDerivWithinAt)
    intro x hx
    exact (Real.sinh_pos_iff.mpr (by simpa only [interior_Ici, mem_Ioi] using hx)).le
  have hc := hconv.2
    (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 from hx.le)
    (sub_nonneg.mpr ht1) ht (by ring : 1 - t + t = 1)
  apply (div_le_iff₀ (Real.sinh_pos_iff.mpr hx)).mpr
  simpa only [smul_eq_mul, mul_zero, Real.sinh_zero, zero_add] using hc

theorem sigma_neg_eq {K N θ : ℝ} (hK : K < 0) (hN : 1 < N) (hθ : 0 < θ)
    (t : ℝ) :
    sigma K N t θ = ENNReal.ofReal
      (Real.sinh (t * θ * Real.sqrt (-K / (N - 1))) /
        Real.sinh (θ * Real.sqrt (-K / (N - 1)))) := by
  have hn : 0 < (N - 1) * Real.pi ^ 2 := mul_pos (sub_pos.mpr hN)
    (sq_pos_of_pos Real.pi_pos)
  have hk : K * θ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK.le (sq_nonneg θ)
  simp only [sigma, ite_eq_right (not_or.mpr ⟨hθ.ne', hK.ne⟩),
    ite_eq_right (by linarith : ¬(N - 1) * Real.pi ^ 2 ≤ K * θ ^ 2),
    ite_eq_right (not_lt.mpr hK.le)]

theorem sigma_antitone_distance_nonpos_curvature {K N t θ D : ℝ}
    (hK : K ≤ 0) (hN : 1 < N) (ht : 0 < t) (ht1 : t ≤ 1)
    (hθ : 0 ≤ θ) (hθD : θ ≤ D) : sigma K N t D ≤ sigma K N t θ := by
  by_cases hK0 : K = 0
  · simp [sigma, hK0]
  have hKneg : K < 0 := lt_of_le_of_ne hK hK0
  by_cases hD0 : D = 0
  · have hθ0 : θ = 0 := le_antisymm (by simpa only [hD0] using hθD) hθ
    simp only [hD0, hθ0, le_refl]
  have hD : 0 < D := lt_of_le_of_ne (hθ.trans hθD) (Ne.symm hD0)
  have ha : 0 < Real.sqrt (-K / (N - 1)) :=
    Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) (sub_pos.mpr hN))
  rw [sigma_neg_eq hKneg hN hD]
  by_cases hθ0 : θ = 0
  · simp only [sigma, hθ0, true_or, ite_true]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using sinh_radial_ratio_le_time ht.le ht1 (mul_pos hD ha)
  have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθ0)
  rw [sigma_neg_eq hKneg hN hθpos]
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using antitone_sinh_radial_ratio ht ht1
    (mul_pos hθpos ha) (mul_pos hD ha) (mul_le_mul_of_nonneg_right hθD ha.le)

theorem tau_antitone_distance_nonpos_curvature {K N t θ D : ℝ}
    (hK : K ≤ 0) (hN : 1 < N) (ht : 0 < t) (ht1 : t < 1)
    (hθ : 0 ≤ θ) (hθD : θ ≤ D) : tau K N t D ≤ tau K N t θ := by
  have hα : 0 ≤ 1 - 1 / N := sub_nonneg.mpr
    ((div_le_one (zero_lt_one.trans hN)).mpr hN.le)
  simp only [tau, ite_eq_right ht.ne', ite_eq_right (ne_of_lt ht1)]
  exact mul_le_mul_right (ENNReal.rpow_le_rpow
    (sigma_antitone_distance_nonpos_curvature hK hN ht ht1.le hθ hθD) hα) _

theorem tau_nat_power {K t θ : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (ht : 0 < t) (ht1 : t < 1) :
    tau K n t θ ^ n = ENNReal.ofReal t * sigma K n t θ ^ (n - 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hfirst : ((ENNReal.ofReal t) ^ (1 / (n : ℝ))) ^ n = ENNReal.ofReal t := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      one_div_mul_cancel hn0, ENNReal.rpow_one]
  have hexponent : (1 - 1 / (n : ℝ)) * n = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
  have hsecond : ((sigma K n t θ) ^ (1 - 1 / (n : ℝ))) ^ n =
      sigma K n t θ ^ (n - 1) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, hexponent, ENNReal.rpow_natCast]
  simp only [tau, ite_eq_right ht.ne', ite_eq_right (ne_of_lt ht1), mul_pow, hfirst, hsecond]

end RegularPointCoordinates

end OAI
