import OAI.GroupTheory.Thompson.CorrectionData

namespace OAI

/-!
# The correction stays away from zero and fixes the outer annulus

The lower bound follows from the two orthogonal inner regions and the two
parameter cases in the outer tube region. All estimates concern the explicit
formula defined in `CorrectionData`.
-/

noncomputable section

universe uE

namespace ThompsonNonamenability.Analytic

open Set
open scoped InnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace CorrectionData

variable {C : RegularCurveData E} (D : CorrectionData C)

private theorem norm_left_le_of_perp {u w : E} (h : ⟪u, w⟫_ℝ = 0) :
    ‖u‖ ≤ ‖u + w‖ := by
  have heq := norm_add_sq_eq_norm_sq_add_norm_sq_real h
  nlinarith [norm_nonneg u, norm_nonneg (u + w), sq_nonneg ‖w‖]

private theorem norm_right_le_of_perp {u w : E} (h : ⟪u, w⟫_ℝ = 0) :
    ‖w‖ ≤ ‖u + w‖ := by
  have heq := norm_add_sq_eq_norm_sq_add_norm_sq_real h
  nlinarith [norm_nonneg w, norm_nonneg (u + w), sq_nonneg ‖u‖]

private theorem radial_perp (a : ℝ) {v w : E} (h : ⟪w, v⟫_ℝ = 0) :
    ⟪a • v, w⟫_ℝ = 0 := by
  have hvw : ⟪v, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact h
  simp only [real_inner_smul_left, hvw, mul_zero]

/-- The orthogonal formula throughout the inner half of the tube. -/
theorem inside_inner_formula (x : C.tube) (hr : ‖C.residual x‖ ≤ C.rho / 2) :
    D.inside x =
      (D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x)) •
        D.v (C.parameter x) + D.R (C.parameter x) (C.residual x) := by
  rw [D.inside_radial, chi_eq_one C.rho_pos _ hr]
  simp only [sub_self, zero_smul, one_smul, zero_add]

private theorem inside_inner_radial_lower (x : C.tube)
    (hr : ‖C.residual x‖ ≤ C.rho / 2) :
    |D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x)| ≤
      ‖D.inside x‖ := by
  rw [D.inside_inner_formula x hr]
  have h := norm_left_le_of_perp
    (radial_perp
      (D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x))
      (D.R_perp _ _ (C.residual_perp_u x)))
  simpa only [norm_smul, Real.norm_eq_abs, D.norm_v, mul_one] using h

private theorem inside_inner_residual_lower (x : C.tube)
    (hr : ‖C.residual x‖ ≤ C.rho / 2) :
    ‖C.residual x‖ ≤ ‖D.inside x‖ := by
  rw [D.inside_inner_formula x hr]
  have h := norm_right_le_of_perp
    (radial_perp
      (D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x))
      (D.R_perp _ _ (C.residual_perp_u x)))
  simpa only [D.norm_R] using h

/-- Convex interpolation between the identity and the rotation is a contraction
on each individual residual. -/
theorem residual_blend_norm_le (x : C.tube) :
    ‖(1 - chi C.rho ‖C.residual x‖) • C.residual x +
      chi C.rho ‖C.residual x‖ • D.R (C.parameter x) (C.residual x)‖ ≤
      ‖C.residual x‖ := by
  have hχ := chi_nonneg C.rho ‖C.residual x‖
  have hχ' := chi_le_one C.rho ‖C.residual x‖
  calc
    _ ≤ ‖(1 - chi C.rho ‖C.residual x‖) • C.residual x‖ +
        ‖chi C.rho ‖C.residual x‖ • D.R (C.parameter x) (C.residual x)‖ :=
      norm_add_le _ _
    _ = (1 - chi C.rho ‖C.residual x‖) * ‖C.residual x‖ +
        chi C.rho ‖C.residual x‖ * ‖C.residual x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hχ'), abs_of_nonneg hχ, D.norm_R]
    _ = ‖C.residual x‖ := by ring

/-- On the early part of the curve the rotation term vanishes identically. -/
theorem inside_early_formula (x : C.tube) (ht : C.parameter x ≤ 1) :
    D.inside x =
      (D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x)) •
        D.v (C.parameter x) + C.residual x := by
  rw [D.inside_radial, D.R_early _ ht]
  congr 1
  rw [← add_smul]
  have heq : 1 - chi C.rho ‖C.residual x‖ + chi C.rho ‖C.residual x‖ = 1 :=
    sub_add_cancel _ _
  rw [heq, one_smul]

private theorem inside_early_residual_lower (x : C.tube)
    (ht : C.parameter x ≤ 1) : ‖C.residual x‖ ≤ ‖D.inside x‖ := by
  rw [D.inside_early_formula x ht]
  have hperp : ⟪C.residual x, D.v (C.parameter x)⟫_ℝ = 0 := by
    have h := C.residual_perp_u x
    rwa [D.tangent_early _ ht] at h
  exact norm_right_le_of_perp (radial_perp _ hperp)

/-- The four tube regions give the same positive lower bound. -/
theorem inside_lower (x : C.tube) : C.rho / 4 ≤ ‖D.inside x‖ := by
  have hρ := C.rho_le
  have hρpos := C.rho_pos
  by_cases hquarter : ‖C.residual x‖ ≤ C.rho / 4
  · have hhalf : ‖C.residual x‖ ≤ C.rho / 2 := by linarith
    have h := D.inside_inner_radial_lower x hhalf
    rw [beta_eq_one C.rho_pos _ hquarter, one_mul, D.radial_eq_min] at h
    have hm : min (D.a (C.parameter x)) (-1 / 8) ≤ -1 / 8 := min_le_right _ _
    rw [abs_of_nonpos (by linarith : min (D.a (C.parameter x)) (-1 / 8) ≤ 0)] at h
    linarith
  · have hquarter' : C.rho / 4 ≤ ‖C.residual x‖ := le_of_not_ge hquarter
    by_cases hhalf : ‖C.residual x‖ ≤ C.rho / 2
    · exact hquarter'.trans (D.inside_inner_residual_lower x hhalf)
    · have hhalf' : C.rho / 2 ≤ ‖C.residual x‖ := le_of_not_ge hhalf
      by_cases ht : C.parameter x ≤ 1
      · exact hquarter'.trans (D.inside_early_residual_lower x ht)
      · have ha : 1 / 8 ≤ D.a (C.parameter x) :=
          D.a_late_lower _ (lt_of_not_ge ht)
        have hrad := D.inside_radial x
        rw [beta_eq_zero C.rho_pos _ hhalf', zero_mul, add_zero] at hrad
        let w : E := (1 - chi C.rho ‖C.residual x‖) • C.residual x +
          chi C.rho ‖C.residual x‖ • D.R (C.parameter x) (C.residual x)
        have hw : ‖w‖ ≤ ‖C.residual x‖ := D.residual_blend_norm_le x
        have htriangle : ‖D.a (C.parameter x) • D.v (C.parameter x)‖ ≤
            ‖D.inside x‖ + ‖w‖ := by
          rw [hrad]
          simpa only [add_sub_cancel_right] using
            norm_sub_le (D.a (C.parameter x) • D.v (C.parameter x) + w) w
        rw [norm_smul, Real.norm_eq_abs, D.norm_v, mul_one,
          abs_of_nonneg (by linarith : 0 ≤ D.a (C.parameter x))] at htriangle
        have hr := C.residual_norm_lt x
        linarith

/-- The explicit correction has a uniform positive norm everywhere. -/
theorem G_lower (x : E) : C.rho / 4 ≤ ‖D.G x‖ := by
  by_cases hx : x ∈ C.tube
  · rw [D.G_of_mem ⟨x, hx⟩]
    exact D.inside_lower ⟨x, hx⟩
  · rw [D.G_of_not_mem hx]
    have hdist : C.rho ≤ Metric.infDist x (range C.curve) := by
      exact le_of_not_gt hx
    have hzero : (0 : E) ∈ range C.curve := ⟨0, D.curve_zero⟩
    have hnorm : Metric.infDist x (range C.curve) ≤ ‖x‖ := by
      simpa only [dist_zero_right] using Metric.infDist_le_dist_of_mem hzero
    have hρ := C.rho_pos
    linarith

/-- Any tube point of norm at least one half has parameter on the unchanged
negative ray, so both additive corrections vanish. -/
theorem inside_outer (x : C.tube) (hx : 1 / 2 ≤ ‖(x : E)‖) :
    D.inside x = (x : E) := by
  have htriangle : ‖(x : E)‖ ≤ |D.a (C.parameter x)| + ‖C.residual x‖ := by
    calc
      ‖(x : E)‖ = ‖C.curve (C.parameter x) + C.residual x‖ :=
        congrArg norm (C.curve_add_residual x).symm
      _ ≤ ‖C.curve (C.parameter x)‖ + ‖C.residual x‖ := norm_add_le _ _
      _ = |D.a (C.parameter x)| + ‖C.residual x‖ := by rw [D.norm_curve]
  have hr := C.residual_norm_lt x
  have hρ := C.rho_le
  have haupper := D.a_upper (C.parameter x)
  have haneg : D.a (C.parameter x) < -1 / 8 := by
    by_contra hn
    have ha_lower : -1 / 8 ≤ D.a (C.parameter x) := le_of_not_gt hn
    have habs : |D.a (C.parameter x)| ≤ 5 / 16 :=
      abs_le.mpr ⟨by linarith, haupper⟩
    linarith
  have ht : C.parameter x ≤ 1 := by
    by_contra hn
    have := D.a_late_lower (C.parameter x) (lt_of_not_ge hn)
    linarith
  have hq : D.q (C.parameter x) = 0 := D.q_eq_zero haneg.le
  unfold inside change
  rw [hq, mul_zero, zero_smul, D.R_early _ ht, sub_self, smul_zero,
    add_zero, add_zero]

/-- The correction is exactly the identity on the whole outer annulus. -/
theorem G_outer (x : E) (hx : 1 / 2 ≤ ‖x‖) : D.G x = x := by
  by_cases htube : x ∈ C.tube
  · rw [D.G_of_mem ⟨x, htube⟩]
    exact D.inside_outer ⟨x, htube⟩ hx
  · exact D.G_of_not_mem htube

end CorrectionData

end ThompsonNonamenability.Analytic

end

end OAI
