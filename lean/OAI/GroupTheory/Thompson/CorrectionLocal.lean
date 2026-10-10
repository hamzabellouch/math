import OAI.GroupTheory.Thompson.CorrectionData

namespace OAI

/-!
# The local Lipschitz estimate for the explicit tube correction

The radius is the distance to the curve, so its Lipschitz constant is one.
The residual itself has local Lipschitz constant eight. Keeping these two
estimates separate gives the stated constant for the two cutoff terms.
-/

noncomputable section

universe uE

namespace ThompsonNonamenability.Analytic

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_smul_sub_smul_bound (a b : ℝ) (u v : E) :
    ‖a • u - b • v‖ ≤ |a| * ‖u - v‖ + |a - b| * ‖v‖ := by
  have hid : a • u - b • v = a • (u - v) + (a - b) • v := by
    simp only [smul_sub, sub_smul]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans_eq (by simp only [norm_smul, Real.norm_eq_abs])

namespace RegularCurveData

variable (C : RegularCurveData E)

/-- The residual length is the actual distance to the curve. -/
theorem residual_radius_lipschitz (x y : C.tube) :
    |‖C.residual x‖ - ‖C.residual y‖| ≤ ‖(x : E) - (y : E)‖ := by
  have hxy := Metric.infDist_le_infDist_add_dist
    (x := (x : E)) (y := (y : E)) (s := Set.range C.curve)
  have hyx := Metric.infDist_le_infDist_add_dist
    (x := (y : E)) (y := (x : E)) (s := Set.range C.curve)
  rw [dist_eq_norm] at hxy hyx
  rw [norm_sub_rev (y : E) (x : E)] at hyx
  rw [C.residual_norm, C.residual_norm, abs_le]
  constructor <;> linarith

end RegularCurveData

namespace CorrectionData

variable {C : RegularCurveData E} (D : CorrectionData C)

include D in
/-- Subtracting the nearest curve points costs at most another seven times
the distance, on the local parameter-comparison scale. -/
theorem residual_local_bound (x y : C.tube)
    (hxy : ‖(x : E) - (y : E)‖ < C.rho) :
    ‖C.residual x - C.residual y‖ ≤ 8 * ‖(x : E) - (y : E)‖ := by
  have ht := C.parameter_local_bound16 x y hxy
  have hc := D.curve_lipschitz (C.parameter y) (C.parameter x)
  have hc' : ‖C.curve (C.parameter x) - C.curve (C.parameter y)‖ ≤
      7 * ‖(x : E) - (y : E)‖ := by
    linarith
  have hid : C.residual x - C.residual y =
      ((x : E) - (y : E)) -
        (C.curve (C.parameter x) - C.curve (C.parameter y)) := by
    simp only [RegularCurveData.residual]
    abel
  rw [hid]
  have hn := norm_sub_le ((x : E) - (y : E))
    (C.curve (C.parameter x) - C.curve (C.parameter y))
  linarith

/-- Local Lipschitz control of the actual corrected point. -/
theorem inside_local_bound (x y : C.tube)
    (hxy : ‖(x : E) - (y : E)‖ < C.rho) :
    ‖D.inside x - D.inside y‖ ≤
      (30 + 7 / (4 * C.rho) + 3808 * C.rho) * ‖(x : E) - (y : E)‖ := by
  let d : ℝ := ‖(x : E) - (y : E)‖
  let s : ℝ := C.parameter x
  let t : ℝ := C.parameter y
  let e : E := C.residual x
  let f : E := C.residual y
  have hd : 0 ≤ d := norm_nonneg _
  have hrho : 0 < C.rho := C.rho_pos
  have he : ‖e‖ ≤ C.rho := (C.residual_norm_lt x).le
  have hf : ‖f‖ ≤ C.rho := (C.residual_norm_lt y).le
  have hst : |s - t| ≤ 16 * d := C.parameter_local_bound16 x y hxy
  have hef : ‖e - f‖ ≤ 8 * d := D.residual_local_bound x y hxy
  have hr : |‖e‖ - ‖f‖| ≤ d := C.residual_radius_lipschitz x y
  have hq : |D.q s - D.q t| ≤ 2 * d := by
    have h := D.q_lipschitz t s
    linarith
  have hv : ‖D.v s - D.v t‖ ≤ 16 * d :=
    (D.v_lipschitz t s).trans hst
  have hqv : ‖D.q s • D.v s - D.q t • D.v t‖ ≤ 9 * d := by
    calc
      ‖D.q s • D.v s - D.q t • D.v t‖
          ≤ |D.q s| * ‖D.v s - D.v t‖ +
            |D.q s - D.q t| * ‖D.v t‖ := norm_smul_sub_smul_bound _ _ _ _
      _ ≤ (7 / 16) * (16 * d) + (2 * d) * 1 :=
        add_le_add
          (mul_le_mul (D.q_bound s) hv (norm_nonneg _) (by norm_num))
          (mul_le_mul hq (le_of_eq (D.norm_v t)) (norm_nonneg _) (by positivity))
      _ = 9 * d := by ring
  have hqvt : ‖D.q t • D.v t‖ ≤ 7 / 16 := by
    simpa only [norm_smul, Real.norm_eq_abs, D.norm_v, mul_one] using D.q_bound t
  have hbeta : |beta C.rho ‖e‖ - beta C.rho ‖f‖| ≤ (4 / C.rho) * d :=
    (beta_abs_sub_le hrho _ _).trans
      (mul_le_mul_of_nonneg_left hr (by positivity))
  have hchi : |chi C.rho ‖e‖ - chi C.rho ‖f‖| ≤ (2 / C.rho) * d :=
    (chi_abs_sub_le hrho _ _).trans
      (mul_le_mul_of_nonneg_left hr (by positivity))
  have hbeta_abs : |beta C.rho ‖e‖| ≤ 1 := by
    rw [abs_of_nonneg (beta_nonneg _ _)]
    exact beta_le_one _ _
  have hchi_abs : |chi C.rho ‖e‖| ≤ 1 := by
    rw [abs_of_nonneg (chi_nonneg _ _)]
    exact chi_le_one _ _
  have hradial :
      ‖(beta C.rho ‖e‖ * D.q s) • D.v s -
        (beta C.rho ‖f‖ * D.q t) • D.v t‖ ≤
      (9 + 7 / (4 * C.rho)) * d := by
    rw [mul_smul, mul_smul]
    calc
      ‖beta C.rho ‖e‖ • (D.q s • D.v s) -
          beta C.rho ‖f‖ • (D.q t • D.v t)‖
          ≤ |beta C.rho ‖e‖| * ‖D.q s • D.v s - D.q t • D.v t‖ +
            |beta C.rho ‖e‖ - beta C.rho ‖f‖| * ‖D.q t • D.v t‖ :=
        norm_smul_sub_smul_bound _ _ _ _
      _ ≤ 1 * (9 * d) + ((4 / C.rho) * d) * (7 / 16) :=
        add_le_add
          (mul_le_mul hbeta_abs hqv (norm_nonneg _) zero_le_one)
          (mul_le_mul hbeta hqvt (norm_nonneg _) (by positivity))
      _ = (9 + 7 / (4 * C.rho)) * d := by
        field_simp [ne_of_gt hrho] ; ring
  have hrotation : ‖D.R s f - D.R t f‖ ≤ 3808 * C.rho * d := by
    calc
      ‖D.R s f - D.R t f‖ ≤ 238 * |s - t| * ‖f‖ := D.R_lipschitz t s f
      _ ≤ (238 * (16 * d)) * C.rho :=
        mul_le_mul (mul_le_mul_of_nonneg_left hst (by norm_num)) hf
          (norm_nonneg _) (by positivity)
      _ = 3808 * C.rho * d := by ring
  have hdefect_norm : ‖D.R t f - f‖ ≤ 2 * C.rho := by
    have h := norm_sub_le (D.R t f) f
    rw [D.norm_R] at h
    linarith
  have hdefect : ‖(D.R s e - e) - (D.R t f - f)‖ ≤
      (16 + 3808 * C.rho) * d := by
    have hid : (D.R s e - e) - (D.R t f - f) =
        (D.R s (e - f) + (D.R s f - D.R t f)) - (e - f) := by
      rw [map_sub]
      abel
    calc
      ‖(D.R s e - e) - (D.R t f - f)‖
          = ‖(D.R s (e - f) + (D.R s f - D.R t f)) - (e - f)‖ := by rw [hid]
      _ ≤ ‖D.R s (e - f) + (D.R s f - D.R t f)‖ + ‖e - f‖ := norm_sub_le _ _
      _ ≤ (‖D.R s (e - f)‖ + ‖D.R s f - D.R t f‖) + ‖e - f‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = (‖e - f‖ + ‖D.R s f - D.R t f‖) + ‖e - f‖ := by rw [D.norm_R]
      _ ≤ (8 * d + 3808 * C.rho * d) + 8 * d :=
        add_le_add (add_le_add hef hrotation) hef
      _ = (16 + 3808 * C.rho) * d := by ring
  have hangular :
      ‖chi C.rho ‖e‖ • (D.R s e - e) - chi C.rho ‖f‖ • (D.R t f - f)‖ ≤
        (20 + 3808 * C.rho) * d := by
    calc
      ‖chi C.rho ‖e‖ • (D.R s e - e) - chi C.rho ‖f‖ • (D.R t f - f)‖
          ≤ |chi C.rho ‖e‖| * ‖(D.R s e - e) - (D.R t f - f)‖ +
            |chi C.rho ‖e‖ - chi C.rho ‖f‖| * ‖D.R t f - f‖ :=
        norm_smul_sub_smul_bound _ _ _ _
      _ ≤ 1 * ((16 + 3808 * C.rho) * d) + ((2 / C.rho) * d) * (2 * C.rho) :=
        add_le_add
          (mul_le_mul hchi_abs hdefect (norm_nonneg _) zero_le_one)
          (mul_le_mul hchi hdefect_norm (norm_nonneg _) (by positivity))
      _ = (20 + 3808 * C.rho) * d := by
        field_simp [ne_of_gt hrho] ; ring
  have hchange : ‖D.change x - D.change y‖ ≤
      (29 + 7 / (4 * C.rho) + 3808 * C.rho) * d := by
    have hid : D.change x - D.change y =
        ((beta C.rho ‖e‖ * D.q s) • D.v s -
          (beta C.rho ‖f‖ * D.q t) • D.v t) +
        (chi C.rho ‖e‖ • (D.R s e - e) -
          chi C.rho ‖f‖ • (D.R t f - f)) := by
      dsimp [change, s, t, e, f]
      abel
    rw [hid]
    exact (norm_add_le _ _).trans ((add_le_add hradial hangular).trans_eq (by ring))
  have hid : D.inside x - D.inside y =
      ((x : E) - (y : E)) + (D.change x - D.change y) := by
    simp only [inside]
    abel
  rw [hid]
  calc
    ‖((x : E) - (y : E)) + (D.change x - D.change y)‖
        ≤ d + ‖D.change x - D.change y‖ := norm_add_le _ _
    _ ≤ d + (29 + 7 / (4 * C.rho) + 3808 * C.rho) * d := add_le_add le_rfl hchange
    _ = (30 + 7 / (4 * C.rho) + 3808 * C.rho) * ‖(x : E) - (y : E)‖ := by
      change d + (29 + 7 / (4 * C.rho) + 3808 * C.rho) * d =
        (30 + 7 / (4 * C.rho) + 3808 * C.rho) * d
      ring

end CorrectionData

end ThompsonNonamenability.Analytic

end

end OAI
