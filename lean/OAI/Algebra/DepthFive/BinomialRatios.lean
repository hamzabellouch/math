import Mathlib

namespace OAI

/-! Binomial dimension estimates for the intermediate spaces in the
differentiation--multiplication rank argument. -/

namespace Problem335

/-- Dimension of homogeneous degree `t` polynomials in `r` variables,
for a positive number of variables. -/
def homogeneousDim (r t : ℕ) : ℕ := (r + t - 1).choose t

theorem homogeneousDim_pos {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    0 < homogeneousDim r t := by
  apply Nat.choose_pos
  omega

@[simp] theorem homogeneousDim_zero (r : ℕ) : homogeneousDim r 0 = 1 := by
  simp [homogeneousDim]

theorem homogeneousDim_succ_mul {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    homogeneousDim r (t + 1) * (t + 1) = homogeneousDim r t * (r + t) := by
  have h := Nat.add_one_mul_choose_eq (r + t - 1) t
  have hrt : r + t - 1 + 1 = r + t := by omega
  have hrt' : r + (t + 1) - 1 = r + t := by omega
  simpa only [homogeneousDim, hrt, hrt', Nat.mul_comm] using h.symm

theorem homogeneousDim_succ_cast {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    (homogeneousDim r (t + 1) : ℝ) =
      (homogeneousDim r t : ℝ) * ((r : ℝ) + t) / ((t : ℝ) + 1) := by
  apply (eq_div_iff (by positivity : (t : ℝ) + 1 ≠ 0)).2
  exact_mod_cast homogeneousDim_succ_mul hr t

theorem homogeneousDim_cast_eq_succ {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    (homogeneousDim r t : ℝ) =
      (homogeneousDim r (t + 1) : ℝ) * ((t : ℝ) + 1) / ((r : ℝ) + t) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  apply (eq_div_iff (by positivity : (r : ℝ) + t ≠ 0)).2
  exact_mod_cast (homogeneousDim_succ_mul hr t).symm

/-- Moving down one degree costs at most the largest ratio on the interval. -/
theorem homogeneousDim_down_step {r a t : ℕ} (hr : 1 ≤ r)
    (ht : t + 1 ≤ a) :
    (homogeneousDim r t : ℝ) ≤
      (homogeneousDim r (t + 1) : ℝ) *
        ((a : ℝ) / ((a : ℝ) + r - 1)) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ht' : (t : ℝ) + 1 ≤ a := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hden : (0 : ℝ) < (a : ℝ) + r - 1 := by linarith
  have hratio : ((t : ℝ) + 1) / ((r : ℝ) + t) ≤
      (a : ℝ) / ((a : ℝ) + r - 1) := by
    apply (div_le_div_iff₀ (by linarith) hden).2
    nlinarith
  rw [homogeneousDim_cast_eq_succ hr t, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)

/-- Moving up one degree costs at most the initial coarse ratio. -/
theorem homogeneousDim_up_step {r b t : ℕ} (hr : 1 ≤ r)
    (hb : 0 < b) (ht : b ≤ t) :
    (homogeneousDim r (t + 1) : ℝ) ≤
      (homogeneousDim r t : ℝ) * (((b : ℝ) + r) / b) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have ht' : (b : ℝ) ≤ t := by exact_mod_cast ht
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hratio : ((r : ℝ) + t) / ((t : ℝ) + 1) ≤
      ((b : ℝ) + r) / b := by
    apply (div_le_div_iff₀ (by positivity) hb').2
    nlinarith
  rw [homogeneousDim_succ_cast hr t, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)

/-- Iterating the descending degree ratio. -/
theorem homogeneousDim_down_bound {r a : ℕ} (hr : 1 ≤ r) (I : ℕ) :
    I ≤ a → (homogeneousDim r (a - I) : ℝ) ≤
      (homogeneousDim r a : ℝ) * ((a : ℝ) / ((a : ℝ) + r - 1)) ^ I := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hq : 0 ≤ (a : ℝ) / ((a : ℝ) + r - 1) := by
    apply div_nonneg (Nat.cast_nonneg _)
    linarith [Nat.cast_nonneg (α := ℝ) a]
  induction I with
  | zero => simp
  | succ I ih =>
      intro hI
      have hindex : a - (I + 1) + 1 = a - I := by omega
      have hstep := homogeneousDim_down_step (a := a) (t := a - (I + 1)) hr
        (by omega)
      rw [hindex] at hstep
      calc
        (homogeneousDim r (a - (I + 1)) : ℝ) ≤
            (homogeneousDim r (a - I) : ℝ) *
              ((a : ℝ) / ((a : ℝ) + r - 1)) := hstep
        _ ≤ ((homogeneousDim r a : ℝ) *
              ((a : ℝ) / ((a : ℝ) + r - 1)) ^ I) *
              ((a : ℝ) / ((a : ℝ) + r - 1)) :=
          mul_le_mul_of_nonneg_right (ih (by omega)) hq
        _ = (homogeneousDim r a : ℝ) *
              ((a : ℝ) / ((a : ℝ) + r - 1)) ^ (I + 1) := by
          rw [pow_succ, mul_assoc]

/-- Iterating the ascending degree ratio. -/
theorem homogeneousDim_up_bound {r b : ℕ} (hr : 1 ≤ r) (hb : 0 < b) (J : ℕ) :
    (homogeneousDim r (b + J) : ℝ) ≤
      (homogeneousDim r b : ℝ) * (((b : ℝ) + r) / b) ^ J := by
  have hq : 0 ≤ ((b : ℝ) + r) / b := by positivity
  induction J with
  | zero => simp
  | succ J ih =>
      calc
        (homogeneousDim r (b + (J + 1)) : ℝ) ≤
            (homogeneousDim r (b + J) : ℝ) * (((b : ℝ) + r) / b) := by
          simpa only [Nat.add_assoc] using
            homogeneousDim_up_step hr hb (Nat.le_add_right b J)
        _ ≤ ((homogeneousDim r b : ℝ) * (((b : ℝ) + r) / b) ^ J) *
              (((b : ℝ) + r) / b) := mul_le_mul_of_nonneg_right ih hq
        _ = (homogeneousDim r b : ℝ) * (((b : ℝ) + r) / b) ^ (J + 1) := by
          rw [pow_succ, mul_assoc]

theorem homogeneousDim_down_ratio {r a I : ℕ} (hr : 1 ≤ r) (hI : I ≤ a) :
    (homogeneousDim r (a - I) : ℝ) / homogeneousDim r a ≤
      ((a : ℝ) / ((a : ℝ) + r - 1)) ^ I := by
  have hd : (0 : ℝ) < homogeneousDim r a := by
    exact_mod_cast homogeneousDim_pos hr a
  apply (div_le_iff₀ hd).2
  simpa only [mul_comm] using homogeneousDim_down_bound hr I hI

theorem homogeneousDim_up_ratio {r b : ℕ} (hr : 1 ≤ r) (hb : 0 < b) (J : ℕ) :
    (homogeneousDim r (b + J) : ℝ) / homogeneousDim r b ≤
      (((b : ℝ) + r) / b) ^ J := by
  have hd : (0 : ℝ) < homogeneousDim r b := by
    exact_mod_cast homogeneousDim_pos hr b
  apply (div_le_iff₀ hd).2
  simpa only [mul_comm] using homogeneousDim_up_bound hr hb J

/-- The product of the two degree-space ratios bounds the relative size
of the intermediate space in the mixed operator factorization. -/
theorem intermediate_dimension_ratio_le {v u a b I J : ℕ}
    (hv : 1 ≤ v) (hu : 1 ≤ u) (hb : 0 < b) (hI : I ≤ a) :
    ((homogeneousDim v (a - I) : ℝ) * homogeneousDim u (b + J)) /
        ((homogeneousDim v a : ℝ) * homogeneousDim u b) ≤
      ((a : ℝ) / ((a : ℝ) + v - 1)) ^ I *
        (((b : ℝ) + u) / b) ^ J := by
  rw [← div_mul_div_comm]
  apply mul_le_mul (homogeneousDim_down_ratio hv hI)
    (homogeneousDim_up_ratio hu hb J)
  · positivity
  · apply pow_nonneg
    apply div_nonneg (Nat.cast_nonneg _)
    have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
    linarith [Nat.cast_nonneg (α := ℝ) a]

/-- The slope condition balances the cost of multiplication against the
cost of differentiation. -/
theorem ratio_power_slope_bound {α β ρ : ℝ} (hα : 0 < α)
    (hβ : α ^ ρ ≤ β) (I J : ℕ) :
    α ^ I / β ^ J ≤ α ^ ((I : ℝ) - ρ * J) := by
  have hp : (α ^ ρ) ^ J ≤ β ^ J :=
    pow_le_pow_left₀ (Real.rpow_nonneg hα.le ρ) hβ J
  calc
    α ^ I / β ^ J ≤ α ^ I / (α ^ ρ) ^ J :=
      div_le_div_of_nonneg_left (pow_nonneg hα.le I)
        (pow_pos (Real.rpow_pos_of_pos hα ρ) J) hp
    _ = α ^ ((I : ℝ) - ρ * J) := by
      rw [Real.rpow_sub hα, Real.rpow_natCast, Real.rpow_mul_natCast hα.le]

/-- A bounded rounding correction can be pulled out before using the
slope condition. -/
theorem corrected_ratio_power_bound {α β ρ η : ℝ} (hα : 0 < α)
    (hβ : α ^ ρ ≤ β) {I J : ℕ} (hη : η ^ I ≤ 2) :
    (α * η) ^ I * (β⁻¹) ^ J ≤ 2 * α ^ ((I : ℝ) - ρ * J) := by
  have hβpos : 0 < β := lt_of_lt_of_le (Real.rpow_pos_of_pos hα ρ) hβ
  calc
    (α * η) ^ I * (β⁻¹) ^ J = η ^ I * (α ^ I / β ^ J) := by
      rw [mul_pow, inv_pow, div_eq_mul_inv]
      ring
    _ ≤ 2 * α ^ ((I : ℝ) - ρ * J) :=
      mul_le_mul hη (ratio_power_slope_bound hα hβ I J) (by positivity) (by norm_num)

/-- The intermediate homogeneous-space bound in the balanced slope form.
The only analytic hypothesis left is the small rounding correction. -/
theorem intermediate_dimension_slope_bound {v u a b I J : ℕ} {ρ : ℝ}
    (hv : 1 ≤ v) (hu : 1 ≤ u) (ha : 0 < a) (hb : 0 < b) (hI : I ≤ a)
    (hβ : ((a : ℝ) / ((a : ℝ) + v)) ^ ρ ≤ (b : ℝ) / ((b : ℝ) + u))
    (hcorr : ((1 - 1 / ((a : ℝ) + v))⁻¹) ^ I ≤ 2) :
    ((homogeneousDim v (a - I) : ℝ) * homogeneousDim u (b + J)) /
        ((homogeneousDim v a : ℝ) * homogeneousDim u b) ≤
      2 * ((a : ℝ) / ((a : ℝ) + v)) ^ ((I : ℝ) - ρ * J) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hsum : (a : ℝ) + v ≠ 0 := by linarith
  have hsum' : (a : ℝ) + v - 1 ≠ 0 := by linarith
  have hratio : (a : ℝ) / ((a : ℝ) + v - 1) =
      ((a : ℝ) / ((a : ℝ) + v)) * (1 - 1 / ((a : ℝ) + v))⁻¹ := by
    field_simp
  have hbeta : ((b : ℝ) + u) / b = ((b : ℝ) / ((b : ℝ) + u))⁻¹ := by
    rw [inv_div]
  calc
    _ ≤ ((a : ℝ) / ((a : ℝ) + v - 1)) ^ I * (((b : ℝ) + u) / b) ^ J :=
      intermediate_dimension_ratio_le hv hu hb hI
    _ ≤ _ := by
      rw [hratio, hbeta]
      exact corrected_ratio_power_bound (by positivity) hβ hcorr

end Problem335

end OAI
