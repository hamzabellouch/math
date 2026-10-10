import OAI.Probability.FreeIsing.Estimates.EndpointSums

namespace OAI

noncomputable section

namespace Problem367

theorem endpoint_two_term_le {A B u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    A * u + B * v ≤ max A B * (u + v) := by
  calc
    A * u + B * v ≤ max A B * u + max A B * v :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hv)
    _ = _ := by ring

theorem cutoff_square_le {R K x y : ℝ} (hR0 : 0 ≤ R) (hK : 0 ≤ K)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hR : R ≤ K * (x + y)) :
    R ^ 2 ≤ 2 * K ^ 2 * (x ^ 2 + y ^ 2) := by
  calc
    R ^ 2 ≤ (K * (x + y)) ^ 2 :=
      (sq_le_sq₀ hR0 (mul_nonneg hK (add_nonneg hx hy))).mpr hR
    _ = K ^ 2 * (x + y) ^ 2 := by ring
    _ ≤ K ^ 2 * (2 * (x ^ 2 + y ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg K)
      nlinarith [sq_nonneg (x - y)]
    _ = _ := by ring

theorem add_mul_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) * Real.sqrt (x + y) ≤ 4 * (x * Real.sqrt x + y * Real.sqrt y) := by
  have haux : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u ≤ v →
      (u + v) * Real.sqrt (u + v) ≤ 4 * (u * Real.sqrt u + v * Real.sqrt v) := by
    intro u v hu hv huv
    have hsum : u + v ≤ 2 * v := by linarith
    have hsqrt : Real.sqrt (u + v) ≤ 2 * Real.sqrt v := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · rw [mul_pow, Real.sq_sqrt hv]
        nlinarith
    calc
      (u + v) * Real.sqrt (u + v) ≤ (2 * v) * (2 * Real.sqrt v) :=
        mul_le_mul hsum hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ ≤ 4 * (u * Real.sqrt u + v * Real.sqrt v) := by
        nlinarith [mul_nonneg hu (Real.sqrt_nonneg u)]
  rcases le_total x y with h | h
  · exact haux x y hx hy h
  · simpa [add_comm] using haux y x hy hx h

theorem cutoff_mul_sqrt_le {R K x y : ℝ} (_hR0 : 0 ≤ R) (hK : 0 ≤ K)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hR : R ≤ K * (x + y)) :
    R * Real.sqrt R ≤
      4 * K * Real.sqrt K * (x * Real.sqrt x + y * Real.sqrt y) := by
  calc
    R * Real.sqrt R ≤ (K * (x + y)) * Real.sqrt (K * (x + y)) :=
      mul_le_mul hR (Real.sqrt_le_sqrt hR) (Real.sqrt_nonneg _) (by positivity)
    _ = (K * Real.sqrt K) * ((x + y) * Real.sqrt (x + y)) := by
      rw [Real.sqrt_mul hK]
      ring
    _ ≤ (K * Real.sqrt K) * (4 * (x * Real.sqrt x + y * Real.sqrt y)) :=
      mul_le_mul_of_nonneg_left (add_mul_sqrt_add_le hx hy) (by positivity)
    _ = _ := by ring

theorem quadratic_endpoint_scale {F A B E S V R K x y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hR0 : 0 ≤ R) (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hR : R ≤ K * (x + y))
    (hF : F ≤ A * S * R ^ 2 + B * S * x ^ 2 + E * V ^ 2) :
    F ≤ max (2 * A * K ^ 2 + B) E *
      (S * (x ^ 2 + y ^ 2) + V ^ 2) := by
  have hfirst := mul_le_mul_of_nonneg_left (cutoff_square_le hR0 hK hx hy hR)
    (mul_nonneg hA hS)
  have hsecond : B * S * x ^ 2 ≤ B * S * (x ^ 2 + y ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB hS)
    nlinarith [sq_nonneg y]
  calc
    F ≤ A * S * (2 * K ^ 2 * (x ^ 2 + y ^ 2)) +
        B * S * (x ^ 2 + y ^ 2) + E * V ^ 2 :=
      hF.trans (add_le_add (add_le_add hfirst hsecond) le_rfl)
    _ = (2 * A * K ^ 2 + B) * (S * (x ^ 2 + y ^ 2)) + E * V ^ 2 := by ring
    _ ≤ _ := endpoint_two_term_le (by positivity) (sq_nonneg V)

theorem linear_endpoint_scale {F A B E V R K x y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hR : R ≤ K * (x + y))
    (hF : F ≤ A * V * R + B * V * x + E * V ^ 2) :
    F ≤ max (A * K + B) E * (V * (x + y) + V ^ 2) := by
  have hfirst := mul_le_mul_of_nonneg_left hR (mul_nonneg hA hV)
  have hsecond : B * V * x ≤ B * V * (x + y) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB hV)
    linarith
  calc
    F ≤ A * V * (K * (x + y)) + B * V * (x + y) + E * V ^ 2 :=
      hF.trans (add_le_add (add_le_add hfirst hsecond) le_rfl)
    _ = (A * K + B) * (V * (x + y)) + E * V ^ 2 := by ring
    _ ≤ _ := endpoint_two_term_le (by positivity) (sq_nonneg V)

theorem sqrt_endpoint_scale {F A B E S V R K x y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hR0 : 0 ≤ R) (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hR : R ≤ K * (x + y))
    (hF : F ≤ A * Real.sqrt S * (R * Real.sqrt R) +
      B * Real.sqrt S * (x * Real.sqrt x) + E * V) :
    F ≤ max (4 * A * K * Real.sqrt K + B) E *
      (Real.sqrt S * (x * Real.sqrt x + y * Real.sqrt y) + V) := by
  have hfirst := mul_le_mul_of_nonneg_left (cutoff_mul_sqrt_le hR0 hK hx hy hR)
    (mul_nonneg hA (Real.sqrt_nonneg S))
  have hsecond : B * Real.sqrt S * (x * Real.sqrt x) ≤
      B * Real.sqrt S * (x * Real.sqrt x + y * Real.sqrt y) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (Real.sqrt_nonneg S))
    nlinarith [mul_nonneg hy (Real.sqrt_nonneg y)]
  calc
    F ≤ A * Real.sqrt S *
        (4 * K * Real.sqrt K * (x * Real.sqrt x + y * Real.sqrt y)) +
        B * Real.sqrt S * (x * Real.sqrt x + y * Real.sqrt y) + E * V :=
      hF.trans (add_le_add (add_le_add hfirst hsecond) le_rfl)
    _ = (4 * A * K * Real.sqrt K + B) *
        (Real.sqrt S * (x * Real.sqrt x + y * Real.sqrt y)) + E * V := by ring
    _ ≤ _ := endpoint_two_term_le (by positivity) hV

theorem tsum_scaled_path_attenuation_le (k : ℕ) {c ω : ℝ}
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) :
    (∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-(c * ω) * n)) ≤
      (k.factorial : ℝ) * (2 / min c 1) ^ (k + 1) * (ω⁻¹) ^ (k + 1) := by
  have hm : 0 < min c 1 := lt_min hc zero_lt_one
  have hrate : 0 < min c 1 * ω := mul_pos hm hω
  have hrate1 : min c 1 * ω ≤ 1 :=
    (mul_le_mul_of_nonneg_right (min_le_right c 1) hω.le).trans (by simpa using hω1)
  calc
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-(min c 1 * ω) * n) := by
      apply Summable.tsum_le_tsum _ (summable_path_attenuation k (mul_pos hc hω))
        (summable_path_attenuation k hrate)
      intro n
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right (min_le_left c 1) hω.le
      have := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) n)
      linarith
    _ ≤ (k.factorial : ℝ) * (2 / (min c 1 * ω)) ^ (k + 1) :=
      tsum_path_attenuation_small_le k hrate hrate1
    _ = _ := by simp [div_eq_mul_inv, mul_inv_rev, mul_pow, mul_assoc, mul_comm, mul_left_comm]

theorem tsum_scaled_sqrt_path_attenuation_le {c ω : ℝ}
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) :
    (∑' n : ℕ, Real.sqrt n * Real.exp (-(c * ω) * n)) ≤
      (3 / (min c 1 * Real.sqrt (min c 1))) * (ω⁻¹ * Real.sqrt (ω⁻¹)) := by
  have hm : 0 < min c 1 := lt_min hc zero_lt_one
  have hrate : 0 < min c 1 * ω := mul_pos hm hω
  have hrate1 : min c 1 * ω ≤ 1 :=
    (mul_le_mul_of_nonneg_right (min_le_right c 1) hω.le).trans (by simpa using hω1)
  calc
    _ ≤ ∑' n : ℕ, Real.sqrt n * Real.exp (-(min c 1 * ω) * n) := by
      apply Summable.tsum_le_tsum _ (summable_sqrt_path_attenuation (mul_pos hc hω))
        (summable_sqrt_path_attenuation hrate)
      intro n
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right (min_le_left c 1) hω.le
      have := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) n)
      linarith
    _ ≤ 3 / ((min c 1 * ω) * Real.sqrt (min c 1 * ω)) :=
      tsum_sqrt_path_attenuation_le hrate hrate1
    _ = _ := by
      rw [Real.sqrt_mul hm.le, Real.sqrt_inv]
      field_simp

theorem pathCutoff_square_le {C ω I : ℝ}
    (hC : 0 ≤ C) (hω : 0 < ω) (hω1 : ω ≤ 1) (hI : 1 ≤ I) :
    (pathCutoff C ω I : ℝ) ^ 2 ≤
      2 * (C + 1) ^ 2 * ((ω⁻¹) ^ 2 + (Real.log I) ^ 2) := by
  exact cutoff_square_le (Nat.cast_nonneg _) (by positivity) (by positivity)
    (Real.log_nonneg hI) (pathCutoff_le hC hω hω1 hI)

theorem pathCutoff_mul_sqrt_le {C ω I : ℝ}
    (hC : 0 ≤ C) (hω : 0 < ω) (hω1 : ω ≤ 1) (hI : 1 ≤ I) :
    (pathCutoff C ω I : ℝ) * Real.sqrt (pathCutoff C ω I) ≤
      4 * (C + 1) * Real.sqrt (C + 1) *
        (ω⁻¹ * Real.sqrt (ω⁻¹) + Real.log I * Real.sqrt (Real.log I)) := by
  exact cutoff_mul_sqrt_le (Nat.cast_nonneg _) (by positivity) (by positivity)
    (Real.log_nonneg hI) (pathCutoff_le hC hω hω1 hI)

end Problem367

end

end OAI
