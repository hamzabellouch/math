import OAI.Combinatorics.ProgressionColoring.SmallBoxAffinity

namespace OAI

/-!
# Real-representative lemmas for the outer-color dichotomy

The integer congruences here are the concrete meaning of equality modulo one.
In particular, the heavy-interval estimate uses only its two endpoint
representatives and does not assume that the path between them avoids a cut.
-/

namespace QuantitativeVanDerWaerden

theorem real_eq_of_integer_difference_small {a b : ℝ}
    (hint : ∃ z : ℤ, a - b = (z : ℝ)) (hsmall : |a - b| < 1) : a = b := by
  obtain ⟨z, hz⟩ := hint
  rw [hz] at hsmall
  have hz0 := integer_zero_of_abs_lt_one hsmall
  simp only [hz0, Int.cast_zero] at hz
  linarith

/-- The short displacement in the two coordinate systems agrees over the reals. -/
theorem dilation_drift_eq {u v lam A B : ℝ}
    (hint : ∃ z : ℤ, v - lam * u = (z : ℝ))
    (hv : |v| ≤ A) (hu : |lam * u| ≤ B) (hsmall : A + B < 1) : v = lam * u := by
  apply real_eq_of_integer_difference_small hint
  exact lt_of_le_of_lt ((abs_sub v (lam * u)).trans (add_le_add hv hu)) hsmall

/-- Endpoint congruence and short total drift give equality before reduction modulo one. -/
theorem heavy_endpoint_eq {Δ a v L T : ℝ}
    (hint : ∃ z : ℤ, Δ - a * v = (z : ℝ))
    (hΔ : |Δ| ≤ L) (hv : |a * v| ≤ T) (hsmall : L + T < 1) : Δ = a * v := by
  apply real_eq_of_integer_difference_small hint
  exact lt_of_le_of_lt ((abs_sub Δ (a * v)).trans (add_le_add hΔ hv)) hsmall

theorem heavy_interval_drift_div {Δ a v L T : ℝ}
    (ha : 0 < a) (hint : ∃ z : ℤ, Δ - a * v = (z : ℝ))
    (hΔ : |Δ| ≤ L) (hv : |a * v| ≤ T) (hsmall : L + T < 1) : |v| ≤ L / a := by
  have heq := heavy_endpoint_eq hint hΔ hv hsmall
  have hmul : a * |v| ≤ L := by
    simpa only [heq, abs_mul, abs_of_pos ha] using hΔ
  exact (le_div_iff₀ ha).2 (by simpa only [mul_comm] using hmul)

/-- The relative-width estimate for every heavy interval in the progression. -/
theorem heavy_interval_relative_drift {Δ a v L T k M : ℝ}
    (hk : 0 < k) (hM : 0 < M) (ha : k / (2 * M) ≤ a)
    (hint : ∃ z : ℤ, Δ - a * v = (z : ℝ))
    (hΔ : |Δ| ≤ L) (hv : |a * v| ≤ T) (hsmall : L + T < 1) :
    |v| ≤ (2 * M / k) * L := by
  have h2M : 0 < 2 * M := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le (div_pos hk h2M) ha
  have heq := heavy_endpoint_eq hint hΔ hv hsmall
  have hmul : a * |v| ≤ L := by
    simpa only [heq, abs_mul, abs_of_pos ha0] using hΔ
  have hak : k ≤ a * (2 * M) := (div_le_iff₀ h2M).1 ha
  have hfinal : |v| * k ≤ 2 * M * L := by
    calc
      |v| * k ≤ |v| * (a * (2 * M)) :=
        mul_le_mul_of_nonneg_left hak (abs_nonneg v)
      _ = (2 * M) * (a * |v|) := by ring
      _ ≤ (2 * M) * L := mul_le_mul_of_nonneg_left hmul h2M.le
  calc
    |v| ≤ (2 * M * L) / k := (le_div_iff₀ hk).2 hfinal
    _ = (2 * M / k) * L := by ring

/-- A discrete nonzero step makes every cut-near adaptive interval narrower
than one step. -/
theorem short_cut_interval_lt_step {H k ρ α width w : ℝ}
    (hH : 0 ≤ H) (hw : w ≠ 0) (hα : α ≤ |w|) (hρ : ρ ≤ k * |w|)
    (hwidth : width ≤ 2 * H * (ρ + α)) (hsmall : 2 * H * (k + 1) < 1) :
    width < |w| := by
  have hstep : 0 < |w| := abs_pos.mpr hw
  have hsum : ρ + α ≤ (k + 1) * |w| := by nlinarith
  calc
    width ≤ 2 * H * (ρ + α) := hwidth
    _ ≤ 2 * H * ((k + 1) * |w|) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2 * H * (k + 1)) * |w| := by ring
    _ < 1 * |w| := mul_lt_mul_of_pos_right hsmall hstep
    _ = |w| := one_mul _

theorem abs_nat_difference_ge_one {a b : ℕ} (hab : a ≠ b) :
    (1 : ℝ) ≤ |(a : ℝ) - b| := by
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_of_nonpos (by linarith : (a : ℝ) - b ≤ 0)]
    linarith
  · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_of_nonneg (by linarith : 0 ≤ (a : ℝ) - b)]
    linarith

/-- Distinct samples of a short nonzero real step cannot occupy an interval
narrower than the step, even if their representatives cross the cut. -/
theorem short_step_not_same_interval {a b k : ℕ} {za zb w : ℝ}
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hmotion : (k : ℝ) * |w| < 1 / 2)
    (hint : ∃ z : ℤ, (za - zb) - ((a : ℝ) - b) * w = (z : ℝ))
    (hnarrow : |za - zb| < |w|) : False := by
  have hk : 1 ≤ k := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le a) hak)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hak' : (a : ℝ) ≤ k := by exact_mod_cast hak.le
  have hbk' : (b : ℝ) ≤ k := by exact_mod_cast hbk.le
  have hw0 := abs_nonneg w
  have hwsmall : |w| < 1 / 2 := by nlinarith
  have hdiff : |(a : ℝ) - b| ≤ k := abs_le.mpr ⟨by linarith, by linarith⟩
  have hprod : |((a : ℝ) - b) * w| < 1 / 2 := by
    rw [abs_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hdiff hw0) hmotion
  have hzero : za - zb = ((a : ℝ) - b) * w := by
    apply real_eq_of_integer_difference_small hint
    have hh := abs_sub (za - zb) (((a : ℝ) - b) * w)
    linarith
  have hlower : |w| ≤ |((a : ℝ) - b) * w| := by
    rw [abs_mul]
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (abs_nat_difference_ge_one hab) hw0)
  rw [hzero] at hnarrow
  exact (not_lt_of_ge hlower) hnarrow

end QuantitativeVanDerWaerden

end OAI
