import OAI.Algebra.DepthFive.AlphaParameters

namespace OAI

noncomputable section
namespace Problem335.LowerParameters

theorem b_scale_lower {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 4 ≤ (b n : ℝ) := by
  apply (a_scale_lower hn).trans
  exact_mod_cast a_le_b (by omega : 4 ≤ n)

/-- The eventual beta bound supplies the matching upper growth estimate for `b`. -/
theorem b_scale_upper_of_beta_bound {n : ℕ} (hn : 16 ≤ n)
    (hbeta : beta n ≤ 2 / Real.sqrt (n : ℝ)) :
    (b n : ℝ) ≤ 4 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
  have hs := sqrt_ge_four hn
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hb : (0 : ℝ) < b n := by exact_mod_cast b_pos (by omega : 4 ≤ n)
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos (by omega : 4 ≤ n)
  have huupper : (u n : ℝ) ≤ (n : ℝ) ^ 3 := by exact_mod_cast u_le_cube n
  have hmul : (b n : ℝ) * Real.sqrt (n : ℝ) ≤ 2 * ((b n : ℝ) + (u n : ℝ)) :=
    (div_le_div_iff₀ (add_pos hb hu) hspos).mp hbeta
  have hhalf : (b n : ℝ) * Real.sqrt (n : ℝ) ≤ 4 * (u n : ℝ) := by
    nlinarith [mul_nonneg hb.le (show 0 ≤ Real.sqrt (n : ℝ) - 4 by linarith)]
  have heq : (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) ^ 3 := by
    calc
      _ = (n : ℝ) ^ 2 * (Real.sqrt (n : ℝ)) ^ 2 := by ring
      _ = (n : ℝ) ^ 3 := by rw [Real.sq_sqrt (by positivity)]; ring
  have hfinal : (b n : ℝ) * Real.sqrt (n : ℝ) ≤
      (4 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) := by nlinarith
  exact le_of_mul_le_mul_right hfinal hspos

theorem sq_div_b_le {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 / (b n : ℝ) ≤ 4 / Real.sqrt (n : ℝ) := by
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos (by omega : 4 ≤ n)
  have hab : (a n : ℝ) ≤ b n := by exact_mod_cast a_le_b (by omega : 4 ≤ n)
  exact (div_le_div_of_nonneg_left (sq_nonneg _) ha hab).trans (sq_div_a_le hn)

theorem sq_div_u_le {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 / (u n : ℝ) ≤ 2 / (n : ℝ) := by
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos (by omega : 4 ≤ n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (div_le_div_iff₀ hu hnR).mpr
  have h : (n : ℝ) ^ 3 ≤ 2 * (u n : ℝ) := by exact_mod_cast cube_le_two_mul_u n
  nlinarith

/-- A concrete bound for the combined occupation-comparison error in both groups. -/
theorem occupation_parameter_loss_le {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 / (a n : ℝ) + (n : ℝ) ^ 2 / (v n : ℝ) +
      (n : ℝ) ^ 2 / (b n : ℝ) + (n : ℝ) ^ 2 / (u n : ℝ) ≤
      16 / Real.sqrt (n : ℝ) := by
  have hs := sqrt_ge_four hn
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hroot : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hvbound : 8 / (3 * (n : ℝ)) ≤ 3 / Real.sqrt (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hspos).mpr
    linarith
  have hubound : 2 / (n : ℝ) ≤ 2 / Real.sqrt (n : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hspos hroot
  have ha := sq_div_a_le hn
  have hv := (sq_div_v_le hn).trans hvbound
  have hb := sq_div_b_le hn
  have hu := (sq_div_u_le hn).trans hubound
  have hpos : 0 < 1 / Real.sqrt (n : ℝ) := one_div_pos.mpr hspos
  simp only [div_eq_mul_inv] at ha hv hb hu hpos ⊢
  linarith

/-- Both finite occupation laws have uniformly small logarithmic comparison loss. -/
theorem occupation_order_loss_le {n : ℕ} (hn : 16 ≤ n) {H : ℝ}
    (hH : 0 ≤ H) (hHn : H ≤ 2 * (n : ℝ)) :
    H ^ 2 / (a n : ℝ) + H ^ 2 / (2 * (v n : ℝ)) +
      H ^ 2 / (b n : ℝ) + H ^ 2 / (2 * (u n : ℝ)) ≤
      64 / Real.sqrt (n : ℝ) := by
  have hsq : H ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos (by omega : 4 ≤ n)
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos (by omega : 4 ≤ n)
  have hb : (0 : ℝ) < b n := by exact_mod_cast b_pos (by omega : 4 ≤ n)
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos (by omega : 4 ≤ n)
  have h1 := div_le_div_of_nonneg_right hsq ha.le
  have h2 := div_le_div_of_nonneg_right hsq hv.le
  have h3 := div_le_div_of_nonneg_right hsq hb.le
  have h4 := div_le_div_of_nonneg_right hsq hu.le
  have h2' : H ^ 2 / (2 * (v n : ℝ)) ≤ H ^ 2 / (v n : ℝ) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hv (by linarith)
  have h4' : H ^ 2 / (2 * (u n : ℝ)) ≤ H ^ 2 / (u n : ℝ) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hu (by linarith)
  have hloss := occupation_parameter_loss_le hn
  simp only [mul_div_assoc] at h1 h2 h3 h4
  simp only [div_eq_mul_inv] at h1 h2 h3 h4 h2' h4' hloss ⊢
  linarith

/-- Separate derivative and multiplication expansion orders obey the same loss bound. -/
theorem occupation_two_orders_loss_le {n : ℕ} (hn : 16 ≤ n) {H₁ H₂ : ℝ}
    (hH₁ : 0 ≤ H₁) (hH₁n : H₁ ≤ 2 * (n : ℝ))
    (hH₂ : 0 ≤ H₂) (hH₂n : H₂ ≤ 2 * (n : ℝ)) :
    H₁ ^ 2 / (a n : ℝ) + H₁ ^ 2 / (2 * (v n : ℝ)) +
      H₂ ^ 2 / (b n : ℝ) + H₂ ^ 2 / (2 * (u n : ℝ)) ≤
      64 / Real.sqrt (n : ℝ) := by
  calc
    _ ≤ (2 * (n : ℝ)) ^ 2 / (a n : ℝ) +
        (2 * (n : ℝ)) ^ 2 / (2 * (v n : ℝ)) +
        (2 * (n : ℝ)) ^ 2 / (b n : ℝ) +
        (2 * (n : ℝ)) ^ 2 / (2 * (u n : ℝ)) := by
      gcongr
    _ ≤ _ := occupation_order_loss_le hn (by positivity) le_rfl

/-- The multiplication order has matching growth once the eventual beta estimate is known. -/
theorem b_isTheta_of_eventually_beta_bound
    (hbeta : ∀ᶠ n : ℕ in Filter.atTop, beta n ≤ 2 / Real.sqrt (n : ℝ)) :
    Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (b n : ℝ))
      (fun n : ℕ => (n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) := by
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨4, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 16, hbeta] with n hn hbeta_n
    have hnonneg : 0 ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by positivity
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (b n : ℝ) by positivity),
      abs_of_nonneg hnonneg, mul_assoc] using b_scale_upper_of_beta_bound hn hbeta_n
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨4, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 16] with n hn
    have hnonneg : 0 ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by positivity
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (b n : ℝ) by positivity), abs_of_nonneg hnonneg]
    have h := b_scale_lower hn
    linarith

end Problem335.LowerParameters

end

end OAI
