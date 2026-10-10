import OAI.Algebra.DepthFive.ParameterBounds

namespace OAI

/-! The real cutoff separating the two circuit-factor cases. -/
noncomputable section
namespace Problem335.LowerParameters

def cutoff (n : ℕ) : ℝ := (n : ℝ) / (4 * (s n : ℝ))

theorem cutoff_pos {n : ℕ} (hn : 4 ≤ n) : 0 < cutoff n := by
  have hs : (0 : ℝ) < s n := by exact_mod_cast s_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold cutoff
  positivity

theorem sqrt_quarter_le_cutoff {n : ℕ} (hn : 4 ≤ n) :
    Real.sqrt (n : ℝ) / 4 ≤ cutoff n := by
  have hs : (0 : ℝ) < s n := by exact_mod_cast s_pos hn
  have hsn := s_le_sqrt n
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  unfold cutoff
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsn (Real.sqrt_nonneg (n : ℝ))]

theorem cutoff_le_sqrt_half {n : ℕ} (hn : 16 ≤ n) :
    cutoff n ≤ Real.sqrt (n : ℝ) / 2 := by
  have hs : (0 : ℝ) < s n := by exact_mod_cast s_pos (show 4 ≤ n by omega)
  have hsn := sqrt_half_le_s hn
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  unfold cutoff
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsn (Real.sqrt_nonneg (n : ℝ))]

theorem cutoff_mul_four_s {n : ℕ} (hn : 4 ≤ n) :
    cutoff n * (4 * (s n : ℝ)) = (n : ℝ) := by
  have hs : (0 : ℝ) < s n := by exact_mod_cast s_pos hn
  exact div_mul_cancel₀ _ (by positivity)

theorem n_div_cutoff {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) / cutoff n = 4 * (s n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold cutoff
  field_simp

theorem two_lt_cutoff {n : ℕ} (hn : 256 ≤ n) : 2 < cutoff n := by
  have hs : 16 ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    exact_mod_cast hn
  have h := sqrt_quarter_le_cutoff (show 4 ≤ n by omega)
  linarith

theorem low_degree_scaled_lt_quarter {n : ℕ} (hn : 4 ≤ n) {e : ℝ}
    (he : e < cutoff n) : (s n : ℝ) * e / (n : ℝ) < 1 / 4 := by
  have hs : (0 : ℝ) < s n := by exact_mod_cast s_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := (lt_div_iff₀ (show 0 < 4 * (s n : ℝ) by positivity)).mp he
  apply (div_lt_iff₀ hn').mpr
  nlinarith

theorem Admissible.q_le_power {n : ℕ} (h : Admissible n) :
    q n ≤ (n : ℝ) ^ (-(2 / 5 : ℝ)) := h.q_upper.trans h.sqrt_upper_power

theorem Admissible.q_le_half {n : ℕ} (h : Admissible n) : q n ≤ 1 / 2 :=
  h.q_upper.trans h.sqrt_upper_half

theorem Admissible.beta_le_half {n : ℕ} (h : Admissible n) : beta n ≤ 1 / 2 :=
  h.beta_upper.trans h.sqrt_upper_half

theorem eventually_admissible_cutoff :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Admissible n ∧ 2 < cutoff n := by
  obtain ⟨n₀, h⟩ := eventually_admissible
  refine ⟨max n₀ 256, fun n hn => ?_⟩
  exact ⟨h n ((le_max_left _ _).trans hn), two_lt_cutoff ((le_max_right _ _).trans hn)⟩

end Problem335.LowerParameters

end

end OAI
