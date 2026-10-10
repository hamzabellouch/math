import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorParameters

namespace OAI

/-! Concrete weight and inverse-weight bounds for the three mediator
stages. Each bound is a fixed polynomial in entering unary parameters. -/

namespace ContinuumCoulomb.MediatorParameters

theorem spoke_lower_half (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : 1 / (W : ℝ) ≤ |(J : ℝ)|) :
    (1 / 2 : ℝ) ≤ spoke r W G J := by
  have ha := canonical_amplitude_lower r hW hG hJ
  have he := (spoke_error r W G J).2
  have hpower : (2 : ℝ) ≤ (2 : ℝ) ^ precision r G := by
    exact_mod_cast Nat.le_self_pow (by unfold precision; omega : precision r G ≠ 0) 2
  have hp : 1 / (2 : ℝ) ^ precision r G ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hpower
  linarith

theorem spoke_upper (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ W) :
    (spoke r W G J : ℝ) ≤ 2 * (scale r W G : ℝ) * W := by
  have he := (spoke_error r W G J).1
  have ha := canonical_amplitude_upper r hW hG hJ
  linarith

def secondWeight (r W G : ℕ) : ℕ :=
  2 + 3 * r * delta r W G + 2 * scale r W G * W

def thirdWeight (r W G : ℕ) : ℕ :=
  2 + 3 * r * delta r W G + delta (2 * r) (secondWeight r W G) G +
    2 * scale (2 * r) (secondWeight r W G) G * secondWeight r W G

def finalWeight (r W G : ℕ) : ℕ :=
  2 + delta r W G + delta (6 * r) (thirdWeight r W G) G +
    2 * scale (6 * r) (thirdWeight r W G) G * thirdWeight r W G

theorem secondWeight_two_le (r W G : ℕ) : 2 ≤ secondWeight r W G := by
  unfold secondWeight
  omega

theorem thirdWeight_two_le (r W G : ℕ) : 2 ≤ thirdWeight r W G := by
  unfold thirdWeight
  omega

theorem finalWeight_two_le (r W G : ℕ) : 2 ≤ finalWeight r W G := by
  unfold finalWeight
  omega

theorem second_spoke_bounds (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ W) (hJlower : 1 / (W : ℝ) ≤ |(J : ℝ)|) :
    1 / (secondWeight r W G : ℝ) ≤ |(spoke r W G J : ℝ)| ∧
      |(spoke r W G J : ℝ)| ≤ secondWeight r W G := by
  have hl := spoke_lower_half r hW hG hJlower
  have hu := spoke_upper r hW hG hJ
  have htwo : (2 : ℝ) ≤ secondWeight r W G := by exact_mod_cast secondWeight_two_le r W G
  have hmax : 2 * (scale r W G : ℝ) * W ≤ secondWeight r W G := by
    exact_mod_cast (show 2 * scale r W G * W ≤ secondWeight r W G by unfold secondWeight; omega)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ spoke r W G J)]
  exact ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans hl, hu.trans hmax⟩

theorem third_spoke_bounds (r : ℕ) {W G : ℕ} (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ secondWeight r W G)
    (hJlower : 1 / (secondWeight r W G : ℝ) ≤ |(J : ℝ)|) :
    1 / (thirdWeight r W G : ℝ) ≤
        |(spoke (2 * r) (secondWeight r W G) G J : ℝ)| ∧
      |(spoke (2 * r) (secondWeight r W G) G J : ℝ)| ≤ thirdWeight r W G := by
  have hW2 : 0 < secondWeight r W G := lt_of_lt_of_le (by norm_num) (secondWeight_two_le r W G)
  have hl := spoke_lower_half (2 * r) hW2 hG hJlower
  have hu := spoke_upper (2 * r) hW2 hG hJ
  have htwo : (2 : ℝ) ≤ thirdWeight r W G := by exact_mod_cast thirdWeight_two_le r W G
  have hmax : 2 * (scale (2 * r) (secondWeight r W G) G : ℝ) * secondWeight r W G ≤
      thirdWeight r W G := by
    exact_mod_cast (show 2 * scale (2 * r) (secondWeight r W G) G * secondWeight r W G ≤
      thirdWeight r W G by unfold thirdWeight; omega)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ spoke (2 * r) (secondWeight r W G) G J)]
  exact ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans hl, hu.trans hmax⟩

theorem third_central_bounds (r : ℕ) {W G : ℕ} (hG : 0 < G) :
    1 / (thirdWeight r W G : ℝ) ≤ delta (2 * r) (secondWeight r W G) G ∧
      (delta (2 * r) (secondWeight r W G) G : ℝ) ≤ thirdWeight r W G := by
  have hW2 : 0 < secondWeight r W G := lt_of_lt_of_le (by norm_num) (secondWeight_two_le r W G)
  have hdelta : (1 : ℝ) ≤ delta (2 * r) (secondWeight r W G) G := by
    have hp : 0 < delta (2 * r) (secondWeight r W G) G := by
      unfold delta
      exact pow_pos (scale_pos (2 * r) hW2 hG) 2
    exact_mod_cast hp
  have htwo : (2 : ℝ) ≤ thirdWeight r W G := by exact_mod_cast thirdWeight_two_le r W G
  refine ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans (by linarith), ?_⟩
  exact_mod_cast (show delta (2 * r) (secondWeight r W G) G ≤ thirdWeight r W G by
    unfold thirdWeight; omega)

end ContinuumCoulomb.MediatorParameters

end OAI
