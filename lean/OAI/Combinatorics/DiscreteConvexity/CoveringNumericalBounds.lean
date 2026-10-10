import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace TalagrandDiscreteConvexity.Covering.NumericalBounds

/-- Number of distinct edges in a residual tuple. -/
def m (h : ℕ) : ℕ := 2 ^ (12 * h)

/-- Threshold for a large weighted degree. -/
def T (h : ℕ) : ℝ := 2 ^ (4 * h)

/-- Independent sampling probability for each ordered pair. -/
noncomputable def p (h : ℕ) : ℝ := (2 ^ (8 * h))⁻¹

/-- Exponent bounding one regular extension factor. -/
def A (r h : ℕ) : ℕ := 4 * h + 13 * r * h

theorem m_pos (h : ℕ) : 0 < m h := by
  unfold m
  positivity

theorem T_pos (h : ℕ) : 0 < T h := by
  unfold T
  positivity

theorem T_nonneg (h : ℕ) : 0 ≤ T h := (T_pos h).le

theorem p_pos (h : ℕ) : 0 < p h := by
  unfold p
  positivity

theorem p_nonneg (h : ℕ) : 0 ≤ p h := (p_pos h).le

theorem p_le_one (h : ℕ) : p h ≤ 1 := by
  unfold p
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

/-- The count of possible padded extensions has this dyadic upper bound. -/
theorem extension_base_le_pow (r h : ℕ) (hrh : r ≤ h) :
    1 + r * m h ≤ 2 ^ (13 * h) := by
  have hm : 1 ≤ m h := m_pos h
  have hpow : h + 1 ≤ 2 ^ h := Nat.lt_two_pow_self
  calc
    1 + r * m h ≤ m h + h * m h :=
      Nat.add_le_add hm (Nat.mul_le_mul_right (m h) hrh)
    _ = (h + 1) * m h := by ring
    _ ≤ 2 ^ h * m h := Nat.mul_le_mul_right (m h) hpow
    _ = 2 ^ (13 * h) := by
      rw [m, ← pow_add]
      congr 1
      omega

/-- The extension factor from the weighted-degree estimate is at most
the stated natural power of two. -/
theorem extension_factor_le_pow (r h : ℕ) (hrh : r ≤ h) :
    T h * (1 + (r : ℝ) * (m h : ℝ)) ^ r ≤ (2 : ℝ) ^ A r h := by
  have hbase : 1 + (r : ℝ) * (m h : ℝ) ≤ (2 : ℝ) ^ (13 * h) := by
    exact_mod_cast extension_base_le_pow r h hrh
  calc
    T h * (1 + (r : ℝ) * (m h : ℝ)) ^ r ≤
        T h * ((2 : ℝ) ^ (13 * h)) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase r) (T_nonneg h)
    _ = (2 : ℝ) ^ A r h := by
      rw [T, ← pow_mul, ← pow_add]
      congr 1
      unfold A
      ring

/-- The quadratic polynomial exponent is dominated by the sampling budget. -/
theorem exponent_budget_nat (r h : ℕ) (hrh : r ≤ h) (hh : 64 ≤ h) :
    A r h + 1 ≤ 2 ^ (4 * h) := by
  have hh1 : 1 ≤ h := by omega
  have hrh' : r * h ≤ h * h := Nat.mul_le_mul_right h hrh
  have hh' : h ≤ h * h := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left h hh1
  have hquadratic : A r h + 1 ≤ 18 * h ^ 2 := by
    unfold A
    nlinarith
  have hpow : h ≤ 2 ^ h := Nat.le_of_lt Nat.lt_two_pow_self
  have hsquare : h ^ 2 ≤ 2 ^ (2 * h) := by
    calc
      h ^ 2 ≤ (2 ^ h) ^ 2 := Nat.pow_le_pow_left hpow 2
      _ = 2 ^ (2 * h) := by rw [← pow_mul, Nat.mul_comm h 2]
  have h18 : 18 ≤ 2 ^ (2 * h) := by
    calc
      18 ≤ (2 : ℕ) ^ 5 := by norm_num
      _ ≤ 2 ^ (2 * h) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
  calc
    A r h + 1 ≤ 18 * h ^ 2 := hquadratic
    _ ≤ 18 * 2 ^ (2 * h) := Nat.mul_le_mul_left 18 hsquare
    _ ≤ 2 ^ (2 * h) * 2 ^ (2 * h) := Nat.mul_le_mul_right _ h18
    _ = 2 ^ (4 * h) := by
      rw [← pow_add]
      congr 1
      omega

/-- The chosen pair probability times the tuple length is exactly the
weighted-degree threshold. -/
theorem p_mul_m (h : ℕ) : p h * (m h : ℝ) = T h := by
  simp only [p, m, T, Nat.cast_pow, Nat.cast_ofNat]
  rw [show 12 * h = 8 * h + 4 * h by omega, pow_add, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

theorem exponent_budget (r h : ℕ) (hrh : r ≤ h) (hh : 64 ≤ h) :
    (A r h : ℝ) + 1 ≤ p h * (m h : ℝ) := by
  rw [p_mul_m]
  unfold T
  exact_mod_cast exponent_budget_nat r h hrh hh

/-- A dyadic growth factor is dominated by independent avoidance when each
block has one additional unit of exponential sampling budget. -/
theorem dyadic_residual_bound (a n : ℕ) (prob : ℝ)
    (hprob : prob ≤ 1)
    (hbudget : (a : ℝ) + 1 ≤ prob * (n : ℝ)) :
    ((2 : ℝ) ^ a) ^ n * (1 - prob) ^ (n * n) ≤ ((2 : ℝ) ^ n)⁻¹ := by
  have hnonneg : 0 ≤ 1 - prob := sub_nonneg.mpr hprob
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ a ≤ Real.exp (a : ℝ) := by
    calc
      (2 : ℝ) ^ a ≤ (Real.exp 1) ^ a :=
        pow_le_pow_left₀ (by norm_num) htwo a
      _ = Real.exp (a : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
  have hexponent : (a : ℝ) + (n : ℝ) * (-prob) ≤ -1 := by
    calc
      (a : ℝ) + (n : ℝ) * (-prob) = (a : ℝ) - prob * (n : ℝ) := by ring
      _ ≤ -1 := by linarith
  have hhalf : Real.exp (-1 : ℝ) ≤ (2 : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).mpr htwo
  have hbase : (2 : ℝ) ^ a * (1 - prob) ^ n ≤ (2 : ℝ)⁻¹ := by
    calc
      (2 : ℝ) ^ a * (1 - prob) ^ n ≤
          Real.exp (a : ℝ) * (Real.exp (-prob)) ^ n :=
        mul_le_mul hpow
          (pow_le_pow_left₀ hnonneg (Real.one_sub_le_exp_neg prob) n)
          (pow_nonneg hnonneg n) (Real.exp_nonneg _)
      _ = Real.exp ((a : ℝ) + (n : ℝ) * (-prob)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr hexponent
      _ ≤ (2 : ℝ)⁻¹ := hhalf
  simpa only [mul_pow, ← pow_mul, inv_pow] using
    pow_le_pow_left₀
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) a)
        (pow_nonneg hnonneg n)) hbase n

/-- The actual residual tuple-growth factor times its exact avoidance
probability is at most the reciprocal dyadic tuple-length power. -/
theorem residual_cost_le_inv_pow (r h : ℕ) (hrh : r ≤ h) (hh : 64 ≤ h) :
    (T h * (1 + (r : ℝ) * (m h : ℝ)) ^ r) ^ m h *
        (1 - p h) ^ (m h * m h) ≤ ((2 : ℝ) ^ m h)⁻¹ := by
  have hfactor : 0 ≤ T h * (1 + (r : ℝ) * (m h : ℝ)) ^ r :=
    mul_nonneg (T_nonneg h) (pow_nonneg (by positivity) r)
  calc
    (T h * (1 + (r : ℝ) * (m h : ℝ)) ^ r) ^ m h *
        (1 - p h) ^ (m h * m h) ≤
        ((2 : ℝ) ^ A r h) ^ m h * (1 - p h) ^ (m h * m h) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hfactor (extension_factor_le_pow r h hrh) (m h))
        (pow_nonneg (sub_nonneg.mpr (p_le_one h)) _)
    _ ≤ ((2 : ℝ) ^ m h)⁻¹ :=
      dyadic_residual_bound (A r h) (m h) (p h) (p_le_one h)
        (exponent_budget r h hrh hh)

/-- The initial weighted-degree generators have the required numerical cost
after inserting the assumed upper bound on the total edge mass. -/
theorem initial_cost_le (r h : ℕ) (hrh : r ≤ h) :
    (T h)⁻¹ * (2 : ℝ) ^ r * (2 : ℝ) ^ (h + 1) ≤
      2 * ((2 : ℝ) ^ (2 * h))⁻¹ := by
  change ((2 : ℝ) ^ (4 * h))⁻¹ * (2 : ℝ) ^ r * (2 : ℝ) ^ (h + 1) ≤ _
  have hpos : 0 < (2 : ℝ) ^ (4 * h) := pow_pos (by norm_num) _
  have hcancel :
      (2 : ℝ) ^ (4 * h) * (2 * ((2 : ℝ) ^ (2 * h))⁻¹) =
        2 * (2 : ℝ) ^ (2 * h) := by
    rw [show 4 * h = 2 * h + 2 * h by omega, pow_add]
    calc
      _ = 2 * ((2 : ℝ) ^ (2 * h) * (2 : ℝ) ^ (2 * h) *
          ((2 : ℝ) ^ (2 * h))⁻¹) := by ring
      _ = 2 * (2 : ℝ) ^ (2 * h) := by rw [mul_self_mul_inv]
  rw [mul_assoc, inv_mul_le_iff₀ hpos, hcancel]
  calc
    (2 : ℝ) ^ r * (2 : ℝ) ^ (h + 1) = (2 : ℝ) ^ (r + (h + 1)) :=
      (pow_add _ _ _).symm
    _ ≤ (2 : ℝ) ^ (2 * h + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    _ = 2 * (2 : ℝ) ^ (2 * h) := by rw [pow_succ, mul_comm]

/-- The sampled-pair numerical cost has the same bound as the initial cost. -/
theorem pair_cost_le (r h : ℕ) (hrh : r ≤ h) :
    p h * (2 : ℝ) ^ (h + 1) * (2 : ℝ) ^ r * T h ≤
      2 * ((2 : ℝ) ^ (2 * h))⁻¹ := by
  have hcancel : p h * T h = (T h)⁻¹ := by
    change ((2 : ℝ) ^ (8 * h))⁻¹ * (2 : ℝ) ^ (4 * h) =
      ((2 : ℝ) ^ (4 * h))⁻¹
    rw [show 8 * h = 4 * h + 4 * h by omega, pow_add, mul_inv_rev,
      mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
      mul_one]
  calc
    p h * (2 : ℝ) ^ (h + 1) * (2 : ℝ) ^ r * T h =
        (p h * T h) * (2 : ℝ) ^ r * (2 : ℝ) ^ (h + 1) := by ring
    _ = (T h)⁻¹ * (2 : ℝ) ^ r * (2 : ℝ) ^ (h + 1) := by rw [hcancel]
    _ ≤ 2 * ((2 : ℝ) ^ (2 * h))⁻¹ := initial_cost_le r h hrh

theorem h_le_m (h : ℕ) : h ≤ m h := by
  calc
    h ≤ 2 ^ h := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ 2 ^ (12 * h) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)

/-- The sum of the two initial-scale costs and the residual dyadic cost
is at most the final covering budget. -/
theorem final_cost_le (h : ℕ) (hh : 64 ≤ h) :
    4 * ((2 : ℝ) ^ (2 * h))⁻¹ + ((2 : ℝ) ^ m h)⁻¹ ≤
      3 * ((2 : ℝ) ^ h)⁻¹ := by
  have hpos : 0 < (2 : ℝ) ^ h := pow_pos (by norm_num) _
  have hfour : (4 : ℝ) ≤ (2 : ℝ) ^ h := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ h := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfirst : 4 * ((2 : ℝ) ^ (2 * h))⁻¹ ≤ ((2 : ℝ) ^ h)⁻¹ := by
    apply (mul_inv_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) (2 * h))).2
    rw [show 2 * h = h + h by omega, pow_add, inv_mul_cancel_left₀ hpos.ne']
    exact hfour
  have hlast : ((2 : ℝ) ^ m h)⁻¹ ≤ ((2 : ℝ) ^ h)⁻¹ :=
    inv_anti₀ hpos (pow_le_pow_right₀ (by norm_num) (h_le_m h))
  calc
    4 * ((2 : ℝ) ^ (2 * h))⁻¹ + ((2 : ℝ) ^ m h)⁻¹ ≤
        ((2 : ℝ) ^ h)⁻¹ + ((2 : ℝ) ^ h)⁻¹ := add_le_add hfirst hlast
    _ = 2 * ((2 : ℝ) ^ h)⁻¹ := by ring
    _ ≤ 3 * ((2 : ℝ) ^ h)⁻¹ :=
      mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hpos.le)

end TalagrandDiscreteConvexity.Covering.NumericalBounds

end OAI
