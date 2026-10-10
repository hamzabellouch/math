import OAI.Probability.FreeIsing.Energy.MomentCombinatorics

namespace OAI

namespace Problem367

theorem pow_mul_exp_le_of_log_le
    {m a c : ℝ} (hm : 0 < m) (hlog : Real.log m ≤ a)
    {q p : ℕ} (hqp : q ≤ p) :
    m ^ p * Real.exp (-a * ((p : ℝ) - c)) ≤
      m ^ q * Real.exp (-a * ((q : ℝ) - c)) := by
  have hp : m ^ p = Real.exp ((p : ℝ) * Real.log m) := by
    rw [Real.exp_nat_mul, Real.exp_log hm]
  have hq : m ^ q = Real.exp ((q : ℝ) * Real.log m) := by
    rw [Real.exp_nat_mul, Real.exp_log hm]
  rw [hp, hq, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hqp' : (q : ℝ) ≤ p := by exact_mod_cast hqp
  nlinarith [mul_nonneg (sub_nonneg.mpr hqp') (sub_nonneg.mpr hlog)]

theorem critical_moment_error_le_order_three
    {m K : ℝ} (hm : 0 < m) (hK : 0 ≤ K) (hlog : Real.log m ≤ 2 * K)
    {p : ℕ} (hp : 3 ≤ p) :
    Real.exp (-K * (p : ℝ) ^ 2 / 2) +
        m ^ p * Real.exp (-2 * K * ((p : ℝ) - 1)) ≤
      Real.exp (-9 * K / 2) + m ^ 3 * Real.exp (-4 * K) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hfirst : Real.exp (-K * (p : ℝ) ^ 2 / 2) ≤ Real.exp (-9 * K / 2) := by
    apply Real.exp_le_exp.mpr
    have hsquare : (9 : ℝ) ≤ (p : ℝ)^2 := by nlinarith
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hsquare)]
  have hsecond := pow_mul_exp_le_of_log_le (c := (1 : ℝ)) hm hlog hp
  norm_num at hsecond
  have he1 : -2 * K * ((p : ℝ) - 1) = -(2 * K * ((p : ℝ) - 1)) := by ring
  have he2 : -4 * K = -(2 * K * 2) := by ring
  rw [he1, he2]
  exact add_le_add hfirst hsecond

theorem exists_critical_moment_constant
    {m kappa : ℝ} (hm : 0 < m) (hkappa : 0 < kappa) (K0 : ℝ) :
    ∃ K : ℝ, K0 ≤ K ∧ 0 ≤ K ∧ Real.log m ≤ 2 * K ∧
      Real.exp (-9 * K / 2) + m ^ 3 * Real.exp (-4 * K) ≤ kappa := by
  let K := |K0| + |Real.log m| + |Real.log (kappa / 2)| +
    |Real.log (kappa / (2 * m ^ 3))| + 1
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hK0 : K0 ≤ K := by
    dsimp [K]
    linarith [le_abs_self K0, abs_nonneg (Real.log m),
      abs_nonneg (Real.log (kappa / 2)), abs_nonneg (Real.log (kappa / (2 * m ^ 3)))]
  have hlog : Real.log m ≤ 2 * K := by
    dsimp [K]
    linarith [le_abs_self (Real.log m), abs_nonneg K0,
      abs_nonneg (Real.log m), abs_nonneg (Real.log (kappa / 2)),
      abs_nonneg (Real.log (kappa / (2 * m ^ 3)))]
  have hfirst_exp : -9 * K / 2 ≤ Real.log (kappa / 2) := by
    have hh : -Real.log (kappa / 2) ≤ K := by
      dsimp [K]
      linarith [neg_le_abs (Real.log (kappa / 2)), abs_nonneg K0,
        abs_nonneg (Real.log m), abs_nonneg (Real.log (kappa / (2 * m ^ 3)))]
    linarith
  have hsecond_exp : -4 * K ≤ Real.log (kappa / (2 * m ^ 3)) := by
    have hh : -Real.log (kappa / (2 * m ^ 3)) ≤ K := by
      dsimp [K]
      linarith [neg_le_abs (Real.log (kappa / (2 * m ^ 3))), abs_nonneg K0,
        abs_nonneg (Real.log m), abs_nonneg (Real.log (kappa / 2))]
    linarith
  have hfirst : Real.exp (-9 * K / 2) ≤ kappa / 2 := by
    calc
      Real.exp (-9 * K / 2) ≤ Real.exp (Real.log (kappa / 2)) :=
        Real.exp_le_exp.mpr hfirst_exp
      _ = kappa / 2 := Real.exp_log (by positivity)
  have hsecond : m ^ 3 * Real.exp (-4 * K) ≤ kappa / 2 := by
    calc
      m ^ 3 * Real.exp (-4 * K) ≤
          m ^ 3 * Real.exp (Real.log (kappa / (2 * m ^ 3))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsecond_exp) (by positivity)
      _ = kappa / 2 := by rw [Real.exp_log (by positivity)]; field_simp
  exact ⟨K, hK0, hK, hlog, by linarith⟩

theorem critical_moment_absorb
    {b theta A B e : ℝ} (hb : 0 ≤ b) (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : b * theta ^ 2 = 1) {p : ℕ} (hp : 3 ≤ p)
    (hB : 0 ≤ B) (he : e ≤ 1 - theta)
    (hrec : (1 - b * theta ^ p) * A ≤ B * e) : A ≤ B := by
  have hgap := (critical_moment_absorption hb htheta htheta1 hcritical hp).2
  have hpos : 0 < 1 - b * theta ^ p := by linarith
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    (1 - b * theta ^ p) * A ≤ B * e := hrec
    _ ≤ B * (1 - theta) := mul_le_mul_of_nonneg_left he hB
    _ ≤ (1 - b * theta ^ p) * B := by
      simpa only [mul_comm B] using mul_le_mul_of_nonneg_left hgap hB

end Problem367

end OAI
