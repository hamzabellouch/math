import OAI.Combinatorics.EditApproximation.Geometry.TreeAccounting

namespace OAI

/-!
# Explicit slack at the large-input cutoff

The cutoff is handled symbolically: no expression with an astronomically
large exponent is expanded. The small-growth estimate supplies the
induction step. This proves the generous polynomial-versus-binary bound
used throughout the manuscript's numerical estimates.
-/

namespace EditApproximation

theorem polynomial_binary_growth_step (degree m : ℕ)
    (hsize : 4 * degree ≤ 2 * m + 1) :
    (2 * (m : ℝ) + 3) ^ degree ≤ 2 * (2 * (m : ℝ) + 1) ^ degree := by
  let d : ℝ := 2 * m + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hsizeR : 4 * (degree : ℝ) ≤ d := by
    dsimp only [d]
    exact_mod_cast hsize
  have hsmall : (degree : ℝ) * (2 / d) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hbound : (1 + 2 / d) ^ degree ≤ 2 :=
    (small_growth_pow degree (by positivity) hsmall).trans (by nlinarith)
  have hrew : 2 * (m : ℝ) + 3 = d * (1 + 2 / d) := by
    dsimp [d]
    field_simp
    ring
  rw [hrew, mul_pow]
  have hmul := mul_le_mul_of_nonneg_left hbound (pow_nonneg hd.le degree)
  simpa only [d, mul_comm] using hmul

theorem astronomical_polynomial_bound (ell : ℕ) (hell : 2 ^ 1000 ≤ ell) :
    (ell : ℝ) ^ 20000 ≤ (2 : ℝ) ^ (ell / 2) := by
  let m0 : ℕ := 2 ^ 999
  have hbaseSize : (2 * (m0 : ℝ) + 1) ≤ (2 : ℝ) ^ 1001 := by
    have hm0 : (m0 : ℝ) = (2 : ℝ) ^ 999 := by
      simp only [m0, Nat.cast_pow, Nat.cast_ofNat]
    have hone : (1 : ℝ) ≤ m0 := by rw [hm0]; exact one_le_pow₀ (by norm_num)
    have hbig : (2 : ℝ) ^ 1001 = 4 * (m0 : ℝ) := by
      rw [show 1001 = 999 + 2 by decide, pow_add, ← hm0]
      norm_num only [pow_two]
      ring
    rw [hbig]
    calc
      2 * (m0 : ℝ) + 1 ≤ 2 * (m0 : ℝ) + m0 := add_le_add le_rfl hone
      _ = 3 * (m0 : ℝ) := by ring
      _ ≤ 4 * (m0 : ℝ) := mul_le_mul_of_nonneg_right (by norm_num)
        ((by norm_num : (0 : ℝ) ≤ 1).trans hone)
  have hbasePower := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (m0 : ℝ) + 1)
    hbaseSize 20000
  rw [← pow_mul] at hbasePower
  have hexponent : 1001 * 20000 ≤ m0 := by
    have hsmall : 1001 * 20000 ≤ (2 : ℕ) ^ 25 := by norm_num
    exact hsmall.trans (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by decide : 25 ≤ 999))
  have hbase : (2 * (m0 : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m0 :=
    hbasePower.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)
  have hgrowth : ∀ m : ℕ, m0 ≤ m → (2 * (m : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hbase
    | succ m hm ih =>
      have hsize0 : 4 * 20000 ≤ 2 * m0 + 1 := by omega
      have hstep := polynomial_binary_growth_step 20000 m (by omega)
      calc
        (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 20000 = (2 * (m : ℝ) + 3) ^ 20000 := by
          congr 1
          push_cast
          ring
        _ ≤ 2 * (2 * (m : ℝ) + 1) ^ 20000 := hstep
        _ ≤ 2 * (2 : ℝ) ^ m := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
  have hcutoff : 2 ^ 1000 = 2 * m0 := by
    dsimp only [m0]
    rw [show 1000 = 999 + 1 by decide, pow_succ]
    exact Nat.mul_comm _ _
  have hm : m0 ≤ ell / 2 := by omega
  have hellR : (ell : ℝ) ≤ 2 * ((ell / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show ell ≤ 2 * (ell / 2) + 1 by omega)
  exact (pow_le_pow_left₀ (Nat.cast_nonneg ell) hellR 20000).trans (hgrowth _ hm)

theorem astronomical_parameter_slack (ell : ℕ) (H : ℝ)
    (hell : 2 ^ 1000 ≤ ell) (hH : (2 : ℝ) ^ (ell / 2) ≤ H) :
    (ell : ℝ) ^ 20000 ≤ H :=
  (astronomical_polynomial_bound ell hell).trans hH

/-- The fourth-root scale has ample polynomial slack. -/
theorem fourth_root_polynomial_slack {ell H quarterRoot : ℝ}
    (hell : 1 ≤ ell) (hH : ell ^ 20000 ≤ H)
    (hroot : 0 ≤ quarterRoot) (hrootPower : quarterRoot ^ 4 = H) :
    ell ^ 5000 ≤ quarterRoot := by
  apply (pow_le_pow_iff_left₀ (pow_nonneg (zero_le_one.trans hell) 5000)
    hroot (by decide : 4 ≠ 0)).mp
  rw [← pow_mul, hrootPower]
  exact hH

/-- The five explicit terms in Section 8 are collectively below `1/ell`.
Here `quarterRoot = H^(1/4)` and `q = p_*+21`. The hypotheses are small
consequences of the manuscript's large-input cutoff, not asymptotic
notation or a presumed error bound. -/
theorem refinement_error_envelope {ell H quarterRoot q : ℝ}
    (hell : 64000000000000 ≤ ell) (hH : ell ^ 2 ≤ H)
    (hroot : ell ^ 4 ≤ quarterRoot) (hq : 0 ≤ q) (hqSquare : q ^ 2 ≤ ell) :
    52000 / H ^ 18 + 8040000 * ell ^ 4 / quarterRoot ^ 2 +
        200 * ell / quarterRoot + 1000000 * q / ell ^ 2 + 13200 / H ^ 2 < 1 / ell := by
  have hellpos : 0 < ell := by linarith
  have hellone : 1 ≤ ell := by linarith
  have hHone : 1 ≤ H := (one_le_pow₀ hellone).trans hH
  have hHpos : 0 < H := by linarith
  have hrootpos : 0 < quarterRoot := (pow_pos hellpos 4).trans_le hroot
  have hell2 : ell ≤ ell ^ 2 := by nlinarith
  have hHell : ell ≤ H := hell2.trans hH
  have hH18 : H ≤ H ^ 18 := by
    simpa only [pow_one] using pow_le_pow_right₀ hHone (by decide : 1 ≤ 18)
  have ht1 : 52000 / H ^ 18 ≤ 1 / (8 * ell) := by
    apply (div_le_div_iff₀ (pow_pos hHpos 18) (by positivity : 0 < 8 * ell)).2
    have hsize : 416000 * ell ≤ ell ^ 2 := by nlinarith
    nlinarith
  have hrootSquare : ell ^ 8 ≤ quarterRoot ^ 2 := by
    have hsq := pow_le_pow_left₀ (pow_nonneg hellpos.le 4) hroot 2
    simpa only [← pow_mul] using hsq
  have hell5 : ell ^ 5 ≤ ell ^ 7 := pow_le_pow_right₀ hellone (by decide : 5 ≤ 7)
  have hsecondPower : 64320000 * ell ^ 5 ≤ ell ^ 8 := by
    have hcoef : 64320000 ≤ ell := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hellpos.le 7)
    have hfirst := mul_le_mul_of_nonneg_left hell5 (by norm_num : (0 : ℝ) ≤ 64320000)
    nlinarith [show ell * ell ^ 7 = ell ^ 8 by ring]
  have ht2 : 8040000 * ell ^ 4 / quarterRoot ^ 2 ≤ 1 / (8 * ell) := by
    apply (div_le_div_iff₀ (pow_pos hrootpos 2) (by positivity : 0 < 8 * ell)).2
    have hid : (8040000 * ell ^ 4) * (8 * ell) = 64320000 * ell ^ 5 := by ring
    rw [hid, one_mul]
    exact hsecondPower.trans hrootSquare
  have hsmallPower : 1600 * ell ^ 2 ≤ ell ^ 4 := by
    have hcoef : (1600 : ℝ) ≤ ell ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ell)
    nlinarith [show ell ^ 2 * ell ^ 2 = ell ^ 4 by ring]
  have ht3 : 200 * ell / quarterRoot ≤ 1 / (8 * ell) := by
    apply (div_le_div_iff₀ hrootpos (by positivity : 0 < 8 * ell)).2
    nlinarith [hsmallPower.trans hroot]
  have hqScale : 8000000 * q ≤ ell := by
    have hsq : (8000000 * q) ^ 2 ≤ ell ^ 2 := by
      have ha := mul_le_mul_of_nonneg_left hqSquare (by norm_num : (0 : ℝ) ≤ 8000000 ^ 2)
      have hb := mul_le_mul_of_nonneg_right hell hellpos.le
      nlinarith
    exact (sq_le_sq₀ (by positivity : 0 ≤ 8000000 * q) hellpos.le).mp hsq
  have ht4 : 1000000 * q / ell ^ 2 ≤ 1 / (8 * ell) := by
    apply (div_le_div_iff₀ (pow_pos hellpos 2) (by positivity : 0 < 8 * ell)).2
    have hmul := mul_le_mul_of_nonneg_right hqScale hellpos.le
    nlinarith
  have ht5 : 13200 / H ^ 2 ≤ 1 / (8 * ell) := by
    apply (div_le_div_iff₀ (pow_pos hHpos 2) (by positivity : 0 < 8 * ell)).2
    have hsq := pow_le_pow_left₀ hellpos.le hHell 2
    have hsize : 105600 * ell ≤ ell ^ 2 := by nlinarith
    nlinarith
  have hstrict : 5 * (1 / (8 * ell)) < 1 / ell := by
    rw [mul_one_div]
    apply (div_lt_div_iff₀ (by positivity : 0 < 8 * ell) hellpos).2
    nlinarith
  linarith

end EditApproximation

end OAI
