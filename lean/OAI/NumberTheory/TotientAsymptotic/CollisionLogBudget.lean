import OAI.NumberTheory.TotientAsymptotic.FordCollisionCutoffs

namespace OAI

/-! Logarithmic normality losses are smaller than the final collision band. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma ford_band_log_upper : ∀ᶠ x : ℝ in atTop, ∀ i < m x,
    Real.log (6*fordBandScale x i) ≤ 26*(m x-i : ℕ) := by
  filter_upwards [fordBandScale_uniform_comparison (ε := 1) (by norm_num),theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hx htheta hB
  intro i hi
  have hh : (1 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hi)
  have hh0 : (0 : ℝ) < (m x-i : ℕ) := zero_lt_one.trans_le hh
  have hp := pow_pos rho_pos (m x-i)
  have hb := bandScale_pos hi
  have hf : fordBandScale x i ≤ 2*bandScale x i := by
    have hu := (div_lt_iff₀ hb).mp (show fordBandScale x i/bandScale x i < 2 by
      linarith [(abs_lt.mp (hx i hi)).2])
    exact hu.le
  have ha : alpha (theta x) ≤ 2 := by
    have hl := alpha_le (theta x) htheta
    have hq : lam/rho < 2 := (div_lt_iff₀ rho_pos).mpr (by linarith [lam_lt_one,collision_rho_bounds.1])
    exact hl.trans hq.le
  have hmodel : bandScale x i ≤ 2*(m x-i : ℕ)/rho^(m x-i) := by
    unfold bandScale
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha hh0.le) (inv_pos.mpr hp).le
  have hu : 6*fordBandScale x i ≤ 24*(m x-i : ℕ)/rho^(m x-i) := by
    calc
      _ ≤ 12*bandScale x i := by linarith
      _ ≤ 12*(2*(m x-i : ℕ)/rho^(m x-i)) := mul_le_mul_of_nonneg_left hmodel (by norm_num)
      _ = _ := by ring
  have hf0 := fordBandScale_pos (zero_lt_one.trans hB) hi
  have hl := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 6) hf0) hu
  rw [Real.log_div (mul_pos (by norm_num : (0 : ℝ) < 24) hh0).ne' hp.ne',
    Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) hh0.ne',Real.log_pow] at hl
  have hrho : Real.log rho = -lam := by simp only [lam,one_div,Real.log_inv,neg_neg]
  rw [hrho] at hl
  have hl24 : Real.log (24 : ℝ) ≤ 24 := Real.log_le_self (by norm_num)
  have hlh := Real.log_le_self hh0.le
  have hlam := mul_le_mul_of_nonneg_right lam_lt_one.le hh0.le
  nlinarith

/-- The loss of one plus the logarithm of the normality factor is uniformly
absorbed by one percent of the smallest retained collision band. -/
theorem collision_log_loss_small : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ y : ℝ, 0 < B y → B y ≤ 2*fordBandScale x i →
    1+Real.log (3*B y) ≤ (1/100 : ℝ)*bandScale x (collisionLastIndex x i) := by
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (ford_band_polynomial_lower 2)
  filter_upwards [eventually_collision_indices,eventually_ge_atTop (2*H₀),
    eventually_ge_atTop 100000] with H hind hthreshold hH
  filter_upwards [ford_band_log_upper,hH₀ H₀ le_rfl,
    fordBandScale_uniform_comparison (ε := 1) (by norm_num),
    m_tendsto.eventually (eventually_ge_atTop H)] with x hlog hp hcompare hm
  intro i hi y hBy hByu
  obtain ⟨hHi,hcut,hk⟩ := hind x hm i hi
  have him : i < m x := by unfold R at hi; omega
  have hkm : collisionLastIndex x i < m x := by
    unfold collisionLastIndex
    omega
  have hh : (100000 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH.trans hHi
  have hhalf : (m x-i : ℕ) ≤ 2*(m x-collisionLastIndex x i) := by
    unfold collisionLastIndex
    omega
  have hp' : ((m x-collisionLastIndex x i : ℕ) : ℝ)^2 ≤ fordBandScale x (collisionLastIndex x i) := by
    apply hp (collisionLastIndex x i) hkm
    have hcutH : H₀ ≤ m x-collisionLastIndex x i := by omega
    exact hcutH
  have hb := bandScale_pos hkm
  have hfu : fordBandScale x (collisionLastIndex x i) ≤ 2*bandScale x (collisionLastIndex x i) := by
    apply le_of_lt
    apply (div_lt_iff₀ hb).mp
    linarith [(abs_lt.mp (hcompare _ hkm)).2]
  have hlogy : Real.log (3*B y) ≤ 26*(m x-i : ℕ) :=
    (Real.log_le_log (by positivity) (by linarith)).trans (hlog i him)
  have hhalfR : ((m x-i : ℕ) : ℝ) ≤ 2*(m x-collisionLastIndex x i : ℕ) := by exact_mod_cast hhalf
  have hh0 : (0 : ℝ) ≤ (m x-i : ℕ) := Nat.cast_nonneg _
  have hsq := pow_le_pow_left₀ hh0 hhalfR 2
  have hgrowth := mul_le_mul_of_nonneg_left hh hh0
  nlinarith

end TotientAsymptotic

end

end OAI
