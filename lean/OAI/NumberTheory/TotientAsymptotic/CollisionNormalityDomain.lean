import OAI.NumberTheory.TotientAsymptotic.FordCollisionCutoffs

namespace OAI

/-! The normality cutoff lies in the actual dyadic counting domain. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma cube_root_le_half {b : ℝ} (hb : 8 ≤ b) : b^(1/3 : ℝ) ≤ b/2 := by
  have hb0 : 0 < b := by linarith
  have he : (b^(1/3 : ℝ))^3=b := by
    rw [← Real.rpow_mul_natCast hb0.le]
    norm_num
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hb0.le _) (by positivity) (by norm_num : 3 ≠ 0)).mp
  rw [he]
  have hs : 8 ≤ b^2 := by nlinarith
  nlinarith

/-- In particular this discharges `S ≥ exp(exp 1)` and `S ≤ y` in the
published comparison lemma at every sufficiently late retained band. -/
theorem collision_normality_domain : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ y : ℝ, 1 < y → fordBandScale x i/2 ≤ B y →
    Real.exp (Real.exp 1) ≤ normalityScale x i ∧
    1 ≤ B (normalityScale x i) ∧ normalityScale x i ≤ y := by
  filter_upwards [ford_band_polynomial_lower 1,eventually_ge_atTop 8] with H hpoly hH
  filter_upwards [hpoly,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi y hy hBy
  have him : i < m x := by unfold R at hi; omega
  have hHi : H ≤ m x-i := by unfold R at hi; omega
  have hb : ((m x-i : ℕ) : ℝ) ≤ fordBandScale x i := by simpa only [pow_one] using hx i him hHi
  have hb8 : 8 ≤ fordBandScale x i := by
    have hh : (8 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH.trans hHi
    exact hh.trans hb
  have hroot : 1 ≤ (fordBandScale x i)^(1/3 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hBscale : B (normalityScale x i)=(fordBandScale x i)^(1/3 : ℝ) := by
    simp only [normalityScale,B,Real.log_exp]
  refine ⟨Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hroot),hBscale ▸ hroot,?_⟩
  have hrootBy := (cube_root_le_half hb8).trans hBy
  have hyexp : Real.exp (Real.exp (B y))=y := by
    rw [B,Real.exp_log (Real.log_pos hy),Real.exp_log (zero_lt_one.trans hy)]
  exact (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hrootBy)).trans_eq hyexp

end TotientAsymptotic

end

end OAI
