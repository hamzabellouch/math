import OAI.NumberTheory.TotientAsymptotic.CollisionChoiceCost
import OAI.NumberTheory.TotientAsymptotic.FordCollisionCutoffs

namespace OAI

/-! Absorbing the complete class-choice costs in the strict exponent saving. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma smooth_choice_cost_scaled {M z Y h : ℝ} (hM : 0 < M) (hz : 1 < z)
    (hlz : 1 ≤ Real.log z) (hh : 2 ≤ h) (hY : 0 ≤ Y) (hZ : B z ≤ 2*Y/h^18) :
    M*Real.log (⌈z⌉₊ : ℝ) ≤
      Real.exp ((|Real.log M|+1)*h^2+Y/(16*h^4)) := by
  apply (smooth_choice_cost hM hz hlz).trans
  apply Real.exp_le_exp.mpr
  have hh1 : 1 ≤ h^2 := by nlinarith
  have ha := mul_le_mul_of_nonneg_left hh1 (show 0 ≤ |Real.log M|+1 by positivity)
  have hb := residual_choice_exponent hY hh hZ
  nlinarith

lemma collision_all_choice_cost {A M y Y z h G : ℝ} {c J : ℕ}
    (hy : 0 ≤ y/Real.log y) (hM : 0 < M) (hY : 1 ≤ Y) (hh : 2 ≤ h)
    (hlogY : Real.log Y ≤ 26*h) (hz : 1 < z) (hlz : 1 ≤ Real.log z)
    (hZ : B z ≤ 2*Y/h^18) (hG : 0 ≤ G) (hGu : G ≤ Real.exp (26*h^2))
    (hc : (c : ℝ) ≤ h) (hJ : (J : ℝ) ≤ h) :
    (2 : ℝ)^J*(y/Real.log y*Real.exp (A*h^2-Y/(4*h^4))*G*
      (M*Real.log (⌈z⌉₊ : ℝ))*(2*(|Real.log M|+3*Y))^c) ≤
      y/Real.log y*Real.exp ((A+3*|Real.log M|+60)*h^2-3*Y/(16*h^4)) := by
  have hs := smooth_choice_cost_scaled hM hz hlz hh (zero_le_one.trans hY) hZ
  have hp := canceled_mass_power_bound (M := M) hY (by linarith) hc hlogY
  have hj := subset_choice_cost (by linarith) hJ
  have hzs : 0 ≤ M*Real.log (⌈z⌉₊ : ℝ) := by
    apply mul_nonneg hM.le
    apply Real.log_nonneg
    exact hz.le.trans (Nat.le_ceil z)
  have hprod := mul_le_mul hj
    (mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_left hGu (mul_nonneg hy (Real.exp_pos (A*h^2-Y/(4*h^4))).le))
        hs hzs (by positivity))
      hp (by positivity) (by positivity))
    (by positivity) (Real.exp_pos _).le
  apply hprod.trans_eq
  rw [show (A+3*|Real.log M|+60)*h^2-3*Y/(16*h^4) =
    h^2+(((A*h^2-Y/(4*h^4))+26*h^2)+
      ((|Real.log M|+1)*h^2+Y/(16*h^4)))+(2*|Real.log M|+32)*h^2 by ring]
  simp only [Real.exp_add]
  ring

/-- Any fixed quadratic logarithmic cost is eventually smaller than the
remaining fraction of the strict slack, uniformly for all retained bands. -/
theorem ford_band_absorbs_square (K : ℝ) : ∀ᶠ H : ℕ in atTop,
    ∀ᶠ x : ℝ in atTop, ∀ i : ℕ, i ≤ R x H → ∀ Y : ℝ,
    (87/100 : ℝ)*fordBandScale x i ≤ Y →
    K*((m x-i : ℕ) : ℝ)^2 ≤ Y/(16*((m x-i : ℕ) : ℝ)^4) := by
  filter_upwards [ford_band_polynomial_lower 8,
    eventually_ge_atTop (⌈max 1 (32*|K|)⌉₊)] with H hpoly hH
  filter_upwards [hpoly,m_tendsto.eventually (eventually_ge_atTop H)] with x hp hm
  intro i hi Y hY
  have him : i < m x := by
    have hh : 1 ≤ H := by
      have ht := (le_max_left 1 (32*|K|)).trans (Nat.le_ceil _)
      have hH' : (⌈max 1 (32*|K|)⌉₊ : ℝ) ≤ H := by exact_mod_cast hH
      exact_mod_cast ht.trans hH'
    unfold R at hi
    omega
  have hHi : H ≤ m x-i := by unfold R at hi; omega
  have hthreshold : max 1 (32*|K|) ≤ ((m x-i : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hH.trans hHi)
  have hh1 := (le_max_left 1 (32*|K|)).trans hthreshold
  have hhK := (le_max_right 1 (32*|K|)).trans hthreshold
  have hh0 : (0 : ℝ) < (m x-i : ℕ) := zero_lt_one.trans_le hh1
  have hs : 32*K ≤ ((m x-i : ℕ) : ℝ)^2 := by
    have hab := le_abs_self K
    nlinarith
  have hb := hp i him hHi
  have hhalf : ((m x-i : ℕ) : ℝ)^8/2 ≤ Y := by nlinarith [pow_nonneg hh0.le 8]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16*((m x-i : ℕ) : ℝ)^4)).mpr
  have hm := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ ((m x-i : ℕ) : ℝ)^2*(16*((m x-i : ℕ) : ℝ)^4)/32 by positivity)
  have he : K*((m x-i : ℕ) : ℝ)^2*(16*((m x-i : ℕ) : ℝ)^4) ≤
      ((m x-i : ℕ) : ℝ)^8/2 := by nlinarith only [hm]
  exact he.trans hhalf

end TotientAsymptotic

end

end OAI
