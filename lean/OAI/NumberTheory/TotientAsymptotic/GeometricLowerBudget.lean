import OAI.NumberTheory.TotientAsymptotic.FordDimensionScale

namespace OAI

/-! The two numerical margins needed for the inner prime grid. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma geometric_dominates_polynomial {c : ℝ} (hc : 0 < c) (A : ℝ) (k : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ h : ℕ,H ≤ h → A*(h:ℝ)^k ≤ c*(rho^h)⁻¹ := by
  have hlim : Tendsto (fun h : ℕ => A*((h:ℝ)^k*rho^h)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one k rho_pos.le rho_lt_one).const_mul A
  have ht := hlim.eventually (eventually_lt_nhds hc)
  obtain ⟨H,hH⟩ := eventually_atTop.mp ht
  filter_upwards [eventually_ge_atTop H] with J hJ
  intro h hh
  have hs := (hH h (hJ.trans hh)).le
  apply (le_div_iff₀ (pow_pos rho_pos h)).mpr
  simpa only [div_eq_mul_inv,mul_assoc] using hs

lemma ambient_polynomial_budget (A : ℝ) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop,A*(m x:ℝ)^k ≤ B x := by
  have ht : Tendsto (fun x : ℝ => A*(m x:ℝ)^k*
      Real.exp (-((3/5:ℝ)*(m x:ℝ)))) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (k:ℝ) (3/5) (by norm_num : (0:ℝ) < 3/5)).comp
        (tendsto_natCast_atTop_atTop.comp m_tendsto)
    simpa only [Real.rpow_natCast,mul_zero,Function.comp_apply,neg_mul,mul_assoc] using h.const_mul A
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    dimension_exponential_lower] with x hx hB
  have hs : A*(m x:ℝ)^k ≤ Real.exp ((3/5:ℝ)*(m x:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hx.le (Real.exp_pos ((3/5:ℝ)*(m x:ℝ))).le
    rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] at hh
    exact hh
  exact hs.trans hB

end TotientAsymptotic

end

end OAI
