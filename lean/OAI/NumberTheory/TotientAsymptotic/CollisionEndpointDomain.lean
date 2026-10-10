import OAI.NumberTheory.TotientAsymptotic.CollisionNormalityDomain

namespace OAI

/-! Every retained dyadic endpoint eventually lies in any fixed analytic domain. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

theorem collision_endpoints_eventually {P : ℝ → Prop} (hP : ∀ᶠ y : ℝ in atTop, P y) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ y : ℝ, 1 < y → fordBandScale x i/2 ≤ B y → P y := by
  obtain ⟨y₀,hy₀⟩ := eventually_atTop.mp hP
  let z := max 2 y₀
  have hz : 1 < z := lt_of_lt_of_le (by norm_num : (1 : ℝ)<2) (le_max_left _ _)
  obtain ⟨H₀,hH₀⟩ := exists_nat_ge (2*B z)
  filter_upwards [ford_band_polynomial_lower 1,eventually_ge_atTop H₀,eventually_ge_atTop 1]
    with H hpoly hH hH1
  filter_upwards [hpoly,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi y hy hBy
  have him : i < m x := by unfold R at hi; omega
  have hHi : H ≤ m x-i := by unfold R at hi; omega
  have hlow : (H₀ : ℝ) ≤ fordBandScale x i := by
    have hh : (H₀ : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH.trans hHi
    exact hh.trans (by simpa only [pow_one] using hx i him hHi)
  have hBz : B z ≤ B y := by linarith
  have he := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hBz)
  have heq (w : ℝ) (hw : 1<w) : Real.exp (Real.exp (B w))=w := by
    rw [B,Real.exp_log (Real.log_pos hw),Real.exp_log (zero_lt_one.trans hw)]
  rw [heq z hz,heq y hy] at he
  exact hy₀ y ((le_max_right _ _).trans he)

end TotientAsymptotic

end

end OAI
