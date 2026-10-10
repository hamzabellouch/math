import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionDecay

namespace OAI

/-! At the source parameters, the exact mass-rescaling errors are
bounded by a fixed polynomial times the inverse square root of the step. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem source_scale_exponent_bound {p μ : ℝ} (hp : 1 ≤ p)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) : |-(1/p)|+|μ-1+1/p| ≤ 2 := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hi0 : 0 ≤ 1/p := by positivity
  have hi1 : 1/p ≤ 1 := (div_le_one hp0).mpr hp
  have ha : |μ-1+1/p| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  rw [abs_neg,abs_of_nonneg hi0]
  linarith

theorem eventually_source_mass_rescaling_error (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ p μ Kw : ℝ, 1 ≤ p → 0 ≤ μ → μ ≤ 1 → 1 ≤ Kw →
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      let e := (|-(1/p)|+|μ-1+1/p|)*δ
      Real.exp e*e ≤ (10*D*Real.exp 1)/Real.sqrt (SourceParameters.step L) := by
  have hroot := (Real.tendsto_sqrt_atTop.comp source_step_tendsto_atTop).eventually_ge_atTop (10*D)
  filter_upwards [hroot] with L hroot
  change 10*D ≤ Real.sqrt (SourceParameters.step L) at hroot
  intro p μ Kw hp hμ0 hμ1 hKw
  dsimp only
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hs : 0 < Real.sqrt (SourceParameters.step L) :=
    Real.sqrt_pos.mpr (SourceParameters.step_pos L)
  have hδ0 : 0 ≤ (5*D/Kw)/Real.sqrt (SourceParameters.step L) := by positivity
  have he : (|-(1/p)|+|μ-1+1/p|)*((5*D/Kw)/Real.sqrt (SourceParameters.step L)) ≤
      (10*D)/Real.sqrt (SourceParameters.step L) := by
    calc
      _ ≤ 2*((5*D/Kw)/Real.sqrt (SourceParameters.step L)) :=
        mul_le_mul_of_nonneg_right (source_scale_exponent_bound hp hμ0 hμ1) hδ0
      _ ≤ 2*((5*D)/Real.sqrt (SourceParameters.step L)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (div_le_self (by positivity) hKw) hs.le) (by norm_num)
      _ = _ := by ring
  have he1 := he.trans ((div_le_one hs).mpr hroot)
  have hb := relative_exponential_error_le he1 he (by positivity)
  convert hb using 1
  ring

theorem eventually_source_transition_error (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ (steps : ℕ) (Z Kw : ℝ),
      (steps:ℝ) ≤ L^2 → 0 ≤ Z → Z ≤ 2*L^2 → 1 ≤ Kw →
      let e := (steps:ℝ)*Z*(2*((5*D/Kw)/Real.sqrt (SourceParameters.step L)))
      Real.exp e*e ≤ (20*D*Real.exp 1)*L^4/Real.sqrt (SourceParameters.step L) := by
  have hsmall := eventually_source_polynomial_motion (20*D) 4
  filter_upwards [hsmall] with L hsmall
  intro steps Z Kw hsteps hZ0 hZ hKw
  dsimp only
  have hs : 0 < Real.sqrt (SourceParameters.step L) :=
    Real.sqrt_pos.mpr (SourceParameters.step_pos L)
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hstepZ : (steps:ℝ)*Z ≤ 2*L^4 := by
    have hb := mul_le_mul hsteps hZ hZ0 (sq_nonneg L)
    nlinarith
  have he : (steps:ℝ)*Z*(2*((5*D/Kw)/Real.sqrt (SourceParameters.step L))) ≤
      (20*D)*L^4/Real.sqrt (SourceParameters.step L) := by
    calc
      _ ≤ (2*L^4)*(2*((5*D)/Real.sqrt (SourceParameters.step L))) :=
        mul_le_mul hstepZ
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (div_le_self (by positivity) hKw) hs.le) (by norm_num))
          (by positivity) (by positivity)
      _ = _ := by ring
  rw [Real.rpow_ofNat] at hsmall
  have he1 := he.trans (hsmall.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)))
  have hb := relative_exponential_error_le he1 he (by positivity)
  convert hb using 1
  ring

/-- Multiplying the parent-mass and transition factors preserves the
same polynomial inverse-square-root scale. -/
theorem eventually_source_relative_product (B b : ℝ) (_hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop, ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      q ≤ B*L^b/Real.sqrt (SourceParameters.step L) →
      r ≤ B*L^b/Real.sqrt (SourceParameters.step L) →
      q+r+q*r ≤ (3*B)*L^b/Real.sqrt (SourceParameters.step L) := by
  filter_upwards [eventually_source_polynomial_motion B b] with L hsmall
  intro q r hq0 hr0 hq hr
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hsmall1 : B*L^b/Real.sqrt (SourceParameters.step L) ≤ 1 := hsmall.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num))
  have hr1 : r ≤ 1 := hr.trans hsmall1
  have hqr : q*r ≤ q := by nlinarith
  calc
    _ ≤ 2*q+r := by linarith
    _ ≤ 2*(B*L^b/Real.sqrt (SourceParameters.step L))+
        B*L^b/Real.sqrt (SourceParameters.step L) := by linarith
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
