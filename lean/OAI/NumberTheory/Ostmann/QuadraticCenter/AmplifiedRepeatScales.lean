import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifiedRepeatScaleGrowth

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_amplifiedRepeatTau_scale (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T / 2 ≤ Real.log Z → Real.log Z ≤ 2 * T →
      1 ≤ z → T ^ auxiliaryExponent / 2 ≤ Real.log z →
      Real.log z ≤ 2 * T ^ auxiliaryExponent →
      ∀ J : ℕ, c * (Z : ℝ) / Real.log Z ≤ (J : ℝ) →
      4 * ((evenMomentParameter (parameterX T) Z : ℝ) + 1) ^ 2 ≤
        Real.sqrt J * amplifiedRepeatTau Z (auxiliaryK Z z)
          (evenMomentParameter (parameterX T) Z) := by
  filter_upwards [eventually_moment_mul_log_le (1 / 500) (by norm_num),
    eventually_evenMomentParameter_bound,
    eventually_mul_rpow_le_rpow 14 (by norm_num : (3 / 5 : ℝ) < 1),
    eventually_parameterX_log_bounds, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (256 / c)] with T hcost hkbound hpow hX hT hcT
  intro Z z hZl hZu hz hzl hzu J hJ
  have hZ : 0 < Real.log Z := by linarith
  have hXlog : 0 ≤ Real.log (parameterX T : ℝ) := by linarith [hX.2.1]
  have horder := (evenMomentParameter_bounds (parameterX T) Z (by positivity)).1
  have hkpos : 0 < evenMomentParameter (parameterX T) Z := by
    have hratio : 0 ≤ Real.log (parameterX T : ℝ) / Real.log Z := by positivity
    have : (0 : ℝ) < evenMomentParameter (parameterX T) Z := by linarith
    exact_mod_cast this
  have hpower : 14 * T ^ (3 / 5 : ℝ) ≤ T := by simpa only [Real.rpow_one] using hpow
  apply amplifiedRepeatTau_scale hT hc hZ (by nlinarith) hkpos
    ((hkbound Z hZl).trans hpower) (hcost Z z hZl hZu hz hzl hzu) _ hJ
  have hcT' : 256 ≤ c * T := by
    have hh := (div_le_iff₀ hc).mp hcT
    nlinarith
  have hTle : T ≤ T ^ 2 := by nlinarith
  exact hcT'.trans (mul_le_mul_of_nonneg_left hTle hc.le)

theorem eventually_amplifiedRepeatTau_error (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T / 2 ≤ Real.log Z → Real.log Z ≤ 2 * T →
      1 ≤ z → T ^ auxiliaryExponent / 2 ≤ Real.log z →
      Real.log z ≤ 2 * T ^ auxiliaryExponent →
      ∀ J : ℕ, c * (Z : ℝ) / Real.log Z ≤ (J : ℝ) →
      let k := evenMomentParameter (parameterX T) Z
      let τ := amplifiedRepeatTau Z (auxiliaryK Z z) k
      4 * ((((k : ℝ) + 1) * (k : ℝ) ^ 2 / J) *
        (τ + (k : ℝ) / Real.sqrt J) ^ (k - 2)) ≤ τ ^ k := by
  filter_upwards [eventually_amplifiedRepeatTau_scale c hc,
    eventually_parameterX_log_bounds] with T hscale hX
  intro Z z hZl hZu hz hzl hzu J hJ
  dsimp only
  have hZ : 0 < Real.log Z := by linarith [hX.1]
  have hZpos : 0 < (Z : ℝ) := by
    have := (Real.log_pos_iff (Nat.cast_nonneg Z)).mp hZ
    linarith
  have hJpos : 0 < (J : ℝ) := (div_pos (mul_pos hc hZpos) hZ).trans_le hJ
  have hXlog : 0 ≤ Real.log (parameterX T : ℝ) := by linarith [hX.2.1]
  have hratio : 0 ≤ Real.log (parameterX T : ℝ) / Real.log Z := by positivity
  have horder := (evenMomentParameter_bounds (parameterX T) Z (by positivity)).1
  have hk : 2 ≤ evenMomentParameter (parameterX T) Z := by
    have : (2 : ℝ) ≤ evenMomentParameter (parameterX T) Z := by linarith
    exact_mod_cast this
  exact repeat_error_le_of_scale hJpos (amplifiedRepeatTau_pos _ _ _) hk
    (hscale Z z hZl hZu hz hzl hzu J hJ)

theorem eventually_amplifiedRepeatTau_mass (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ T : ℝ in atTop, ∀ Z K : ℕ,
      T / 2 ≤ Real.log Z →
      (parameterX T : ℝ) * c₀ *
        amplifiedRepeatTau Z K (evenMomentParameter (parameterX T) Z) ^
          evenMomentParameter (parameterX T) Z ≤
        Real.sqrt (parameterX T : ℝ) * Real.exp ((2 / 125 : ℝ) * K) := by
  filter_upwards [eventually_parameterX_log_bounds,
    eventually_ge_atTop (Real.log c₀)] with T hX hcT
  intro Z K hZl
  have hZ : 0 < Real.log Z := by linarith [hX.1]
  have hXlog : 0 < Real.log (parameterX T : ℝ) := by linarith [hX.2.1]
  have hXpos : 0 < (parameterX T : ℝ) := by
    have := (Real.log_pos_iff (Nat.cast_nonneg (parameterX T))).mp hXlog
    linarith
  have hratio : 0 ≤ Real.log (parameterX T : ℝ) / Real.log Z := by positivity
  have horder := (evenMomentParameter_bounds (parameterX T) Z (by positivity)).1
  have hk : 0 < evenMomentParameter (parameterX T) Z := by
    have : (0 : ℝ) < evenMomentParameter (parameterX T) Z := by linarith
    exact_mod_cast this
  exact amplifiedRepeatTau_mass hXpos hc₀ hZ hk horder (by linarith [hX.1])

theorem eventually_amplified_repeat_inputs (c c₀ : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T / 2 ≤ Real.log Z → Real.log Z ≤ 2 * T →
      1 ≤ z → T ^ auxiliaryExponent / 2 ≤ Real.log z →
      Real.log z ≤ 2 * T ^ auxiliaryExponent →
      ∀ J : ℕ, c * (Z : ℝ) / Real.log Z ≤ (J : ℝ) →
      let k := evenMomentParameter (parameterX T) Z
      let τ := amplifiedRepeatTau Z (auxiliaryK Z z) k
      ∀ I I₀ : ℝ, I₀ = (parameterX T : ℝ) * c₀ →
        Real.sqrt (parameterX T : ℝ) * Real.exp ((2 / 125 : ℝ) * auxiliaryK Z z) ≤ I →
        0 < τ ∧ I₀ * τ ^ k ≤ I ∧
          4 * ((((k : ℝ) + 1) * (k : ℝ) ^ 2 / J) *
            (τ + (k : ℝ) / Real.sqrt J) ^ (k - 2)) ≤ τ ^ k := by
  filter_upwards [eventually_amplifiedRepeatTau_error c hc,
    eventually_amplifiedRepeatTau_mass c₀ hc₀] with T herr hmass
  intro Z z hZl hZu hz hzl hzu J hJ k τ I I₀ hI₀ hI
  refine ⟨amplifiedRepeatTau_pos _ _ _, ?_, herr Z z hZl hZu hz hzl hzu J hJ⟩
  rw [hI₀]
  exact (hmass Z (auxiliaryK Z z) hZl).trans hI

end Ostmann.QuadraticCenter

end

end OAI
