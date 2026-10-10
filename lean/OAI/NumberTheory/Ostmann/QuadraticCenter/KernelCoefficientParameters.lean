import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientGrowth

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem kernel_mean_loss_of_repeat_scale {k J : ℕ} {c : ℝ} (hc : 0 < c)
    (hscale : 4*((k : ℝ)+1)^2 ≤ Real.sqrt (J : ℝ)*c) :
    0 < J ∧ 2*(k : ℝ)/(J : ℝ) ≤ c/2 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hJ : 0 < J := by
    by_contra hh
    have hzero : J = 0 := by omega
    simp only [hzero, Nat.cast_zero, Real.sqrt_zero, zero_mul] at hscale
    nlinarith [sq_nonneg (k : ℝ)]
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hroot : Real.sqrt (J : ℝ) ≤ J := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hh := hscale.trans (mul_le_mul_of_nonneg_right hroot hc.le)
  refine ⟨hJ, (div_le_iff₀ (by exact_mod_cast hJ : (0 : ℝ) < J)).mpr ?_⟩
  nlinarith [sq_nonneg ((k : ℝ)-1)]

theorem eventually_kernel_population_inputs (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (Z J : ℕ), T/2 ≤ Real.log Z →
      commonCenterCutoff Z ≤ J →
      let k := evenMomentParameter (parameterX T) Z
      2 ≤ k ∧ Even k ∧ 0 < J ∧ 2*k ≤ J ∧
        2*(k : ℝ)/(J : ℝ) ≤ c/2 ∧
        4*((k : ℝ)+1)^2 ≤ Real.sqrt (J : ℝ)*c := by
  filter_upwards [eventually_kernel_repeat_scale c hc,
    eventually_kernel_repeat_scale 1 (by norm_num), eventually_parameterX_log_bounds]
    with T hscale hone hX
  intro Z J hZl hJ
  dsimp only
  let k := evenMomentParameter (parameterX T) Z
  have hZ : 0 < Real.log Z := by linarith [hX.1]
  have hXlog : 0 ≤ Real.log (parameterX T : ℝ) := by linarith [hX.2.1]
  have hratio : 0 ≤ Real.log (parameterX T : ℝ)/Real.log Z := by positivity
  have horder := (evenMomentParameter_bounds (parameterX T) Z (by positivity)).1
  have hk : 2 ≤ k := by
    have : (2 : ℝ) ≤ k := by dsimp [k]; linarith
    exact_mod_cast this
  have hh := kernel_mean_loss_of_repeat_scale hc (hscale Z J hZl hJ)
  have hunit := kernel_mean_loss_of_repeat_scale (by norm_num : (0 : ℝ) < 1)
    (hone Z J hZl hJ)
  have htwice : 2*k ≤ J := by
    have hraw := (div_le_iff₀ (by exact_mod_cast hh.1 : (0 : ℝ) < J)).mp hunit.2
    have : (2 : ℝ)*k ≤ J := by nlinarith [show (0 : ℝ) ≤ J from Nat.cast_nonneg J]
    exact_mod_cast this
  exact ⟨hk, evenMomentParameter_even _ _, hh.1, htwice, hh.2, hscale Z J hZl hJ⟩

end Ostmann.QuadraticCenter

end

end OAI
