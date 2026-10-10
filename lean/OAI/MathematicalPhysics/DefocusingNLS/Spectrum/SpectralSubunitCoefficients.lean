import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoefficientContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformAnnulus
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! Uniform decay of the actual two spectral potential coefficients on the
exterior subunit annulus. The polynomial factor in the power is retained. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralSubunitCoefficient_decay (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n : ℕ => (2*(n : ℝ)+1)*ρ^(2*n)) atTop (𝓝 0) := by
  have hq : ρ^2 < 1 := pow_lt_one₀ hρ hρ1 (by decide : 2 ≠ 0)
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ρ) hq
  have hn := tendsto_self_mul_const_pow_of_lt_one (sq_nonneg ρ) hq
  convert (hn.const_mul 2).add hp using 1
  · funext n
    rw [pow_mul]
    ring
  · norm_num

theorem spectralCoefficient_norm_sum (m : ℕ) (hm : 1 ≤ m) (q : ℂ) :
    ‖spectralDiagonalCoefficient m q‖+‖spectralCrossCoefficient m q‖=
      (2*(m : ℝ)+1)*‖q‖^(2*m) := by
  rw [spectralDiagonalCoefficient_norm,spectralCrossCoefficient_norm m hm]
  ring

theorem spectralCoefficient_subunit_bound (m : ℕ) (hm : 1 ≤ m) (q : ℂ)
    (ρ : ℝ) (hq : ‖q‖ ≤ ρ) :
    ‖spectralDiagonalCoefficient m q‖+‖spectralCrossCoefficient m q‖ ≤
      (2*(m : ℝ)+1)*ρ^(2*m) := by
  rw [spectralCoefficient_norm_sum m hm]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hq _) (by positivity)

theorem spectralCoefficient_zero (m : ℕ) (hm : 1 ≤ m) :
    spectralDiagonalCoefficient m 0=0 ∧ spectralCrossCoefficient m 0=0 := by
  have hmn : m ≠ 0 := by omega
  simp [spectralDiagonalCoefficient,spectralCrossCoefficient,hmn]

theorem circularBoundedField_subunit_bound (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℂ) (ρ : ℝ) (hq : ‖q‖ ≤ ρ) (z : E₄) :
    ‖circularBoundedField νp νm η m q z-circularBoundedField νp νm η m 0 z‖ ≤
      ((2*(m : ℝ)+1)*ρ^(2*m))*‖z‖ := by
  rw [circularBoundedField_coefficient_difference,
    (spectralCoefficient_zero m hm).1,(spectralCoefficient_zero m hm).2,sub_zero,sub_zero]
  exact (circularCoefficientAction_norm _ _ z).trans
    (mul_le_mul_of_nonneg_right (spectralCoefficient_subunit_bound m hm q ρ hq) (norm_nonneg z))

theorem radialShooting_spectralCoefficients_uniform_small :
    ∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall, ∀ t : ℝ,
        Real.log innerBoundaryRadius ≤ t →
          ‖spectralDiagonalCoefficient n
            (radialExteriorCanonical (radialShootingNu n z) n (radialShootingM z)
              (Real.log innerBoundaryRadius) t).1‖+
          ‖spectralCrossCoefficient n
            (radialExteriorCanonical (radialShootingNu n z) n (radialShootingM z)
              (Real.log innerBoundaryRadius) t).1‖ ≤ δ n := by
  obtain ⟨κ,ρ,hκ,hρ,he⟩ := radialShooting_uniform_annulus
  let σ := max ρ 0
  have hσ : 0 ≤ σ := le_max_right _ _
  have hσ1 : σ < 1 := max_lt hρ (by norm_num)
  refine ⟨fun n => (2*(n : ℝ)+1)*σ^(2*n),fun n => by positivity,
    spectralSubunitCoefficient_decay σ hσ hσ1,?_⟩
  filter_upwards [he,eventually_ge_atTop 1] with n hn hm z t ht
  exact spectralCoefficient_subunit_bound n hm _ σ ((hn z t ht).2.trans (le_max_left _ _))

end DefocusingNLS

end OAI
