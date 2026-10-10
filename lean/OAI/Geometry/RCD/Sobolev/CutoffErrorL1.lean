import OAI.Geometry.RCD.Sobolev.CutoffErrorEstimates

namespace OAI

/-! # Quantitative L1 control of the annular product-rule error -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

/-- The source is estimated on its actual support. Young's inequality
uses only the energy-gradient integral on the enclosing ball. -/
theorem GoodLaplacianCutoff.error_L1_le {p : X} {ρ C R B : ℝ}
    (χ : GoodLaplacianCutoff μ hQ p ρ C) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hroom : 2 * ρ < R) (g : SobolevSpace μ hQ)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ B) :
    (∫ x, |cutoffSourceDensity μ hQ g χ.sobolev χ.laplacian x| ∂μ) ≤
      (B * (C / ρ ^ 2) + (C / ρ) ^ 2) * μ.real (ball p R) +
        ∫ x in ball p R, localGamma μ hQ g g x ∂μ := by
  let S := ball p R
  let f := cutoffSourceDensity μ hQ g χ.sobolev χ.laplacian
  have : IsFiniteMeasure (μ.restrict S) :=
    ⟨by simpa only [S, Measure.restrict_apply_univ] using isBounded_ball.measure_lt_top⟩
  have hf : Integrable f μ := cutoffSourceDensity_integrable μ hQ _ _ _
  have hz : ∀ᵐ x ∂μ, x ∉ S → f x = 0 := by
    filter_upwards [χ.error_zero_off_annulus μ hQ g] with x hx hn
    apply hx
    intro ha
    have hd : dist x p < R := by rw [dist_comm]; exact ha.2.trans_lt hroom
    exact hn hd
  have heq : (∫ x, |f x| ∂μ) = ∫ x in S, |f x| ∂μ := by
    symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hz] with x hx hn
    rw [hx hn, abs_zero]
  have hslope := SobolevSpace.minimalSlope_le_lipschitz μ hQ χ.sobolev
    χ.lipschitz χ.representative
  have hbound : ∀ᵐ x ∂μ.restrict S,
      |f x| ≤ B * (C / ρ ^ 2) + (C / ρ) ^ 2 + localGamma μ hQ g g x := by
    filter_upwards [ae_restrict_of_ae hg, ae_restrict_of_ae χ.laplacian_bound,
      ae_restrict_of_ae (localGamma_abs_le μ hQ g χ.sobolev),
      ae_restrict_of_ae (localGamma_self μ hQ g), ae_restrict_of_ae hslope,
      ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ g))]
      with x hx hq hcross hself hs hsl0
    have hterm : |SobolevSpace.toLp μ hQ g x * χ.laplacian x| ≤ B * (C / ρ ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul hx hq (abs_nonneg _) (le_trans (abs_nonneg _) hx)
    have hs' : SobolevSpace.minimalSlope μ hQ χ.sobolev x ≤ C / ρ := by
      simpa only [Real.coe_toNNReal (C / ρ) (div_nonneg hC hρ.le)] using hs
    have hcross' := hcross.trans (mul_le_mul_of_nonneg_left hs' hsl0)
    have hy := sq_nonneg (SobolevSpace.minimalSlope μ hQ g x - C / ρ)
    have habs := abs_add_le (SobolevSpace.toLp μ hQ g x * χ.laplacian x)
      (2 * localGamma μ hQ g χ.sobolev x)
    dsimp only [f, cutoffSourceDensity]
    simp only [abs_mul, show |(2 : ℝ)| = 2 by norm_num] at habs hterm
    nlinarith only [hterm, hcross', hy, hself, habs]
  rw [heq]
  have hi := (integrable_const (μ := μ.restrict S) (B * (C / ρ ^ 2) + (C / ρ) ^ 2)).add
    (localGamma_memL1 μ hQ g g).integrableOn
  have hb := integral_mono_ae hf.abs.integrableOn hi hbound
  change (∫ x in S, |f x| ∂μ) ≤ ∫ x in S,
    (B * (C / ρ ^ 2) + (C / ρ) ^ 2) + localGamma μ hQ g g x ∂μ at hb
  rw [integral_add (integrable_const _) (localGamma_memL1 μ hQ g g).integrableOn] at hb
  simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, S, mul_comm] using hb

end RegularPointCoordinates

end

end OAI
