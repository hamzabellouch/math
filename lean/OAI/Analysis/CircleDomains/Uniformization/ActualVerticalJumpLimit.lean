import OAI.Analysis.CircleDomains.Selection.ActualVerticalScalarJump

namespace OAI

/-! The constructed finite fillings have vanishing distributional errors.
Consequently every weak limit of their two pairings satisfies the vertical
weak derivative identity. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem filled_vertical_error_tendsto (harea : ExteriorCoefficientAreaTheorem)
    (i : Fin m) (hQ : Continuous (Q i).quotient) (F : ∀ n, R.HoleFilling i n)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    Tendsto (fun n => (∫ z, (F n).filled z * fderiv ℝ φ z Complex.I) +
      (∫ z, fderiv ℝ (F n).filled z Complex.I * φ z)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hs
  have hCpos : 0 ≤ C := (norm_nonneg (φ 0)).trans (hC 0)
  have hlim : Tendsto (fun n => 4 * C * (3 * R.model.radius * modelError n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (modelError_tendsto.const_mul (3 * R.model.radius)).const_mul (4 * C)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [R.eventually_filled_vertical_jump i, R.eventually_hole_cost_bound harea i hQ]
    with n hn hcost
  rw [Real.norm_eq_abs]
  exact (hn (F n) φ hφ hs C hCpos (fun z => by simpa only [Real.norm_eq_abs] using hC z)).trans
    (mul_le_mul_of_nonneg_left (hcost (F n)).le (mul_nonneg (by norm_num) hCpos))

 theorem vertical_weak_limit_identity (harea : ExteriorCoefficientAreaTheorem)
    (i : Fin m) (hQ : Continuous (Q i).quotient) (F : ∀ n, R.HoleFilling i n)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {V G : ℂ → ℝ}
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hV : Tendsto (fun n => ∫ z, (F (σ n)).filled z * fderiv ℝ φ z Complex.I)
      atTop (𝓝 (∫ z, V z * fderiv ℝ φ z Complex.I)))
    (hG : Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z Complex.I * φ z)
      atTop (𝓝 (∫ z, G z * φ z))) :
    (∫ z, V z * fderiv ℝ φ z Complex.I) = -(∫ z, G z * φ z) := by
  have hzero := (R.filled_vertical_error_tendsto harea i hQ F hφ hs).comp hσ.tendsto_atTop
  have he := tendsto_nhds_unique (hV.add hG) hzero
  linarith

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
