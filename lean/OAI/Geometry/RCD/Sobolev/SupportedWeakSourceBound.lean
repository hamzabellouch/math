import OAI.Geometry.RCD.Sobolev.WeakSourceGradientBound

namespace OAI

/-! # Compactly supported tests for the vanishing viscosity term -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem supported_test_slope_integrable (φ : SobolevSpace μ Q)
    {Ω : Set X} (hμΩ : μ Ω ≠ ∞)
    (hs : ∀ᵐ x ∂μ, x ∉ Ω → SobolevSpace.toLp μ Q φ x = 0) :
    Integrable (SobolevSpace.minimalSlope μ Q φ) μ := by
  have hi := lp_integrableOn_of_finite μ (SobolevSpace.minimalSlope μ Q φ) Ω hμΩ
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [hs,SobolevSpace.minimalSlope_zero_on_zero μ Q φ] with x hx hz
  exact fun h => hz (hx h)

theorem supported_weak_source_test_bound (w φ : SobolevSpace μ Q)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ Q w q)
    {Ω : Set X} (hΩ : MeasurableSet Ω) (hμΩ : μ Ω ≠ ∞)
    (hs : ∀ᵐ x ∂μ, x ∉ Ω → SobolevSpace.toLp μ Q φ x = 0)
    {L : ℝ} (hgrad : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q w x ≤ L) :
    |inner ℝ q (SobolevSpace.toLp μ Q φ)| ≤ L * ∫ x, SobolevSpace.minimalSlope μ Q φ x ∂μ := by
  apply weak_source_test_gradient_bound μ Q w φ q hq _ (supported_test_slope_integrable μ Q φ hμΩ hs)
  filter_upwards [(ae_restrict_iff' hΩ).mp hgrad,hs] with x hx hz
  intro hφ
  apply hx
  by_contra hnot
  exact hφ (hz hnot)

theorem supported_weak_source_vanishes
    (w : ℕ → SobolevSpace μ Q) (q : ℕ → Lp ℝ 2 μ)
    (hq : ∀ k, IsWeakLaplacian μ Q (w k) (q k)) (φ : SobolevSpace μ Q)
    {Ω : Set X} (hΩ : MeasurableSet Ω) (hμΩ : μ Ω ≠ ∞)
    (hs : ∀ᵐ x ∂μ, x ∉ Ω → SobolevSpace.toLp μ Q φ x = 0)
    {L : ℝ} (hgrad : ∀ k, ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q (w k) x ≤ L)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ε k * inner ℝ (q k) (SobolevSpace.toLp μ Q φ)) atTop (𝓝 0) := by
  let C := L * ∫ x, SobolevSpace.minimalSlope μ Q φ x ∂μ
  have hb (k : ℕ) : ‖ε k * inner ℝ (q k) (SobolevSpace.toLp μ Q φ)‖ ≤ |ε k| * C := by
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left
      (supported_weak_source_test_bound μ Q (w k) φ (q k) (hq k) hΩ hμΩ hs (hgrad k)) (abs_nonneg _)
  have hh := hε.abs.mul_const C
  simp only [abs_zero,zero_mul] at hh
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun k => norm_nonneg _) hb hh

end RegularPointCoordinates

end

end OAI
