import OAI.Analysis.IrrationalRotation.Analysis.OrbitInvariance
import OAI.Analysis.IrrationalRotation.Rotation.PositiveDiagonal
import OAI.Analysis.IrrationalRotation.Rotation.ProjectionDiagonalPropagation

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace

namespace Invariant233.Fields

theorem ae_strict_projection_diagonal
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
    {σ : Y → Y} (hσ : Ergodic σ μ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p D : Y → H →L[ℂ] H} {e : H} (he : ‖e‖ = 1) {f : Y → ℝ}
    (hp : ∀ᵐ y ∂μ, IsStarProjection (p y))
    (hD : ∀ᵐ y ∂μ, IsSelfAdjoint (D y))
    (hf : ∀ᵐ y ∂μ, f y ≠ 0)
    (heigen : ∀ᵐ y ∂μ, D y e = (f y : ℂ) • e)
    (hinv : ∀ᵐ y ∂μ, (1 - p (σ y)) * D y * p y = 0)
    (hr : Measurable fun y => (⟪e, p y e⟫_ℂ).re)
    (hmean0 : 0 < ∫ y, (⟪e, p y e⟫_ℂ).re ∂μ)
    (hmean1 : (∫ y, (⟪e, p y e⟫_ℂ).re ∂μ) < 1) :
    ∀ᵐ y ∂μ, 0 < (⟪e, p y e⟫_ℂ).re ∧ (⟪e, p y e⟫_ℂ).re < 1 := by
  have hps : ∀ᵐ y ∂μ, IsStarProjection (p (σ y)) :=
    hσ.toMeasurePreserving.quasiMeasurePreserving.ae hp
  have hprop : ∀ᵐ y ∂μ,
      ((⟪e, p (σ y) e⟫_ℂ).re = 0 → (⟪e, p y e⟫_ℂ).re = 0) ∧
      ((⟪e, p y e⟫_ℂ).re = 1 → (⟪e, p (σ y) e⟫_ℂ).re = 1) := by
    filter_upwards [hp, hps, hD, hf, heigen, hinv] with y hpy hpsy hDy hfy hey hiy
    exact InvariantProjection.projection_real_diagonal_propagation
      hpy hpsy hDy he hfy hey hiy
  apply ae_strict_diagonal_of_ergodic hσ hr ?_ hmean0 hmean1
    (hprop.mono fun _ h => h.1) (hprop.mono fun _ h => h.2)
  filter_upwards [hp] with y hpy
  simpa only [he, one_pow] using InvariantProjection.projection_re_inner_bounds hpy e

theorem ae_strict_projection_diagonal_of_weighted_shift
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
    {σ : Y → Y} (hσ : Ergodic σ μ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p D : Y → H →L[ℂ] H} (S : (H →L[ℂ] H)ˣ)
    {e : H} (he : ‖e‖ = 1) {f : Y → ℝ}
    (hp : ∀ᵐ y ∂μ, IsStarProjection (p y))
    (hD : ∀ᵐ y ∂μ, IsSelfAdjoint (D y))
    (hf : ∀ᵐ y ∂μ, f y ≠ 0)
    (heigen : ∀ᵐ y ∂μ, D y e = (f y : ℂ) • e)
    (hcov : ∀ᵐ y ∂μ, p (σ y) = ↑(S⁻¹) * p y * (S : H →L[ℂ] H))
    (hinv : ∀ᵐ y ∂μ, (1 - p y) * ((S : H →L[ℂ] H) * D y) * p y = 0)
    (hr : Measurable fun y => (⟪e, p y e⟫_ℂ).re)
    (hmean0 : 0 < ∫ y, (⟪e, p y e⟫_ℂ).re ∂μ)
    (hmean1 : (∫ y, (⟪e, p y e⟫_ℂ).re ∂μ) < 1) :
    ∀ᵐ y ∂μ, 0 < (⟪e, p y e⟫_ℂ).re ∧ (⟪e, p y e⟫_ℂ).re < 1 := by
  apply ae_strict_projection_diagonal hσ he hp hD hf heigen ?_ hr hmean0 hmean1
  filter_upwards [hcov, hinv] with y hcy hiy
  rw [hcy]
  exact OrbitInvariance.orbit_inclusion S (D y) hiy

end Invariant233.Fields

end OAI
