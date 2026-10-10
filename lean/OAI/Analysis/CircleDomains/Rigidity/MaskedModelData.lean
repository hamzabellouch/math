import OAI.Analysis.CircleDomains.Transfer.PrincipalSubordinateGraphTransfer

namespace OAI

/-! The actual masked coordinates and metric on one finite circle model.
The record retains the exact source and transported energy identities,
as well as the filling and core equalities needed by the limiting tests. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure MaskedModelData {J I : Type*} {n : ℕ}
    (T : J → ℂ ≃ₜ ℂ) (H : I → ℂ ≃ₜ ℂ) (G K : Set (ℝ × ℝ))
    (M : Fin n → Set (ℝ × ℝ)) (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (θ : Fin n → ℝ) (ε : ℝ) where
  widthIndex : ℕ
  base : Fin n → (ℝ × ℝ) → UnitAddCircle
  base_mask : ∀ l, base l =ᶠ[𝓝ˢ (M l)] f l
  base_core : ∀ᶠ z in 𝓝ˢ K, ∀ l, base l z = f l z
  functions : Fin n → (ℝ × ℝ) → UnitAddCircle
  filled : IsMaskedFilledCircleFamily (fun i => realJordanInterior (H i))
    (G ∪ ⋃ i, realJordanInterior (H i)) M
    (circleCutoffFamily base χ N (staircaseWidth (reciprocalGridStep N) widthIndex) θ) functions
  extension_contains : realChartDomain (completedRegion T) ⊆ G ∪ ⋃ i, realJordanInterior (H i)
  mask_boundary_core : ∀ l, frontier (M l) ⊆ interior K
  retained : ∀ᶠ z in 𝓝ˢ K, ∀ l, functions l z = f l z
  radius : ℝ
  radius_pos : 0 < radius
  metric : (ℝ × ℝ) → PlanarMetric
  metric_smooth : ContDiff ℝ ∞ metric
  metric_pos : ∀ z, (metric z).PosDef
  metric_core : ∀ᶠ z in 𝓝ˢ K, metric z = sphericalMetricFactor z • 1
  metric_far : ∀ z ∉ Metric.closedBall 0 radius, metric z = sphericalMetricFactor z • 1
  tail : (∑ l : Fin n, ∫ z in (realChartDomain (completedRegion T) \ K) ∩ M l,
    fieldEnergy (circleGradient (functions l)) metric z) < ε
  localized : ∀ l (E : Set (ℝ × ℝ)), MeasurableSet E → E ⊆ K →
    (∫ z in (realChartDomain (completedRegion T) \ E) ∩ M l,
      fieldEnergy (circleGradient (functions l)) metric z) <
    (∫ z in (G \ E) ∩ M l, fieldEnergy (circleGradient (f l))
      (fun z => sphericalMetricFactor z • 1) z) + ε
  domain : Set Sphere
  forward : Sphere → Sphere
  inverse : Sphere → Sphere
  circle_domain : IsCircleDomain domain
  equivalence : IsSmoothSphereEquivalence forward inverse (openCompletedRegion T) domain
  conformal_core : IsConformalOn forward (sphericalCore K)
  principal : IsPrincipalNormalized forward
  transported : ∀ l, IsOpen (sphereRealMap forward ''
      (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
    SmoothCircleOn (functions l ∘ sphereRealMap inverse)
      (sphereRealMap forward '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
    (∀ x ∈ realChartDomain (openCompletedRegion T) ∩ interior (M l),
      ((functions l ∘ sphereRealMap inverse) ∘ sphereRealMap forward) =ᶠ[𝓝 x] functions l)
  transported_energy : ∀ l (s : Set (ℝ × ℝ)), MeasurableSet s →
    s ⊆ realChartDomain (openCompletedRegion T) ∩ interior (M l) →
    (∫ y in sphereRealMap forward '' s,
      fieldEnergy (circleGradient (functions l ∘ sphereRealMap inverse)) (fun _ => 1) y) =
    ∫ x in s, fieldEnergy (circleGradient (functions l)) metric x

end CircleDomainRigidity.FiniteTransfer

end

end OAI
