import OAI.Geometry.RCD.Transport.CompressedPlanUnique

namespace OAI

/-! # Comparison of two arbitrary finite compression constants -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem compressed_plan_unique_finite (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    {ν₀ ν₁ : Measure X}
    (π ρ : Measure C(Time,X)) [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ) (hgρ : ∀ᵐ γ ∂ρ, IsGeodesic γ)
    (hpπ : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hpρ : IsOptimalCoupling ν₀ ν₁ (ρ.map (fun γ => (γ 0,γ 1))))
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hcπ : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    (hcρ : ∀ t : Time, ρ.map (fun γ => γ t) ≤ D • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs₁ : ∀ᵐ x ∂ν₁, dist x p ≤ R) : π=ρ := by
  let B : ℝ≥0 := ⟨C.toReal+D.toReal+1,by positivity⟩
  have hB : 0 < B := by change 0 < C.toReal+D.toReal+1; positivity
  have hCB : C ≤ ENNReal.ofReal B := by
    rw [←ENNReal.ofReal_toReal hC]
    apply ENNReal.ofReal_le_ofReal
    change C.toReal ≤ C.toReal+D.toReal+1
    linarith [ENNReal.toReal_nonneg (a:=D)]
  have hDB : D ≤ ENNReal.ofReal B := by
    rw [←ENNReal.ofReal_toReal hD]
    apply ENNReal.ofReal_le_ofReal
    change D.toReal ≤ C.toReal+D.toReal+1
    linarith [ENNReal.toReal_nonneg (a:=C)]
  apply hX.compressed_plan_unique hn p hR π ρ hgπ hgρ hpπ hpρ hB _ _ hs₀ hs₁
  · intro t
    apply (hcπ t).trans
    intro S
    exact mul_le_mul' hCB le_rfl
  · intro t
    apply (hcρ t).trans
    intro S
    exact mul_le_mul' hDB le_rfl

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
