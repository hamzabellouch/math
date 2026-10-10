import OAI.Geometry.NodalSets.Charts.CorrugationFrameBounds
import OAI.Geometry.NodalSets.Charts.CorrugationMetricErrorRescale
import OAI.Geometry.NodalSets.Elliptic.CorrugationOldData

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem corrugation_actual_metric_unit_errors
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (χ : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχrange : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) {A : ℝ} (hA : 0 < A)
    (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ A*(χ z)^((7:ℝ)/8))
    {amp : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s L : ℝ), 0 ≤ s → 0 < L → ∀ k : ℕ,
      ∀ y ∈ D, ∀ x ∈ D, ∀ e : Coord ≃L[ℝ] Coord,
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ∀ u v : Coord, g x u u = 1 → g x v v = 1 →
      let a := frozenFrameCovector e 2
      let b := frozenFrameCovector e 3
      let χ₀ := χ ((corrugationScale L k)⁻¹ • (x-y))
      let l := corrugationSlope amp (1/4)
        (corrugationCellRadius (corrugationFastMap (corrugationFrequency k) a b (x-y)))
      ∀ T : ℝ, 0 < T →
      (corrugationFrequency k*χ₀*l ≤ T →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤ C*s*corrugationLowErrorRate L T k) ∧
      (T < corrugationFrequency k*χ₀*l →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤
            C*s*corrugationHighErrorRate L T k*(corrugationFrequency k*χ₀*l)) := by
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨G,hG,hΓ⟩ := compact_connection_bound g hD hU hDU hg hp
  obtain ⟨C,hC,hbound⟩ := corrugation_actual_bounded_regime_errors χ hχ hc hχrange hA hχA
    ha ha1 (show 0 ≤ M*(1+c⁻¹) by positivity) hG.le (show 0 < 1+c⁻¹ by positivity)
  refine ⟨C,hC,?_⟩
  intro s L hs hL k y hy x hx e he u v hu hv
  exact hbound g s L hs hL k _ _ y x u v
    (metric_unit_coordinate_bound (g x) hc0 (hmetric x hx).2 u hu)
    (metric_unit_coordinate_bound (g x) hc0 (hmetric x hx).2 v hv)
    (frozenFrame_pair_norm_bound (g y) hc0 hM.le (hmetric y hy).2 (hmetric y hy).1 e he)
    (hΓ x hx)

end
end Yau.Geometry

end OAI
