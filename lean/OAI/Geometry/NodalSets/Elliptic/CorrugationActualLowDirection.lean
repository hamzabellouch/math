import OAI.Geometry.NodalSets.Elliptic.CorrugationGradientRates
import OAI.Geometry.NodalSets.Elliptic.CorrugationLowDirection

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_actual_low_direction
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
      corrugationFrequency k*χ ((corrugationScale L k)⁻¹ • (x-y))*
        corrugationSlope amp (1/4) (corrugationCellRadius z) ≤ T →
      ‖metricNormalize (g x) (metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x)-e (Pi.single 0 1)‖ ≤
        C*corrugationScale L k := by
  obtain ⟨A,hA,hdir⟩ := corrugation_normalized_gradient_freezing g S χ hD hconv hU hDU
    hg hS hp hn hχ hc hχ0 hχ1 ha ha1 hL
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨δ,B,hδ,hB,hlow⟩ := corrugation_low_leading_direction hc0 hM.le
  refine ⟨2*A+B,by linarith,?_⟩
  filter_upwards [hdir,corrugationGradientRate_le_scale hL,
    corrugation_low_tilt_le_scale (T := T) hL,
    (corrugationScale_tendsto L).eventually_lt_const hδ] with k hkdir hrate htilt hsmall
  intro y hy x hx hxy e he0 he
  dsimp only
  let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
  let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
  let w := corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e z
  intro hreg
  have ht : χ ((corrugationScale L k)⁻¹ • (x-y))*corrugationSlope amp (1/4) (corrugationCellRadius z) ≤
      corrugationScale L k := htilt _ _ hreg
  have hb := hlow (g y) (hmetric y hy).1 (hmetric y hy).2 e he amp
    (χ ((corrugationScale L k)⁻¹ • (x-y))) z ha (hχ0 _) (ht.trans hsmall.le)
  have hd : ‖metricNormalize (g x) p-metricNormalize (g y) w‖ ≤ A*corrugationGradientRate L k :=
    hkdir y hy x hx hxy e he0 he
  calc
    _ ≤ ‖metricNormalize (g x) p-metricNormalize (g y) w‖+
        ‖metricNormalize (g y) w-e (Pi.single 0 1)‖ := by
      convert norm_add_le (metricNormalize (g x) p-metricNormalize (g y) w)
        (metricNormalize (g y) w-e (Pi.single 0 1)) using 1
      congr 1
      module
    _ ≤ A*corrugationGradientRate L k+
        B*(χ ((corrugationScale L k)⁻¹ • (x-y))*corrugationSlope amp (1/4) (corrugationCellRadius z)) := add_le_add hd hb
    _ ≤ A*(2*corrugationScale L k)+B*corrugationScale L k :=
      add_le_add (mul_le_mul_of_nonneg_left hrate hA.le) (mul_le_mul_of_nonneg_left ht hB.le)
    _ = _ := by ring

end
end Yau.Geometry

end OAI
