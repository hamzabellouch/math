import OAI.Geometry.NodalSets.Elliptic.CorrugationActualLowDirection
import OAI.Geometry.NodalSets.Elliptic.CorrugationDirectionEvaluations
import OAI.Geometry.NodalSets.Elliptic.CorrugationProjectedDirections

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_actual_low_radial
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
      let r := frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
        ((corrugationCellPoint z).2/corrugationCellRadius z)
      let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
      let e' := metricNormalize (g x) p
      let q := metricPerpProjection (g x) e' (e (Pi.single 1 1))
      let t' := metricNormalize (g x) q
      corrugationCellRadius z ≠ 0 →
      corrugationFrequency k*χ ((corrugationScale L k)⁻¹ • (x-y))*
        corrugationSlope amp (1/4) (corrugationCellRadius z) ≤ T →
      |g y r e'| ≤ C*corrugationScale L k ∧ |g y r t'| ≤ C*corrugationScale L k := by
  obtain ⟨A,hA,hdir⟩ := corrugation_actual_low_direction g S χ hD hconv hU hDU
    hg hS hp hn hχ hc hχ0 hχ1 ha ha1 hL T
  obtain ⟨B,hB,hproj⟩ := corrugation_projected_direction_freezing g S χ hD hconv hU hDU
    hg hS hp hn hχ hc hχ0 hχ1 ha ha1 hL
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  let K : ℝ := 1+c⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  let C : ℝ := M*K*(A+2*B)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hdir,hproj,corrugationGradientRate_le_scale hL] with k hkdir hkproj hrate
  intro y hy x hx hxy e he0 he
  dsimp only
  let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
  let r := frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
    ((corrugationCellPoint z).2/corrugationCellRadius z)
  let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
  let e' := metricNormalize (g x) p
  let q := metricPerpProjection (g x) e' (e (Pi.single 1 1))
  let t' := metricNormalize (g x) q
  intro hr hreg
  have hrr : g y r r = 1 := (frozenPlaneVector_rotating_frame (g y) e he
    (corrugation_cell_unit_coefficients z hr)).1
  have hrB : ‖r‖ ≤ K := metric_unit_coordinate_bound (g y) hc0 (hmetric y hy).2 r hrr
  have h0 : g y r (e (Pi.single 0 1)) = 0 :=
    (frozenPlaneVector_axis_pair (g y) e he _ _ 0 (by decide)).2
  have h1 : g y r (e (Pi.single 1 1)) = 0 :=
    (frozenPlaneVector_axis_pair (g y) e he _ _ 1 (by decide)).2
  have hd : ‖e'-e (Pi.single 0 1)‖ ≤ A*corrugationScale L k := hkdir y hy x hx hxy e he0 he hreg
  have htunit : g y (e (Pi.single 1 1)) (e (Pi.single 1 1)) = 1 := by simpa using he 1 1
  obtain ⟨_,_,_,htd⟩ := hkproj y hy x hx hxy e he0 he _ htunit
    (corrugationLeadingVector_second_orthogonal (g y) e he amp _ _)
  have hd' : ‖t'-e (Pi.single 1 1)‖ ≤ 2*B*corrugationScale L k :=
    htd.trans ((mul_le_mul_of_nonneg_left hrate hB.le).trans_eq (by ring))
  have hpe := frozen_pairing_error (g y) r e' (e (Pi.single 0 1)) hM.le hK.le (hmetric y hy).1 hrB hd
  have hpt := frozen_pairing_error (g y) r t' (e (Pi.single 1 1)) hM.le hK.le (hmetric y hy).1 hrB hd'
  rw [h0,sub_zero] at hpe
  rw [h1,sub_zero] at hpt
  have hR := (corrugationScale_positive hL k).le
  constructor
  · exact hpe.trans (by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hM.le hK.le) hB.le) hR])
  · exact hpt.trans (by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hM.le hK.le) hA.le) hR])

end
end Yau.Geometry

end OAI
