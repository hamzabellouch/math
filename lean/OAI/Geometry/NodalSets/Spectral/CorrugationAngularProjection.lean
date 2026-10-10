import OAI.Geometry.NodalSets.Elliptic.CorrugationDirectionEvaluations
import OAI.Geometry.NodalSets.Elliptic.CorrugationGradientRates
import OAI.Geometry.NodalSets.Elliptic.CorrugationProjectedDirections

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_actual_angular_estimates
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
      let r := frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
        ((corrugationCellPoint z).2/corrugationCellRadius z)
      let t := frozenPlaneVector e (-((corrugationCellPoint z).2/corrugationCellRadius z))
        ((corrugationCellPoint z).1/corrugationCellRadius z)
      let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
      let e' := metricNormalize (g x) p
      let q := metricPerpProjection (g x) e' t
      let t' := metricNormalize (g x) q
      corrugationCellRadius z ≠ 0 →
      q ≠ 0 ∧ g x t' t' = 1 ∧ g x e' t' = 0 ∧
        1/2 ≤ g y t t' ∧ |g y r t'| ≤ C*corrugationScale L k ∧
        |g y r e'| ≤ χ ((corrugationScale L k)⁻¹ • (x-y))*
          corrugationSlope amp (1/4) (corrugationCellRadius z)+C*corrugationScale L k := by
  obtain ⟨A,hA,hdir⟩ := corrugation_normalized_gradient_freezing g S χ hD hconv hU hDU
    hg hS hp hn hχ hc hχ0 hχ1 ha ha1 hL
  obtain ⟨B,hB,hproj⟩ := corrugation_projected_direction_freezing g S χ hD hconv hU hDU
    hg hS hp hn hχ hc hχ0 hχ1 ha ha1 hL
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  let K : ℝ := 1+c⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  let C : ℝ := 2*M*K*(A+B+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  have ht : Tendsto (fun k ↦ M*K*(B*corrugationGradientRate L k)) atTop (𝓝 0) := by
    simpa using ((corrugationGradientRate_tendsto hL).const_mul B).const_mul (M*K)
  filter_upwards [hdir,hproj,corrugationGradientRate_le_scale hL,
    ht.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with k hkdir hkproj hrate hsmall
  intro y hy x hx hxy e he0 he
  dsimp only
  let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
  let r := frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
    ((corrugationCellPoint z).2/corrugationCellRadius z)
  let t := frozenPlaneVector e (-((corrugationCellPoint z).2/corrugationCellRadius z))
    ((corrugationCellPoint z).1/corrugationCellRadius z)
  let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
  let e' := metricNormalize (g x) p
  let q := metricPerpProjection (g x) e' t
  let t' := metricNormalize (g x) q
  let w := corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e z
  intro hr
  have hrot := frozenPlaneVector_rotating_frame (g y) e he (corrugation_cell_unit_coefficients z hr)
  have hrr : g y r r = 1 := hrot.1
  have htt : g y t t = 1 := hrot.2.1
  have hrt : g y r t = 0 := hrot.2.2.1
  have hrB : ‖r‖ ≤ K := metric_unit_coordinate_bound (g y) hc0 (hmetric y hy).2 r hrr
  have htB : ‖t‖ ≤ K := metric_unit_coordinate_bound (g y) hc0 (hmetric y hy).2 t htt
  have hwt : g y w t = 0 := corrugationLeadingVector_angular_orthogonal (g y) e he amp _ z hr
  obtain ⟨hnq,hu,ho,hb⟩ := hkproj y hy x hx hxy e he0 he t htt hwt
  have hb' : ‖t'-t‖ ≤ B*corrugationGradientRate L k := hb
  have hrad := radial_angular_transfer (g y) r t t' hM.le hK.le (hmetric y hy).1 hrB htB hrt htt hb' hsmall.le
  have hd : ‖e'-metricNormalize (g y) w‖ ≤ A*corrugationGradientRate L k := hkdir y hy x hx hxy e he0 he
  have hpair := frozen_pairing_error (g y) r e' (metricNormalize (g y) w) hM.le hK.le
    (hmetric y hy).1 hrB hd
  have hlead : |g y r (metricNormalize (g y) w)| ≤
      χ ((corrugationScale L k)⁻¹ • (x-y))*corrugationSlope amp (1/4) (corrugationCellRadius z) :=
    corrugation_normalized_leading_radial_bound (g y) e he ha (hχ0 _) z hr
  have hR := (corrugationScale_positive hL k).le
  have hAc : M*K*(A*corrugationGradientRate L k) ≤ C*corrugationScale L k := by
    calc
      _ ≤ M*K*(A*(2*corrugationScale L k)) := by gcongr
      _ ≤ C*corrugationScale L k := by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hM.le hK.le) hR) (by linarith : 0 ≤ B+1)]
  have hBc : M*K*(B*corrugationGradientRate L k) ≤ C*corrugationScale L k := by
    calc
      _ ≤ M*K*(B*(2*corrugationScale L k)) := by gcongr
      _ ≤ C*corrugationScale L k := by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hM.le hK.le) hR) (by linarith : 0 ≤ A+1)]
  refine ⟨hnq,hu,ho,hrad.2,hrad.1.trans hBc,?_⟩
  calc
    _ ≤ |g y r e'-g y r (metricNormalize (g y) w)|+|g y r (metricNormalize (g y) w)| := by
      convert abs_add_le (g y r e'-g y r (metricNormalize (g y) w)) (g y r (metricNormalize (g y) w)) using 1
      congr 1
      ring
    _ ≤ M*K*(A*corrugationGradientRate L k)+
        χ ((corrugationScale L k)⁻¹ • (x-y))*corrugationSlope amp (1/4) (corrugationCellRadius z) := add_le_add hpair hlead
    _ ≤ _ := by linarith

end
end Yau.Geometry

end OAI
