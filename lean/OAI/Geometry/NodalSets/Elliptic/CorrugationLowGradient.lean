import OAI.Geometry.NodalSets.Elliptic.CorrugationGradientFreezing
import OAI.Geometry.NodalSets.Elliptic.CorrugationGradientRates

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_actual_low_gradient
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
      ‖metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x-metricGradient g S y‖ ≤
        C*corrugationScale L k := by
  obtain ⟨A,hA,hgrad⟩ := corrugation_gradient_freezing g S χ hD hconv hU hDU
    hg hS hp hn hχ hc hχ0 hχ1 ha ha1
  obtain ⟨m,hm,B,hB,hslope⟩ := corrugationOldSlope_compact_bounds g S hD hU hDU hg hS hp hn
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  let K : ℝ := 1+c⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨B*(2*A+4*K),by positivity,?_⟩
  filter_upwards [corrugationGradientRate_le_scale hL,
    corrugation_low_tilt_le_scale (T := T) hL] with k hrate htilt
  intro y hy x hx hxy e he0 he
  dsimp only
  intro hreg
  let s := corrugationOldSlope g S y
  let t := χ ((corrugationScale L k)⁻¹ • (x-y))
  let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
  let w := corrugationLeadingVector amp t e z
  let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    s (corrugationFrequency k) (corrugationScale L k)
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
  have hs : 0 < s := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hbase : s • e (Pi.single 0 1) = metricGradient g S y := by
    rw [he0,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  have ht : t*corrugationSlope amp (1/4) (corrugationCellRadius z) ≤ corrugationScale L k :=
    htilt _ _ hreg
  have hw : ‖s • w-metricGradient g S y‖ ≤ s*(4*K*corrugationScale L k) := by
    have hid : s • w-metricGradient g S y = s • (t • corrugationFastVector amp e z) := by
      rw [← hbase]; dsimp [w,corrugationLeadingVector]; module
    rw [hid,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hs,abs_of_nonneg (hχ0 _)]
    apply mul_le_mul_of_nonneg_left _ hs.le
    calc
      t*‖corrugationFastVector amp e z‖ ≤
          t*(4*corrugationSlope amp (1/4) (corrugationCellRadius z)*K) :=
        mul_le_mul_of_nonneg_left (corrugationFastVector_bound (g y) hc0 (hmetric y hy).2 ha e he z) (hχ0 _)
      _ = 4*K*(t*corrugationSlope amp (1/4) (corrugationCellRadius z)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)
  have hd : ‖p-s • w‖ ≤ s*A*corrugationGradientRate L k :=
    hgrad _ _ (corrugationFrequency_positive k) (corrugationScale_positive hL k) y hy x hx hxy e he0 he
  calc
    ‖p-metricGradient g S y‖ ≤ ‖p-s • w‖+‖s • w-metricGradient g S y‖ := by
      convert norm_add_le (p-s • w) (s • w-metricGradient g S y) using 1
      congr 1
      module
    _ ≤ s*A*(2*corrugationScale L k)+s*(4*K*corrugationScale L k) :=
      add_le_add (hd.trans (mul_le_mul_of_nonneg_left hrate (by positivity))) hw
    _ = s*(2*A+4*K)*corrugationScale L k := by ring
    _ ≤ B*(2*A+4*K)*corrugationScale L k := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hslope y hy).2 (by positivity))
        (corrugationScale_positive hL k).le

end
end Yau.Geometry

end OAI
