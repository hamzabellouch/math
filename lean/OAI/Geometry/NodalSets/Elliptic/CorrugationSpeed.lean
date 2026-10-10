import OAI.Geometry.NodalSets.Charts.MetricNormalizationStabilityLemmas
import OAI.Geometry.NodalSets.Elliptic.CorrugationNormalizedGradient

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_speed_freezing
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
      |corrugationOldSlope g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x -
        corrugationOldSlope g S y * Real.sqrt (1+(χ ((corrugationScale L k)⁻¹ • (x-y))*
          corrugationSlope amp (1/4) (corrugationCellRadius
            (corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2)
              (frozenFrameCovector e 3) (x-y))))^2)| ≤
        corrugationOldSlope g S y*C*corrugationGradientRate L k := by
  obtain ⟨A,hA,hgrad⟩ := corrugation_gradient_freezing g S χ hD hconv hU hDU hg hS hp hn hχ hc hχ0 hχ1 ha ha1
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨G,hG,hfreeze⟩ := smooth_compact_freezing g hD hconv hU hDU hg
  let K : ℝ := 5*(1+c⁻¹)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let B : ℝ := 2*M*(K+1)+(K+1)^2
  have hB : 0 < B := by dsimp [B]; positivity
  let Q : ℝ := A+G+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨B*Q,mul_pos hB hQ,?_⟩
  have ht : Tendsto (fun k ↦ Q*corrugationGradientRate L k) atTop (𝓝 0) :=
    by simpa using (corrugationGradientRate_tendsto hL).const_mul Q
  filter_upwards [ht.eventually_lt_const zero_lt_one] with k hk
  intro y hy x hx hxy e he0 he
  let s := corrugationOldSlope g S y
  let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp) s
    (corrugationFrequency k) (corrugationScale L k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
  let w := corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e
    (corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))
  have hs := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hρ := (corrugationGradientRate_positive hL k).le
  have hJ := corrugationFrequency_positive k
  have hR := corrugationScale_positive hL k
  have hr : corrugationScale L k ≤ corrugationGradientRate L k := by
    dsimp [corrugationGradientRate]
    have hh : 0 ≤ 1/(corrugationFrequency k*corrugationScale L k) := by positivity
    linarith
  have hraw : ‖p-s • w‖ ≤ s*(A*corrugationGradientRate L k) := by
    simpa only [p,w,s,corrugationGradientRate,mul_assoc] using hgrad _ _ hJ hR y hy x hx hxy e he0 he
  have hd : ‖s⁻¹ • p-w‖ ≤ Q*corrugationGradientRate L k := by
    apply (inverse_scaled_vector_error p w hs hraw).trans
    exact mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith) hρ
  have hm : ‖g x-g y‖ ≤ Q*corrugationGradientRate L k := by
    calc
      _ ≤ G*‖x-y‖ := hfreeze x hx y hy
      _ ≤ G*corrugationGradientRate L k := mul_le_mul_of_nonneg_left (hxy.trans hr) hG.le
      _ ≤ Q*corrugationGradientRate L k := mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith) hρ
  have hw : ‖w‖ ≤ K := corrugationLeadingVector_bound (g y) hc0 (hmetric y hy).2 ha ha1
    (hχ0 _) (hχ1 _) e he _
  have hlen : 1 ≤ g y w w := corrugationLeadingVector_length_ge_one (g y) e he amp _ _
  have hpos : 0 ≤ g x (s⁻¹ • p) (s⁻¹ • p) :=
    (mul_nonneg hc0.le (sq_nonneg _)).trans ((hmetric x hx).2 _)
  have hh := metric_speed_uniform_stability hM.le hK (g x) (g y) (s⁻¹ • p) w
    (hmetric x hx).1 hw hpos hlen hd hm hk.le
  rw [metric_speed_smul (g x) p (inv_nonneg.mpr hs.le),
    corrugationLeadingVector_global_length (g y) e he] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hs.le
  nth_rw 1 [← abs_of_pos hs] at hh'
  rw [← abs_mul] at hh'
  have hid : s*(s⁻¹*Real.sqrt (g x p p)-Real.sqrt (1+
      (χ ((corrugationScale L k)⁻¹ • (x-y))*corrugationSlope amp (1/4)
        (corrugationCellRadius (corrugationFastMap (corrugationFrequency k)
          (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))))^2)) =
      Real.sqrt (g x p p)-s*Real.sqrt (1+
      (χ ((corrugationScale L k)⁻¹ • (x-y))*corrugationSlope amp (1/4)
        (corrugationCellRadius (corrugationFastMap (corrugationFrequency k)
          (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))))^2) := by
    rw [mul_sub,← mul_assoc,mul_inv_cancel₀ hs.ne',one_mul]
  rw [hid] at hh'
  simpa only [corrugationOldSlope,p,s,B,mul_assoc] using hh'

end
end Yau.Geometry

end OAI
