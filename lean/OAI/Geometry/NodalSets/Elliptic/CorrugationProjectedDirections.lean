import OAI.Geometry.NodalSets.Elliptic.CorrugationNonvanishing
import OAI.Geometry.NodalSets.Elliptic.CorrugationNormalizedGradient
import OAI.Geometry.NodalSets.Spectral.MetricProjectionStability

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_projected_direction_freezing
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
      let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
      let w := corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e
        (corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))
      ∀ t : Coord, g y t t = 1 → g y w t = 0 →
      let q := metricPerpProjection (g x) (metricNormalize (g x) p) t
      q ≠ 0 ∧ g x (metricNormalize (g x) q) (metricNormalize (g x) q) = 1 ∧
        g x (metricNormalize (g x) p) (metricNormalize (g x) q) = 0 ∧
        ‖metricNormalize (g x) q-t‖ ≤ C*corrugationGradientRate L k := by
  obtain ⟨A,hA,hdir⟩ := corrugation_normalized_gradient_freezing g S χ hD hconv hU hDU
    hg hS hp hn hχ hc hχ0 hχ1 ha ha1 hL
  have hnv := corrugation_local_nonvanishing g S χ hD hconv hU hDU hg hS hp hn hχ hc amp hL
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨G,hG,hfreeze⟩ := smooth_compact_freezing g hD hconv hU hDU hg
  let K : ℝ := 1+c⁻¹
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨ε₀,B,hε₀,hB,hstab⟩ := metric_projection_uniform_stability hM.le hK
  let Q : ℝ := A+G+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨B*Q,mul_pos hB hQ,?_⟩
  have ht : Tendsto (fun k ↦ Q*corrugationGradientRate L k) atTop (𝓝 0) :=
    by simpa using (corrugationGradientRate_tendsto hL).const_mul Q
  filter_upwards [hdir,hnv,ht.eventually_lt_const hε₀] with k hkdir hknv hk
  intro y hy x hx hxy e he0 he
  dsimp only
  let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
  let w := corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e
    (corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))
  intro t htunit horth
  have hpunit : g x (metricNormalize (g x) p) (metricNormalize (g x) p) = 1 :=
    metricNormalize_unit (g x) p (hp x (hDU hx) p (hknv y hy x hx hxy e he0 he))
  have hwlen : 0 < g y w w := lt_of_lt_of_le zero_lt_one
    (corrugationLeadingVector_length_ge_one (g y) e he amp _ _)
  have hwunit := metricNormalize_unit (g y) w hwlen
  have heB := metric_unit_coordinate_bound (g x) hc0 (hmetric x hx).2 _ hpunit
  have he₀B := metric_unit_coordinate_bound (g y) hc0 (hmetric y hy).2 _ hwunit
  have htB := metric_unit_coordinate_bound (g y) hc0 (hmetric y hy).2 t htunit
  change g y w t = 0 at horth
  have horth' : g y (metricNormalize (g y) w) t = 0 := by
    simp [metricNormalize,map_smul,horth]
  have hρ := (corrugationGradientRate_positive hL k).le
  have hd : ‖metricNormalize (g x) p-metricNormalize (g y) w‖ ≤ Q*corrugationGradientRate L k :=
    (hkdir y hy x hx hxy e he0 he).trans
      (mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith) hρ)
  have hr : corrugationScale L k ≤ corrugationGradientRate L k := by
    have hJ := corrugationFrequency_positive k
    have hR := corrugationScale_positive hL k
    have hh : 0 ≤ 1/(corrugationFrequency k*corrugationScale L k) := by positivity
    dsimp [corrugationGradientRate]
    linarith
  have hm : ‖g x-g y‖ ≤ Q*corrugationGradientRate L k := by
    calc
      _ ≤ G*‖x-y‖ := hfreeze x hx y hy
      _ ≤ G*corrugationGradientRate L k := mul_le_mul_of_nonneg_left (hxy.trans hr) hG.le
      _ ≤ Q*corrugationGradientRate L k := mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith) hρ
  obtain ⟨hnq,hu,ho,hb⟩ := hstab (g x) (g y) (metricNormalize (g x) p) (metricNormalize (g y) w) t
    (Q*corrugationGradientRate L k) (hmetric x hx).1 heB he₀B htB hpunit htunit horth' hd hm hk.le
  refine ⟨hnq,hu,ho,?_⟩
  convert hb using 1
  ring

end
end Yau.Geometry

end OAI
