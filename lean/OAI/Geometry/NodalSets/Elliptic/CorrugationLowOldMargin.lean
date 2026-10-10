import OAI.Geometry.NodalSets.Elliptic.CorrugationDirectionEvaluations
import OAI.Geometry.NodalSets.Elliptic.CorrugationLowGradient
import OAI.Geometry.NodalSets.Elliptic.CorrugationProjectedDirections
import OAI.Geometry.NodalSets.Elliptic.CorrugationStrictMargin
import OAI.Geometry.NodalSets.Elliptic.WeightedHessianStability

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_actual_low_old_margin
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ D, ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ D, metricGradient g S y ≠ 0 ∧
      ∃ q : Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
    (hχ : ContDiff ℝ ∞ χ) (hcpt : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      (∀ u, g y u u = 1 → g y (metricGradient g S y) u = 0 →
        sourceHessian g S y u u ≤ sourceHessian g S y (e (Pi.single 1 1)) (e (Pi.single 1 1))) →
      let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
      let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
      let q := metricPerpProjection (g x) (metricNormalize (g x) p) (e (Pi.single 1 1))
      let t := metricNormalize (g x) q
      corrugationFrequency k*χ ((corrugationScale L k)⁻¹ • (x-y))*
        corrugationSlope amp (1/4) (corrugationCellRadius z) ≤ T →
      q ≠ 0 ∧ g x t t = 1 ∧ g x (metricNormalize (g x) p) t = 0 ∧
        c ≤ (g x p p/(g x p p+4))*sourceHessian g S x (metricNormalize (g x) p)
          (metricNormalize (g x) p)+sourceHessian g S x t t := by
  have hn : ∀ y ∈ D, metricGradient g S y ≠ 0 := fun y hy ↦ (hadm y hy).1
  obtain ⟨c,hc,hmargin⟩ := corrugation_old_uniform_margin g S hD hU hDU hg hS hp hsym hadm
  obtain ⟨a,ha0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  have hcP : ContinuousOn (metricGradient g S) D := by
    intro y hy
    exact (localMetricGradient_continuousAt g S y
      (hg.contDiffAt (hU.mem_nhds (hDU hy))).continuousAt
      (hS.contDiffAt (hU.mem_nhds (hDU hy))) (hp y (hDU hy))).continuousWithinAt
  have hcH : ContinuousOn (sourceHessian g S) D := by
    intro y hy
    exact (localMetricHessian_continuousAt g S y
      (hg.contDiffAt (hU.mem_nhds (hDU hy))) (hS.contDiffAt (hU.mem_nhds (hDU hy)))
      (hp y (hDU hy))).continuousWithinAt
  obtain ⟨G,hG,hGB⟩ := (hD.image_of_continuousOn hcP).isBounded.exists_pos_norm_le
  have hgp : ∀ y ∈ D, ‖metricGradient g S y‖ ≤ G := fun y hy ↦ hGB _ ⟨y,hy,rfl⟩
  let K : ℝ := G+1+(1+a⁻¹)
  have hKp : G+1 ≤ K := by
    have hi : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
    dsimp [K]; linarith
  have hKt : 1+a⁻¹ ≤ K := by dsimp [K]; linarith
  have hg0 : ∀ x ∈ D, ∀ v, 0 ≤ g x v v := by
    intro x hx v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hp x (hDU hx) v hv).le
  obtain ⟨δ,hδ,hstable⟩ := weightedHessianValue_uniform_continuity g (sourceHessian g S) hD
    (hg.continuousOn.mono hDU) hcH hg0 K (half_pos hc)
  refine ⟨c/2,half_pos hc,?_⟩
  intro T
  obtain ⟨A,hA,hgrad⟩ := corrugation_actual_low_gradient g S χ hD hconv hU hDU hg hS hp hn
    hχ hcpt hχ0 hχ1 ha ha1 hL T
  obtain ⟨B,hB,hproj⟩ := corrugation_projected_direction_freezing g S χ hD hconv hU hDU hg hS hp hn
    hχ hcpt hχ0 hχ1 ha ha1 hL
  have hnv := corrugation_local_nonvanishing g S χ hD hconv hU hDU hg hS hp hn hχ hcpt amp hL
  have htA : Tendsto (fun k ↦ A*corrugationScale L k) atTop (𝓝 0) := by
    simpa using (corrugationScale_tendsto L).const_mul A
  have htB : Tendsto (fun k ↦ B*corrugationGradientRate L k) atTop (𝓝 0) := by
    simpa using (corrugationGradientRate_tendsto hL).const_mul B
  filter_upwards [hgrad,hproj,hnv,(corrugationScale_tendsto L).eventually_lt_const hδ,
    htA.eventually_lt_const hδ,htA.eventually_lt_const zero_lt_one,
    htB.eventually_lt_const hδ] with k hkgrad hkproj hknv hkR hkA hkA1 hkB
  intro y hy x hx hxy e he0 he hmax
  dsimp only
  intro hreg
  let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
  let u := e (Pi.single 1 1)
  let q := metricPerpProjection (g x) (metricNormalize (g x) p) u
  let t := metricNormalize (g x) q
  have hu : g y u u = 1 := by simpa [u] using he 1 1
  obtain ⟨hnq,htunit,htorth,htclose⟩ := hkproj y hy x hx hxy e he0 he u hu
    (corrugationLeadingVector_second_orthogonal (g y) e he amp _ _)
  have hd : ‖p-metricGradient g S y‖ ≤ A*corrugationScale L k := hkgrad y hy x hx hxy e he0 he hreg
  have hpbound : ‖p‖ ≤ K := by
    have htri : ‖p‖ ≤ ‖p-metricGradient g S y‖+‖metricGradient g S y‖ :=
      norm_le_norm_sub_add _ _
    exact (htri.trans (add_le_add (hd.trans hkA1.le) (hgp y hy))).trans (by linarith)
  have htbound : ‖t‖ ≤ K := (metric_unit_coordinate_bound (g x) ha0 (hmetric x hx).2 t htunit).trans hKt
  have hubound : ‖u‖ ≤ K := (metric_unit_coordinate_bound (g y) ha0 (hmetric y hy).2 u hu).trans hKt
  have hdiff := hstable x hx y hy p (metricGradient g S y) t u hpbound
    ((hgp y hy).trans (by linarith)) htbound hubound (hxy.trans_lt hkR)
    (hd.trans_lt hkA) (htclose.trans_lt hkB)
  have hold : c ≤ weightedHessianValue (g y) (sourceHessian g S y) (metricGradient g S y) u :=
    hmargin y hy u hmax
  have hnew : c/2 ≤ weightedHessianValue (g x) (sourceHessian g S x) p t := by
    have hh := (abs_lt.mp hdiff).1
    linarith
  rw [weightedHessianValue_normalized (g x) (sourceHessian g S x) p t
    (hp x (hDU hx) p (hknv y hy x hx hxy e he0 he))] at hnew
  exact ⟨hnq,htunit,htorth,hnew⟩

end
end Yau.Geometry

end OAI
