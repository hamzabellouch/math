import OAI.Geometry.NodalSets.Charts.MetricNormalizationStabilityLemmas
import OAI.Geometry.NodalSets.Elliptic.CorrugationOldData

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma metricGradient_contDiffAt_local
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ) (x : Coord)
    (hg : ContDiffAt ℝ ∞ g x) (hS : ContDiffAt ℝ ∞ S x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) :
    ContDiffAt ℝ ∞ (metricGradient g S) x := by
  have hi : ContDiffAt ℝ ∞
      (ContinuousLinearMap.inverse : (Coord →L[ℝ] Coord →L[ℝ] ℝ) → ((Coord →L[ℝ] ℝ) →L[ℝ] Coord)) (g x) := by
    convert contDiffAt_map_inverse (n := ∞) (positiveMetricEquiv (g x) hp) using 1
    rfl
  exact (hi.comp x hg).clm_apply (hS.fderiv_right (m := ∞) (by simp))

theorem corrugation_old_speed_freezing
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ y ∈ D,
      |corrugationOldSlope g S x-corrugationOldSlope g S y| ≤
        corrugationOldSlope g S y*C*‖x-y‖ := by
  obtain ⟨m,hm,B,hB,hs⟩ := corrugationOldSlope_compact_bounds g S hD hU hDU hg hS hp hn
  have hgrad : ContDiffOn ℝ ∞ (metricGradient g S) U := by
    intro x hx
    exact (metricGradient_contDiffAt_local g S x (hg.contDiffAt (hU.mem_nhds hx))
      (hS.contDiffAt (hU.mem_nhds hx)) (hp x hx)).contDiffWithinAt
  have hsq : ContDiffOn ℝ ∞ (fun x ↦ g x (metricGradient g S x) (metricGradient g S x)) U :=
    (hg.clm_apply hgrad).clm_apply hgrad
  obtain ⟨A,hA,hfreeze⟩ := smooth_compact_freezing _ hD hconv hU hDU hsq
  refine ⟨A/m^2,by positivity,?_⟩
  intro x hx y hy
  have hxp := hp x (hDU hx) _ (hn x hx)
  have hyp := hp y (hDU hy) _ (hn y hy)
  have hsy : m^2 ≤ g y (metricGradient g S y) (metricGradient g S y) := by
    have hh := Real.sq_sqrt hyp.le
    have hh' := (hs y hy).1
    change m ≤ Real.sqrt _ at hh'
    nlinarith
  have hh := sqrt_difference_bound_of_reference hxp.le hm hsy (hfreeze x hx y hy)
  change |corrugationOldSlope g S x-corrugationOldSlope g S y| ≤ _ at hh
  have hmul := mul_le_mul_of_nonneg_right (hs y hy).1
    (show 0 ≤ (A/m^2)*‖x-y‖ by positivity)
  calc
    _ ≤ (A*‖x-y‖)/m := hh
    _ = m*((A/m^2)*‖x-y‖) := by field_simp
    _ ≤ corrugationOldSlope g S y*((A/m^2)*‖x-y‖) := hmul
    _ = _ := by ring

end
end Yau.Geometry

end OAI
