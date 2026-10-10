import OAI.Geometry.NodalSets.Charts.CompactFrameCover
import OAI.Geometry.NodalSets.Elliptic.CorrugationOldData
import OAI.Geometry.NodalSets.Elliptic.UniformTripleBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma maximizing_margin_from_eta (g H : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (p q v : Coord) (hp : 0 < g p p) (hq : g q q = g p p+4) (hpq : g p q = 0)
    {c : ℝ} (hc : 0 < c) (heta : c ≤ sourceDirectionEta g H p q)
    (hmax : ∀ u, g u u = 1 → g p u = 0 → H u u ≤ H v v) :
    c ≤ H p p/(g p p+4)+H v v := by
  have hqpos : 0 < g q q := by linarith
  have hd : 0 < g p p+g q q := by linarith
  have he := (le_div_iff₀ hd).mp heta
  have hmax' := hmax (metricNormalize g q) (metricNormalize_unit g q hqpos)
    (metricNormalize_orthogonal g p q hpq)
  have hsqrt := Real.sq_sqrt hqpos.le
  have hsqrt0 : Real.sqrt (g q q) ≠ 0 := (Real.sqrt_pos.mpr hqpos).ne'
  have hscale : (g q q)*H (metricNormalize g q) (metricNormalize g q) = H q q := by
    simp only [metricNormalize,map_smul,smul_apply,smul_eq_mul]
    field_simp
    rw [hsqrt]
  have hineq := mul_le_mul_of_nonneg_left hmax' hqpos.le
  rw [hscale,hq] at hineq
  rw [hq] at he
  have hden : 0 < g p p+4 := by linarith
  have hmain : c*(g p p+4) ≤ H p p+(g p p+4)*H v v := by nlinarith
  calc
    c ≤ (H p p+(g p p+4)*H v v)/(g p p+4) := (le_div_iff₀ hden).mpr hmain
    _ = H p p/(g p p+4)+H v v := by field_simp

theorem compact_maximizing_margin {T : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (g H : T → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : Continuous g) (hH : Continuous H)
    (hsym : ∀ t u v, g t u v = g t v u)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (hdir : ∀ t, ∃ v, g t (p t) v = 0 ∧ g t v v = 1 ∧
      0 < H t (p t) (p t)+(g t (p t) (p t)+4)*H t v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ t v,
      (∀ u, g t u u = 1 → g t (p t) u = 0 → H t u u ≤ H t v v) →
      c ≤ H t (p t) (p t)/(g t (p t) (p t)+4)+H t v v := by
  obtain ⟨d⟩ := exists_compact_frame_cover g H hg hH hsym hpos p hp hp0 hdir
  obtain ⟨c,hc,C,hC,hbound⟩ := uniform_direction_strictness (g ∘ d.center) (H ∘ d.center)
    (hg.comp d.continuous_center) (hH.comp d.continuous_center) (fun z ↦ hpos (d.center z))
    (p ∘ d.center) (hp.comp d.continuous_center) (fun z ↦ hp0 (d.center z)) d.triple
  refine ⟨c,hc,?_⟩
  intro t v hmax
  obtain ⟨z,hz⟩ := d.surjective_center t
  have h := maximizing_margin_from_eta (g (d.center z)) (H (d.center z))
    (p (d.center z)) (d.triple.q z 0) v (hpos _ _ (hp0 _)) (d.triple.length z 0)
    (d.triple.perpendicular z 0) hc (hbound z 0).1 (by simpa [hz] using hmax)
  simpa [hz] using h

theorem corrugation_old_uniform_margin
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ D, ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ D, metricGradient g S y ≠ 0 ∧
      ∃ q : Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ D, ∀ v,
      (∀ u, g y u u = 1 → g y (metricGradient g S y) u = 0 →
        sourceHessian g S y u u ≤ sourceHessian g S y v v) →
      c ≤ sourceHessian g S y (metricGradient g S y) (metricGradient g S y)/
        (g y (metricGradient g S y) (metricGradient g S y)+4)+sourceHessian g S y v v := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
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
  obtain ⟨c,hc,hbound⟩ := compact_maximizing_margin (fun y : D ↦ g y) (fun y : D ↦ sourceHessian g S y)
    (hg.continuousOn.mono hDU).domRestrict hcH.domRestrict (fun y ↦ hsym y y.property)
    (fun y ↦ hp y (hDU y.property)) (fun y : D ↦ metricGradient g S y) hcP.domRestrict
    (fun y ↦ (hadm y y.property).1) (fun y ↦ by
      obtain ⟨q,hq,hpq,hstr⟩ := (hadm y y.property).2
      exact ⟨q,hpq,hq,hstr⟩)
  exact ⟨c,hc,fun y hy ↦ hbound ⟨y,hy⟩⟩

end
end Yau.Geometry

end OAI
