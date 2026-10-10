import OAI.Geometry.NodalSets.Charts.CorrugationFrozenFrame

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma metric_unit_coordinate_bound (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (hg : ∀ v : Coord, c*‖v‖^2 ≤ g v v)
    (v : Coord) (hv : g v v = 1) : ‖v‖ ≤ 1+c⁻¹ := by
  have h := hg v
  rw [hv] at h
  have hi := mul_inv_cancel₀ hc.ne'
  nlinarith [sq_nonneg (‖v‖-1),norm_nonneg v,inv_pos.mpr hc]

lemma frozenFrameCovector_norm_bound (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ v : Coord, c*‖v‖^2 ≤ g v v) (hupper : ‖g‖ ≤ M)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (i : Fin 4) : ‖frozenFrameCovector e i‖ ≤ M*(1+c⁻¹) := by
  have heq : frozenFrameCovector e i = g (e (Pi.single i 1)) := by
    ext v
    exact frozenFrameCovector_metric g e he i v
  rw [heq]
  have hu : g (e (Pi.single i 1)) (e (Pi.single i 1)) = 1 := by simpa using he i i
  calc
    _ ≤ ‖g‖*‖e (Pi.single i 1)‖ := g.le_opNorm _
    _ ≤ M*(1+c⁻¹) := mul_le_mul hupper
      (metric_unit_coordinate_bound g hc hlower _ hu) (norm_nonneg _) hM

lemma frozenFrame_pair_norm_bound (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ v : Coord, c*‖v‖^2 ≤ g v v) (hupper : ‖g‖ ≤ M)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) :
    ‖(frozenFrameCovector e 2).prod (frozenFrameCovector e 3)‖ ≤ M*(1+c⁻¹) := by
  have h2 := frozenFrameCovector_norm_bound g hc hM hlower hupper e he 2
  have h3 := frozenFrameCovector_norm_bound g hc hM hlower hupper e he 3
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖(frozenFrameCovector e 2 v,frozenFrameCovector e 3 v)‖ ≤ _
  rw [Prod.norm_def]
  apply max_le
  · exact ((frozenFrameCovector e 2).le_opNorm v).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg v))
  · exact ((frozenFrameCovector e 3).le_opNorm v).trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg v))

end
end Yau.Geometry

end OAI
