import OAI.Geometry.NodalSets.Charts.AdaptedNormalChart
import OAI.Geometry.NodalSets.Charts.ChartedEnvelope
import OAI.Geometry.NodalSets.Elliptic.PositiveBilinearBound

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
noncomputable section

lemma metric_perpendicular_unit_compact
    (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v : Coord, v ≠ 0 → 0 < g v v) (p : Coord) :
    IsCompact {v : Coord | g v v = 1 ∧ g p v = 0} := by
  obtain ⟨c,hc,hbound⟩ := positive_bilinear_coercive g hp
  have hclosed : IsClosed {v : Coord | g v v = 1 ∧ g p v = 0} :=
    (isClosed_eq (g.continuous.clm_apply continuous_id) continuous_const).inter
      (isClosed_eq (g p).continuous continuous_const)
  apply (isCompact_closedBall (0:Coord) (1+c⁻¹)).of_isClosed_subset hclosed
  intro v hv
  rw [mem_closedBall,dist_zero_right]
  have hb := hbound v
  rw [hv.1] at hb
  have hi : c*c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  nlinarith [sq_nonneg (‖v‖-1),norm_nonneg v,inv_pos.mpr hc]

lemma exists_maximizing_perpendicular_axis
    (g H : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v : Coord, v ≠ 0 → 0 < g v v) (p q₀ : Coord)
    (hq₀ : g q₀ q₀ = 1) (hpq₀ : g p q₀ = 0) :
    ∃ q : Coord, g q q = 1 ∧ g p q = 0 ∧
      ∀ v : Coord, g v v = 1 → g p v = 0 → H v v ≤ H q q := by
  obtain ⟨q,hq,hmax⟩ := (metric_perpendicular_unit_compact g hp p).exists_isMaxOn
    ⟨q₀,hq₀,hpq₀⟩ (H.continuous.clm_apply continuous_id).continuousOn
  exact ⟨q,hq.1,hq.2,fun v hv hvp ↦ hmax ⟨hv,hvp⟩⟩

def frozenFrameCovector (e : Coord ≃L[ℝ] Coord) (i : Fin 4) : Coord →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp e.symm.toContinuousLinearMap

lemma frozenFrameCovector_apply (e : Coord ≃L[ℝ] Coord) (i : Fin 4) (v : Coord) :
    frozenFrameCovector e i v = e.symm v i := rfl

lemma frozenFrameCovector_axis (e : Coord ≃L[ℝ] Coord) (i j : Fin 4) :
    frozenFrameCovector e i (e (Pi.single j 1)) = if i=j then 1 else 0 := by
  simp [frozenFrameCovector,Pi.single_apply]

lemma frozenFrameCovector_metric (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (i : Fin 4) (v : Coord) :
    frozenFrameCovector e i v = g (e (Pi.single i 1)) v := by
  rw [frozenFrameCovector_apply,← orthonormal_frame_pair g e he i (e.symm v)]
  simp

theorem exists_corrugation_frozen_frame
    (g H : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v : Coord, v ≠ 0 → 0 < g v v) (hs : ∀ u v, g u v = g v u)
    (p q₀ : Coord) (hp₀ : p ≠ 0) (hq₀ : g q₀ q₀ = 1) (hpq₀ : g p q₀ = 0) :
    ∃ (q : Coord) (e : Coord ≃L[ℝ] Coord),
      g q q = 1 ∧ g p q = 0 ∧
      (∀ v : Coord, g v v = 1 → g p v = 0 → H v v ≤ H q q) ∧
      e (Pi.single 0 1) = (Real.sqrt (g p p))⁻¹ • p ∧
      e (Pi.single 1 1) = q ∧
      (∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) ∧
      frozenFrameCovector e 2 p = 0 ∧ frozenFrameCovector e 3 p = 0 ∧
      frozenFrameCovector e 2 q = 0 ∧ frozenFrameCovector e 3 q = 0 := by
  obtain ⟨q,hqq,hpq,hm⟩ := exists_maximizing_perpendicular_axis g H hp p q₀ hq₀ hpq₀
  have hp' := hp p hp₀
  obtain ⟨e,he0,he1,he⟩ := positive_coordinate_adapted_frame g hp hs p q
    (Real.sqrt (g p p)) 1 (Real.sqrt_pos.mpr hp') (by norm_num)
    (Real.sq_sqrt hp'.le).symm (by simpa using hqq) hpq
  have he1' : e (Pi.single 1 1) = q := by simpa using he1
  have hep : p = Real.sqrt (g p p) • e (Pi.single 0 1) := by
    rw [he0,smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr hp').ne',one_smul]
  refine ⟨q,e,hqq,hpq,hm,he0,he1',he,?_,?_,?_,?_⟩
  · rw [hep,map_smul,frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  · rw [hep,map_smul,frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  · rw [← he1',frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  · rw [← he1',frozenFrameCovector_axis]; norm_num [Fin.ext_iff]

end
end Yau.Geometry

end OAI
