import Mathlib.Analysis.Normed.Module.FiniteDimension
import OAI.Geometry.NodalSets.Elliptic.UniformContact

namespace OAI

namespace Yau.Geometry
open Set Bornology Yau.Jets
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma positive_bilinear_coercive (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) :
    ∃ c > 0, ∀ v, c * ‖v‖^2 ≤ g v v := by
  obtain ⟨c,hc,_,_,hb⟩ := compact_positive_bounds
    (isCompact_sphere (0:E) 1) (fun v ↦ g v v)
    ((g.continuous.clm_apply continuous_id).continuousOn)
    (fun v hv ↦ hp v (by intro he; simp [he] at hv))
  refine ⟨c,hc,fun v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have hh := (hb ((‖v‖⁻¹:ℝ) • v) (by simpa using hu)).1
  simp only [map_smul,smul_apply,smul_eq_mul] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
  have he : ‖v‖^2*(‖v‖⁻¹*(‖v‖⁻¹*g v v)) = g v v := by field_simp
  rw [he] at hmul
  nlinarith

lemma positive_bilinear_bounded (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) :
    IsVonNBounded ℝ {v | g v v < 1} := by
  obtain ⟨c,hc,hb⟩ := positive_bilinear_coercive g hp
  apply (NormedSpace.isVonNBounded_iff ℝ).mpr
  apply (Metric.isBounded_closedBall (x := (0:E)) (r := 1+c⁻¹)).subset
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  have hh := hb v
  have hi : c*c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  have hp' : 0 < c⁻¹ := inv_pos.mpr hc
  dsimp at hv
  nlinarith [sq_nonneg (‖v‖-1),norm_nonneg v]

end
end Yau.Geometry

end OAI
