import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.CoordinateGeometry

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem positive_metric_coercive {B : MetricTensor E}
    (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ v : E, κ * ‖v‖ ^ 2 ≤ B v v := by
  by_cases hs : Subsingleton E
  · let := hs
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  · let : Nontrivial E := not_subsingleton_iff_nontrivial.mp hs
    have hc : Continuous (fun v : E => B v v) :=
      (B.continuous.comp continuous_id).clm_apply continuous_id
    obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hc.continuousOn
    have hwn : ‖w‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hw
    have hw0 : w ≠ 0 := by intro h; simp [h] at hwn
    refine ⟨B w w, hB w hw0, ?_⟩
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · let u : E := ‖v‖⁻¹ • v
      have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hun : ‖u‖ = 1 := by
        simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
        exact inv_mul_cancel₀ hvn
      have hu : u ∈ Metric.sphere (0 : E) 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hun
      have hvu : ‖v‖ • u = v := by simp [u, smul_smul, hvn]
      have hminu := hmin hu
      have he : B v v = ‖v‖ ^ 2 * B u u := by
        conv_lhs => rw [← hvu]
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
      rw [he, mul_comm (B w w)]
      exact mul_le_mul_of_nonneg_left hminu (sq_nonneg _)

 theorem uniform_metric_coercive {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContinuousOn G S) {x : E} (hx : x ∈ S)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G x v v) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ S ∧
      ∀ y ∈ V, ∀ v : E, κ * ‖v‖ ^ 2 ≤ G y v v := by
  obtain ⟨m, hm, hbound⟩ := positive_metric_coercive hpos
  let V := S ∩ G ⁻¹' Metric.ball (G x) (m / 2)
  have hV : IsOpen V := hG.isOpen_inter_preimage hS Metric.isOpen_ball
  have hxV : x ∈ V := ⟨hx, Metric.mem_ball_self (half_pos hm)⟩
  refine ⟨m / 2, half_pos hm, V, hV, hxV, inter_subset_left, ?_⟩
  intro y hy v
  have hdiff : ‖G y - G x‖ < m / 2 := by
    have hh : dist (G y) (G x) < m / 2 := hy.2
    rwa [dist_eq_norm (G y) (G x)] at hh
  have hnorm : ‖(G y - G x) v v‖ ≤ ‖G y - G x‖ * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖(G y - G x) v‖ * ‖v‖ := ((G y - G x) v).le_opNorm v
      _ ≤ (‖G y - G x‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((G y - G x).le_opNorm v) (norm_nonneg _)
      _ = _ := by ring
  have hd : |G y v v - G x v v| ≤ m / 2 * ‖v‖ ^ 2 := by
    have h := hnorm.trans (mul_le_mul_of_nonneg_right hdiff.le (sq_nonneg ‖v‖))
    simpa only [sub_apply, Real.norm_eq_abs] using h
  have hlo := (abs_le.mp hd).1
  have hb := hbound v
  linarith

end
end CoordinateGeometry
end

end WeakMTWGlobalSupport

end OAI
