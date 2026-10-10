import Mathlib
import OAI.Geometry.WeakMTW.Model

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff Manifold ENNReal
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

include n
omit [CompactSpace M] in
 theorem exists_approx_distance_split (x y : M) {r ε : ℝ}
    (hr : r ∈ Icc (0 : ℝ) (dist x y)) (hε : 0 < ε) :
    ∃ z : M, dist x z = r ∧ r + dist z y < dist x y + ε := by
  have hpos : 0 < dist x y + ε := add_pos_of_nonneg_of_pos dist_nonneg hε
  have hh : riemannianEDist (model n) x y < ENNReal.ofReal (dist x y + ε) := by
    rw [← IsRiemannianManifold.out, edist_dist, ENNReal.ofReal_lt_ofReal_iff hpos]
    linarith
  obtain ⟨γ,h0,h1,hγ,hlen,_⟩ := exists_lt_locally_constant_of_riemannianEDist_lt hh zero_lt_one
  have hc : ContinuousOn (fun t => dist x (γ t)) (Icc (0 : ℝ) 1) :=
    (continuous_const.dist hγ.continuous).continuousOn
  have hr' : r ∈ Icc (dist x (γ 0)) (dist x (γ 1)) := by simpa [h0,h1] using hr
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc zero_le_one hc hr'
  change dist x (γ t) = r at he
  refine ⟨γ t, he, ?_⟩
  have hp := riemannianEDist_le_pathELength (hγ.contMDiffOn :
    ContMDiffOn 𝓘(ℝ, ℝ) (model n) 1 γ (Icc (0 : ℝ) t)) h0 rfl ht.1
  have hq := riemannianEDist_le_pathELength (hγ.contMDiffOn :
    ContMDiffOn 𝓘(ℝ, ℝ) (model n) 1 γ (Icc t 1)) rfl h1 ht.2
  rw [← IsRiemannianManifold.out, edist_dist, he] at hp
  rw [← IsRiemannianManifold.out, edist_dist] at hq
  have hb := (add_le_add hp hq).trans_lt (by
    rw [pathELength_add ht.1 ht.2]
    exact hlen)
  rw [← ENNReal.ofReal_add hr.1 dist_nonneg, ENNReal.ofReal_lt_ofReal_iff hpos] at hb
  exact hb

 theorem exists_distance_split (x y : M) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) (dist x y)) :
    ∃ z : M, dist x z = r ∧ dist z y = dist x y - r := by
  obtain ⟨w,hw,_⟩ := exists_approx_distance_split (n := n) x y hr (ε := 1) zero_lt_one
  have hne : (Metric.sphere x r).Nonempty := ⟨w, by simpa [Metric.mem_sphere,dist_comm] using hw⟩
  obtain ⟨z,hz,hmin⟩ := (isCompact_sphere x r).exists_isMinOn hne (continuous_id.dist continuous_const).continuousOn
  have hz' : dist x z = r := by simpa [Metric.mem_sphere,dist_comm] using hz
  refine ⟨z,hz',?_⟩
  have hlo : dist x y - r ≤ dist z y := by
    have ht := dist_triangle x z y
    rw [hz'] at ht
    linarith
  apply le_antisymm ?_ hlo
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨w,hw,hw'⟩ := exists_approx_distance_split (n := n) x y hr hε
  have hle : dist z y ≤ dist w y := hmin (by simpa [Metric.mem_sphere,dist_comm] using hw)
  linarith

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
