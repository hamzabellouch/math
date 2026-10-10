import OAI.Analysis.CircleDomains.Topology.SmallConnectedMetricSets
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Affine.AddTorsor

namespace OAI

/-! Finite metric chains give actual ambient paths arbitrarily close to a
connected set. These are the paths to be refined in the compact arc argument. -/
open Set Function Metric
open scoped unitInterval Topology
noncomputable section
namespace CircleDomainRigidity

lemma metric_chain_path_near_set
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {ε : ℝ} (hε : 0 < ε) {x y : S}
    (h : Relation.ReflTransGen (fun a b : S => dist (a : E) (b : E) < ε) x y) :
    ∃ γ : Path (x : E) (y : E), ∀ t, ∃ c ∈ S, dist (γ t) c < ε := by
  induction h with
  | refl =>
      refine ⟨Path.refl (x : E), fun t => ⟨x, x.property, ?_⟩⟩
      simpa using hε
  | @tail b c hprev hbc ih =>
      obtain ⟨γ, hγ⟩ := ih
      refine ⟨γ.trans (Path.segment (b : E) (c : E)), ?_⟩
      intro t
      have ht : γ.trans (Path.segment (b : E) (c : E)) t ∈
          range γ ∪ range (Path.segment (b : E) (c : E)) := by
        rw [← Path.trans_range]
        exact mem_range_self t
      rcases ht with ⟨u, hu⟩ | ⟨u, hu⟩
      · rw [← hu]
        exact hγ u
      · refine ⟨b, b.property, ?_⟩
        rw [← hu, Path.segment_apply, dist_lineMap_left, Real.norm_eq_abs,
          abs_of_nonneg u.property.1]
        exact (mul_le_mul_of_nonneg_right u.property.2 dist_nonneg).trans_lt (by simpa using hbc)

lemma connected_set_path_near
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : IsConnected S) {ε : ℝ} (hε : 0 < ε) {x y : E}
    (hx : x ∈ S) (hy : y ∈ S) :
    ∃ γ : Path x y, ∀ t, ∃ c ∈ S, dist (γ t) c < ε := by
  exact metric_chain_path_near_set hε (connected_set_metric_chain hS hε ⟨x, hx⟩ ⟨y, hy⟩)

end CircleDomainRigidity

end

end OAI
