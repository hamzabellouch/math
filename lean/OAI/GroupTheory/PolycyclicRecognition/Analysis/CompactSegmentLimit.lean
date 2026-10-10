import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! # Compact limits of approximations to a minimizing segment -/

namespace PolycyclicRecognition

open Set Metric Filter
open scoped Topology

theorem exists_segment_of_compact_approximations {X : Type*} [MetricSpace X]
    [ProperSpace X] (x y : X)
    (f : ℕ → Icc (0 : ℝ) 1 → X) (err : ℕ → ℝ)
    (herr : Tendsto err atTop (𝓝 0))
    (hzero : ∀ n, f n ⟨0, by simp⟩ = x)
    (hone : ∀ n, f n ⟨1, by simp⟩ = y)
    (hball : ∀ n t, dist (f n t) x ≤ dist x y)
    (hpair : ∀ n s t, dist (f n s) (f n t) ≤ dist x y * |(s : ℝ) - t| + err n) :
    ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) ≤ dist x y * |s - t| := by
  let K : Set (Icc (0 : ℝ) 1 → X) := univ.pi (fun _ => closedBall x (dist x y))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall x (dist x y)
  have hfK : ∀ᶠ n in atTop, f n ∈ K := Eventually.of_forall fun n t _ => hball n t
  obtain ⟨g, _, hg⟩ := hK.exists_mapClusterPt (le_principal_iff.mpr hfK)
  have gzero : g ⟨0, by simp⟩ = x :=
    (isClosed_eq (continuous_apply _) continuous_const).mem_of_mapClusterPt hg
      (Eventually.of_forall hzero)
  have gone : g ⟨1, by simp⟩ = y :=
    (isClosed_eq (continuous_apply _) continuous_const).mem_of_mapClusterPt hg
      (Eventually.of_forall hone)
  have gpair (s t : Icc (0 : ℝ) 1) :
      dist (g s) (g t) ≤ dist x y * |(s : ℝ) - t| := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have he := herr.eventually (gt_mem_nhds hε)
    have hclosed : IsClosed {v : Icc (0 : ℝ) 1 → X |
        dist (v s) (v t) ≤ dist x y * |(s : ℝ) - t| + ε} :=
      isClosed_le ((continuous_apply s).dist (continuous_apply t)) continuous_const
    apply hclosed.mem_of_mapClusterPt hg
    filter_upwards [he] with n hn
    exact (hpair n s t).trans (add_le_add_right hn.le _)
  classical
  let γ : ℝ → X := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then g ⟨t, ht⟩ else x
  refine ⟨γ, ?_, ?_, ?_⟩
  · simpa only [γ, dite_eq_left (show (0 : ℝ) ∈ Icc 0 1 by simp)] using gzero
  · simpa only [γ, dite_eq_left (show (1 : ℝ) ∈ Icc 0 1 by simp)] using gone
  · intro s hs t ht
    simpa only [γ, dite_eq_left hs, dite_eq_left ht] using gpair ⟨s, hs⟩ ⟨t, ht⟩

end PolycyclicRecognition

end OAI
