import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterUpdate
import OAI.Probability.CriticalPercolation.Clusters.Earlier
import OAI.Probability.CriticalPercolation.Clusters.HitValue
import OAI.Probability.CriticalPercolation.GraphGeometry.LastInverseDiagonal

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

omit [Fintype V] in
lemma hitting_eq_one_sub_avoidance (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (A : Set V) (s : V) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) s)) =
      1 - G.avoidedAverage w A s (fun _ => 1) := by
  conv_rhs => lhs; rw [← expect_const w hw 1]
  unfold avoidedAverage
  erw [← expect_sub]
  congr 1
  funext ω
  simp only [hitValue, component_inter_nonempty_iff]
  split_ifs <;> norm_num

lemma finite_joint_gluing_list {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin (n+1) → V) (hx : Function.Injective x)
    (T : Set V) (a : ℝ) (ha : ∀ j : Fin n, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) (x j.castSucc)))) :
    expect w (fun ω => hitValue (earlier x (Fin.last n))
        (component (G.openGraph ω) (x (Fin.last n)))) * a ≤
      expect w (fun ω => jointHitValue (earlier x (Fin.last n)) T
        (component (G.openGraph ω) (x (Fin.last n)))) := by
  rw [G.hitting_eq_one_sub_avoidance w hw]
  apply G.finite_cluster_relay w hw hpos hclosed x hx
    (jointHitValue_monotone _ _) (jointHitValue_nonneg _ _)
  intro j
  have he : (fun ω : E → Prop => jointHitValue (earlier x (Fin.last n)) T
      (component (G.openGraph ω) (x j.castSucc))) =
      (fun ω => hitValue T (component (G.openGraph ω) (x j.castSucc))) := by
    funext ω
    apply jointHitValue_eq_hitValue
    exact ⟨x j.castSucc, component_self _ _, ⟨j.castSucc, Fin.castSucc_lt_last j, rfl⟩⟩
  rw [he]
  exact ha j

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory

end
end

end OAI
