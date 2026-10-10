import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Order.Zorn
import Mathlib.Tactic

namespace OAI

/-! # The locally finite unit net used for Lipschitz replacement -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- A maximal unit-separated set covers the whole metric space by closed
unit balls. No measure or geometric input is required for this step. -/
theorem exists_unit_separated_net :
    ∃ V : Set X, V.Pairwise (fun x y => 1 < dist x y) ∧
      ∀ x : X, ∃ v ∈ V, dist x v ≤ 1 := by
  classical
  obtain ⟨V, hV⟩ := zorn_subset {V : Set X | V.Pairwise (fun x y => 1 < dist x y)}
    (by
      intro C hC hc
      exact ⟨⋃₀ C, hc.pairwise_sUnion.mpr (fun s hs => hC hs), fun s hs => subset_sUnion_of_mem hs⟩)
  refine ⟨V, hV.1, ?_⟩
  intro x
  by_contra hn
  have hfar : ∀ v ∈ V, 1 < dist x v := by
    intro v hv
    exact lt_of_not_ge (fun h => hn ⟨v, hv, h⟩)
  have hi : (insert x V).Pairwise (fun y z => 1 < dist y z) := by
    rw [Set.pairwise_insert]
    exact ⟨hV.1, fun y hy _ => ⟨hfar y hy, by simpa only [dist_comm] using hfar y hy⟩⟩
  have hx : x ∈ V := hV.2 hi (subset_insert x V) (mem_insert x V)
  exact hn ⟨x, hx, by simp⟩

/-- Compact sets contain only finitely many points of a unit-separated set. -/
theorem finite_separated_subset_of_compact {V K : Set X}
    (hV : V.Pairwise (fun x y => 1 < dist x y)) (hK : IsCompact K) (hVK : V ⊆ K) :
    V.Finite := by
  classical
  obtain ⟨C, hC, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (1 / 3 : ℝ) (by norm_num)
  have hc (x : V) : ∃ c : C, dist (x : X) c < 1 / 3 := by
    have h := hcover (hVK x.property)
    rcases mem_iUnion.mp h with ⟨c, h⟩
    rcases mem_iUnion.mp h with ⟨hc, h⟩
    exact ⟨⟨c, hc⟩, mem_ball.mp h⟩
  choose c hc using hc
  have hinj : Function.Injective c := by
    intro x y he
    apply Subtype.ext
    by_contra hne
    have hsep := hV x.property y.property hne
    have htri := dist_triangle (x : X) (c x : X) y
    have hx := hc x
    have hy := hc y
    rw [← he] at hy
    rw [dist_comm (c x : X) y] at htri
    linarith
  let : Finite C := hC.to_subtype
  let : Finite V := Finite.of_injective c hinj
  exact Set.toFinite V

/-- Every bounded part of the net is finite, giving the local finiteness
needed to glue the cutoff partitions. -/
theorem finite_unit_net_ball [ProperSpace X] {V : Set X}
    (hV : V.Pairwise (fun x y => 1 < dist x y)) (x : X) (R : ℝ) :
    (V ∩ Metric.closedBall x R).Finite :=
  finite_separated_subset_of_compact (hV.mono inter_subset_left)
    (isCompact_closedBall x R) inter_subset_right

end PolycyclicRecognition

end

end OAI
