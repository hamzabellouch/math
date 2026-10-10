import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open Finset
variable {V : Type*} [Fintype V]

/-- The side of an oriented tree edge towards its second endpoint. -/
def treeBranch (G : SimpleGraph V) (v w : V) : Finset V :=
  Finset.univ.filter (fun x => G.dist x w < G.dist x v)

/-- A finite weighted tree has a centroid: each branch at the selected vertex
has at most half the total weight. This is a genuine weighted-tree theorem,
not a planar-separator assumption. -/
theorem weighted_tree_centroid (G : SimpleGraph V) (hG : G.IsTree) (weight : V → ℝ) :
    ∃ v : V, ∀ w : V, G.Adj v w →
      2 * ∑ x ∈ treeBranch G v w, weight x ≤ ∑ x : V, weight x := by
  let potential : V → ℝ := fun v => ∑ x : V, weight x * G.dist x v
  have : Nonempty V := hG.connected.nonempty
  obtain ⟨v, _, hmin⟩ := Finset.exists_min_image Finset.univ potential Finset.univ_nonempty
  refine ⟨v,?_⟩
  intro w hadj
  have hid : potential w + 2 * ∑ x ∈ treeBranch G v w, weight x =
      potential v + ∑ x : V, weight x := by
    unfold potential treeBranch
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases hG.dist_eq_dist_add_one_of_adj x hadj with h | h
    · have hx : G.dist x w < G.dist x v := by omega
      rw [ite_eq_left hx,h,Nat.cast_add,Nat.cast_one]
      ring
    · have hx : ¬G.dist x w < G.dist x v := by omega
      rw [ite_eq_right hx,h,Nat.cast_add,Nat.cast_one]
      ring
  have hle := hmin w (Finset.mem_univ w)
  linarith

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
