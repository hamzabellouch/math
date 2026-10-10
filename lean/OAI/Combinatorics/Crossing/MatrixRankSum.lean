import OAI.Combinatorics.Crossing.SubspaceIntersection
import OAI.Combinatorics.Crossing.MatrixGraphs
import OAI.Combinatorics.Crossing.FloorArithmetic

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
open scoped BigOperators

def offDiagonalRankSum (m d : ℕ)
    (X Y : Fin m → Matrix (Fin d) (Fin d) ℝ) : ℕ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, (X i-Y j).rank

theorem matrix_rank_sum_bound (m d : ℕ)
    (X Y : Fin m → Matrix (Fin d) (Fin d) ℝ)
    (hdiag : ∀ i, IsUnit (X i-Y i)) :
    2 * axisPairs m * d ≤ offDiagonalRankSum m d X Y := by
  let U := fun i => (X i).mulVecLin.graph
  let V := fun i => (Y i).mulVecLin.graph
  have hUV : ∀ i, Disjoint (U i) (V i) := fun i => matrix_graph_disjoint d (X i) (Y i) (hdiag i)
  have hsub := subspace_intersection_bound m U V hUV
  have hdim : finrank ℝ ((Fin d → ℝ) × (Fin d → ℝ)) = 2*d := by
    simp [Module.finrank_prod, two_mul]
  rw [hdim] at hsub
  have htotal : (∑ i, ∑ j, finrank ℝ ↥(U i ⊓ V j)) +
      (∑ i, ∑ j, (X i-Y j).rank) = m*m*d := by
    dsimp only [U, V]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, matrix_graph_finrank_add_rank]
    simp [Nat.mul_assoc]
  have hremove : offDiagonalRankSum m d X Y + m*d = ∑ i, ∑ j, (X i-Y j).rank := by
    have hdiagrank : ∀ i, (X i-Y i).rank = d := by
      intro i
      simpa using Matrix.rank_of_isUnit (X i-Y i) (hdiag i)
    unfold offDiagonalRankSum
    have hm : m*d = ∑ i : Fin m, d := by simp
    rw [hm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [hdiagrank i] using
      Finset.sum_erase_add Finset.univ (fun j => (X i-Y j).rank) (Finset.mem_univ i)
  have hfloor := congrArg (fun a : ℕ => a*d) (diagonal_floor_identity m)
  nlinarith

end Zarankiewicz

end

end OAI
