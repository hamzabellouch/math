import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.MemPairRank

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.AffineRealization
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K I ι J : Type*} [Field K] [Fintype I] [Fintype ι] [Fintype J]

theorem projective_line_pair_packing
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (W : J → Submodule K (I → K)) (hW : ∀ l, finrank K (W l) = 2)
    (hWinj : Function.Injective W) (M : ℕ)
    (hM : ∀ l, M ≤ (Finset.univ.filter (fun k => (p k).rep ∈ W l)).card) :
    Fintype.card J * (M * (M-1)) ≤ (Fintype.card ι)^2 := by
  classical
  let A (l : J) : Finset ι := Finset.univ.filter (fun k => (p k).rep ∈ W l)
  have hd : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint (fun l => (A l).offDiag) := by
    intro l hl m hm hlm
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨hi, hj, hij⟩ := Finset.mem_offDiag.mp hz
    obtain ⟨hi', hj', _⟩ := Finset.mem_offDiag.mp hz'
    apply hlm
    apply hWinj
    rw [← span_pair_eq_line p hp _ (hW l) hij (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hj).2,
      ← span_pair_eq_line p hp _ (hW m) hij (Finset.mem_filter.mp hi').2
        (Finset.mem_filter.mp hj').2]
  calc
    Fintype.card J * (M * (M-1)) = ∑ _l : J, M * (M-1) := by simp
    _ ≤ ∑ l : J, (A l).offDiag.card := by
      apply Finset.sum_le_sum
      intro l hl
      rw [Finset.offDiag_card]
      have he (n : ℕ) : n*n-n = n*(n-1) := by rw [Nat.mul_sub_left_distrib, mul_one]
      rw [he]
      exact Nat.mul_le_mul (hM l) (Nat.sub_le_sub_right (hM l) 1)
    _ = (Finset.univ.biUnion (fun l => (A l).offDiag)).card := (Finset.card_biUnion hd).symm
    _ ≤ Fintype.card (ι × ι) := Finset.card_le_univ _
    _ = (Fintype.card ι)^2 := by simp [pow_two]
end SharpRamseyFive.AffineRealization

end OAI
