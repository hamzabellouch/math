import OAI.Combinatorics.Crossing.RankDetector
import OAI.Combinatorics.Crossing.MatrixRankBounds
import Mathlib.Data.Matrix.Basis

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem detectorAtom_rank_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (node : ι → ℝ) (p q : ι) :
    (detectorAtom s node p q).rank ≤ 1 :=
  (matrix_rank_smul_le _ _).trans (Matrix.rank_vecMulVec_le _ _)

theorem detectorAtom_rank_one (s : ℕ) (hs : 0 < s) (node : ι → ℝ)
    (hn : Function.Injective node) {p q : ι} (hpq : p ≠ q) :
    (detectorAtom s node p q).rank = 1 := by
  have hw := detectorWeight_ne_zero node hn hpq
  have hne : detectorAtom s node p q ≠ 0 := by
    intro hz
    have he := congrArg (fun A : Matrix (BiExponent s) (BiExponent s) ℝ =>
      A (⟨0,hs⟩,⟨0,hs⟩) (⟨0,hs⟩,⟨0,hs⟩)) hz
    apply hw
    simpa [detectorAtom, detectorVector, Matrix.vecMulVec_apply] using he
  have hr0 := (matrix_rank_eq_zero_iff (detectorAtom s node p q)).not.mpr hne
  have hr1 := detectorAtom_rank_le_one s node p q
  omega

theorem rankDetector_single (s : ℕ) (node : ι → ℝ) (p q : ι) (c : ℝ) :
    rankDetector s node (Matrix.single p q c) = c • detectorAtom s node p q := by
  change (∑ i, ∑ j, Matrix.single p q c i j • detectorAtom s node i j) = _
  simp [Matrix.single_apply, ite_and]

theorem rankDetector_support_bound (s : ℕ) (node : ι → ℝ) (H : Matrix ι ι ℝ) :
    (rankDetector s node H).rank ≤
      (Finset.univ.filter (fun pq : ι × ι => pq.1 ≠ pq.2 ∧ H pq.1 pq.2 ≠ 0)).card := by
  let S := Finset.univ.filter (fun pq : ι × ι => pq.1 ≠ pq.2 ∧ H pq.1 pq.2 ≠ 0)
  have he : rankDetector s node H = ∑ pq ∈ S, H pq.1 pq.2 • detectorAtom s node pq.1 pq.2 := by
    change (∑ p, ∑ q, H p q • detectorAtom s node p q) = _
    rw [← Fintype.sum_prod_type (fun pq : ι × ι => H pq.1 pq.2 • detectorAtom s node pq.1 pq.2)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro pq hpq hnot
    have hnot' : ¬(pq.1 ≠ pq.2 ∧ H pq.1 pq.2 ≠ 0) := by simpa [S] using hnot
    by_cases heq : pq.1 = pq.2
    · simp [heq, detectorAtom_self]
    · have hz : H pq.1 pq.2 = 0 := by tauto
      rw [hz, zero_smul]
  rw [he]
  calc
    _ ≤ ∑ pq ∈ S, (H pq.1 pq.2 • detectorAtom s node pq.1 pq.2).rank := matrix_rank_sum_le S _
    _ ≤ ∑ _pq ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro pq hpq
      exact (matrix_rank_smul_le _ _).trans (detectorAtom_rank_le_one s node pq.1 pq.2)
    _ = _ := by simp [S]

end Zarankiewicz

end

end OAI
