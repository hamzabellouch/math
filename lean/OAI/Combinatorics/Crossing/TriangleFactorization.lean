import OAI.Combinatorics.Crossing.HalfOrderReduction
import OAI.Combinatorics.Crossing.WeightedGram

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def triangleDiagonalWeight (s : ℕ) (node : OrderedNode s → ℝ) (j : BiExponent s) : ℝ :=
  let pq := triangleNodePair s (triangleCoordEquiv s j)
  triangleCoefficient s pq.1 pq.2 * detectorWeight node pq.1 pq.2

theorem triangleDiagonalWeight_ne_zero (s : ℕ) (node : OrderedNode s → ℝ)
    (hn : Function.Injective node) (j : BiExponent s) : triangleDiagonalWeight s node j ≠ 0 := by
  let pq := triangleNodePair s (triangleCoordEquiv s j)
  have hmem : (pq.1.val,pq.2.val) ∈ twoTriangle s := (triangleCoordEquiv s j).property
  have hpq : pq.1 ≠ pq.2 := by
    intro he
    have hv := congrArg Subtype.val he
    rw [mem_twoTriangle] at hmem
    omega
  exact mul_ne_zero ((triangleCoefficient_ne_zero_iff s pq.1 pq.2).mpr hmem)
    (detectorWeight_ne_zero node hn hpq)

theorem rankDetector_triangle_sum (s : ℕ) (node : OrderedNode s → ℝ) :
    rankDetector s node (fun p q => triangleCoefficient s p q) =
      ∑ j : BiExponent s,
        let pq := triangleNodePair s (triangleCoordEquiv s j)
        triangleCoefficient s pq.1 pq.2 • detectorAtom s node pq.1 pq.2 := by
  let f := fun pq : OrderedNode s × OrderedNode s =>
    triangleCoefficient s pq.1 pq.2 • detectorAtom s node pq.1 pq.2
  have hfull : rankDetector s node (fun p q => triangleCoefficient s p q) = ∑ pq, f pq :=
    (Fintype.sum_prod_type f).symm
  have hfilter : (∑ pq ∈ orderedTriangle s, f pq) = ∑ pq, f pq := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro pq hpq hnot
    have hm : (pq.1.val,pq.2.val) ∉ twoTriangle s := by simpa [orderedTriangle] using hnot
    have hz : triangleCoefficient s pq.1 pq.2 = 0 :=
      not_ne_iff.mp (mt (triangleCoefficient_ne_zero_iff s pq.1 pq.2).mp hm)
    simp only [f, hz, zero_smul]
  rw [hfull, ← hfilter, ← Finset.sum_coe_sort]
  exact ((triangleCoordEquiv s).trans (triangleNodeEquiv s)).sum_comp
    (fun pq : ↥(orderedTriangle s) => f pq.val) |>.symm

theorem rankDetector_triangle_factorization (s : ℕ) (node : OrderedNode s → ℝ) :
    rankDetector s node (fun p q => triangleCoefficient s p q) =
      triangleMatrix s (extendOrderedNode s node) * Matrix.diagonal (triangleDiagonalWeight s node) *
        (triangleMatrix s (extendOrderedNode s node)).transpose := by
  rw [rankDetector_triangle_sum, weightedGram_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [triangleDiagonalWeight, detectorAtom, smul_smul]
  congr 2
  · funext ab
    exact (triangleMatrix_ordered_entry s node ab j).symm
  · funext ab
    exact (triangleMatrix_ordered_entry s node ab j).symm

theorem rankDetector_ordered_isUnit (s : ℕ) (node : OrderedNode s → ℝ)
    (hn : Function.Injective node) :
    IsUnit (rankDetector s node (halfOrderMatrix (OrderedNode s))) := by
  rw [rankDetector_halfOrder_reduction s node hn]
  apply IsUnit.neg
  change IsUnit (rankDetector s node (fun p q => triangleCoefficient s p q))
  rw [rankDetector_triangle_factorization]
  exact weightedGram_isUnit _ _
    (triangleMatrix_isUnit s (extendOrderedNode s node) (extendOrderedNode_injOn s node hn))
    (triangleDiagonalWeight_ne_zero s node hn)

end Zarankiewicz

end

end OAI
