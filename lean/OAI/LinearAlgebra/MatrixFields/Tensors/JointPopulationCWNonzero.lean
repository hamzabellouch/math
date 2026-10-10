import Mathlib
import OAI.LinearAlgebra.MatrixFields.Tensors.CWCompleteStatistics

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationCWNonzero

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open CWStrands InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [Field F]

omit [DecidableEq H] in
theorem class_half_products_nonzero
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ) (hleft : ∀ h, leftLength h ≤ 8)
    (hsupp : ∀ h u, 0 < counts h u → ∀ s, shapeNat u s ≤ parentShape h s)
    (e : Target counts)
    (x y z : RawPairs counts (Left leftLength) (Right rightLength))
    (hsource : sourceTensor counts (Left leftLength) (Right rightLength)
      (parentTensor (F := F) leftLength rightLength parentShape) x y z ≠ 0)
    (hx : coarseMask counts (Left leftLength) (Right rightLength)
      (coarse leftLength rightLength hleft) 0 e x)
    (hy : coarseMask counts (Left leftLength) (Right rightLength)
      (coarse leftLength rightLength hleft) 1 e y)
    (hz : coarseMask counts (Left leftLength) (Right rightLength)
      (coarse leftLength rightLength hleft) 2 e z)
    (h : H) (u : Shape) (hn : 0 < counts h u) :
    (∏ i : Class counts e h u,
      shapeTensor (F := F) (Fin (leftLength h)) (shapeNat u)
        (x h i.val).1 (y h i.val).1 (z h i.val).1) ≠ 0 ∧
    (∏ i : Class counts e h u,
      shapeTensor (F := F) (Fin (rightLength h)) (parentShape h - shapeNat u)
        (x h i.val).2 (y h i.val).2 (z h i.val).2) ≠ 0 := by
  change (∏ h' : H, ∏ i : Positions counts h',
    parentTensor (F := F) leftLength rightLength parentShape h'
      (x h' i) (y h' i) (z h' i)) ≠ 0 at hsource
  have hparent (i : Positions counts h) :
      parentTensor (F := F) leftLength rightLength parentShape h
        (x h i) (y h i) (z h i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp
      (Finset.prod_ne_zero_iff.mp hsource h (Finset.mem_univ h)) i (Finset.mem_univ i)
  have hhalves (i : Class counts e h u) :
      shapeTensor (F := F) (Fin (leftLength h)) (shapeNat u)
          (x h i.val).1 (y h i.val).1 (z h i.val).1 *
        shapeTensor (F := F) (Fin (rightLength h)) (parentShape h - shapeNat u)
          (x h i.val).2 (y h i.val).2 (z h i.val).2 ≠ 0 := by
    have hx' : coarse leftLength rightLength hleft 0 h (x h i.val) = u.1 := by
      simpa [shapeSide, i.property] using hx h i.val
    have hy' : coarse leftLength rightLength hleft 1 h (y h i.val) = u.2.1 := by
      simpa [shapeSide, i.property] using hy h i.val
    have hz' : coarse leftLength rightLength hleft 2 h (z h i.val) = u.2.2 := by
      simpa [shapeSide, i.property] using hz h i.val
    have hblock : block (Left leftLength) (Right rightLength)
        (parentTensor (F := F) leftLength rightLength parentShape)
        (coarse leftLength rightLength hleft) (h, u)
        (x h i.val) (y h i.val) (z h i.val) ≠ 0 := by
      simpa [block, hx', hy', hz'] using hparent i.val
    rw [block_eq_product leftLength rightLength parentShape hleft h u
      (hsupp h u hn)] at hblock
    exact hblock
  constructor
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (mul_ne_zero_iff.mp (hhalves i)).1
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (mul_ne_zero_iff.mp (hhalves i)).2

end MatrixMultiplication.JointPopulationCWNonzero

end
end

end MatrixAllFields

end OAI
