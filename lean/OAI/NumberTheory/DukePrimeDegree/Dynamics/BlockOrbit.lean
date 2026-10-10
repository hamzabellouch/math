import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitRationality
import OAI.NumberTheory.PrimePackets.AtomMass

namespace OAI

/-!
# The standard block group and its finite-volume lattice orbits

The group here is defined by its concrete action on the coordinate
blocks. The split diagonals and all within-block root groups lie in it.
The preceding rationality argument then forces any nontrivial partition
with a finite-volume orbit through a generic prime-degree lattice to be
the universal partition.
-/

noncomputable section
open Matrix Module Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The determinant-one matrices commuting with every block-scalar
diagonal. This is the usual block-diagonal matrix subgroup. -/
def blockMatrixGroup {n : ℕ} (r : Setoid (Fin n)) : Subgroup (G n) where
  carrier := {g | ∀ c ∈ blockCoordinateAlgebra r,
    slMatrixConjugation g (Matrix.diagonal c) = Matrix.diagonal c}
  one_mem' := by
    intro c _
    exact slMatrixConjugation_one _
  mul_mem' := by
    intro g h hg hh c hc
    rw [slMatrixConjugation_mul, hg c hc, hh c hc]
  inv_mem' := by
    intro g hg c hc
    have he := slMatrixConjugation_mul g g⁻¹ (Matrix.diagonal c)
    rw [mul_inv_cancel, slMatrixConjugation_one, hg c hc] at he
    exact he.symm

lemma blockMatrixGroup_commute {n : ℕ} (r : Setoid (Fin n))
    (g : blockMatrixGroup r) (c : Fin n → ℝ) (hc : c ∈ blockCoordinateAlgebra r) :
    Commute (Matrix.diagonal c) g.val.val := by
  have he := congrArg (fun M => g.val.val * M) (g.property c hc)
  have hg : g.val.val * g.val⁻¹.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  change Matrix.diagonal c * g.val.val = g.val.val * Matrix.diagonal c
  simpa only [slMatrixConjugation, ← mul_assoc, hg, one_mul] using he

lemma diagonalOneParameter_mem_blockMatrixGroup {n : ℕ}
    (r : Setoid (Fin n)) (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ) :
    diagonalOneParameter ell hell t ∈ blockMatrixGroup r := by
  intro c _
  apply slMatrixConjugation_eq_self
  exact Matrix.commute_diagonal _ _

lemma transvection_mem_blockMatrixGroup {n : ℕ}
    (r : Setoid (Fin n)) (i j : Fin n) (hij : i ≠ j) (hr : r i j) :
    Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ blockMatrixGroup r := by
  intro c hc
  apply slMatrixConjugation_eq_self
  exact (diagonal_commute_transvection_iff c hij).mpr (hc i j hr)

/-- A generic lattice in prime dimension has no finite-volume orbit
under a proper nontrivial block group. All matrix-group and rationality
conditions have been discharged for this concrete block subgroup. -/
theorem block_partition_universal_of_finite_orbit {d : ℕ}
    (hn : (d + 1).Prime) (g : G (d + 1))
    (hzero : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    (r : Setoid (Fin (d + 1))) (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (μ : Measure (LatticeOrbitQuotient g (blockMatrixGroup r)))
    [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : blockMatrixGroup r,
      μ.map (fun x => latticeOrbitRightAction g (blockMatrixGroup r) x h) = μ) :
    ∀ i j, r i j := by
  have hell : Function.Injective (regularDiagonalWeights d) := by
    intro i j he
    by_contra hij
    have hgap := regularDiagonalWeights_separated d i j hij
    rw [he, sub_self, abs_zero] at hgap
    norm_num at hgap
  apply root_partition_universal_of_finite_orbit hn g hzero (blockMatrixGroup r)
    μ hμ hinv (regularDiagonalWeights d) (regularDiagonalWeights_sum d) hell
    (diagonalOneParameter_mem_blockMatrixGroup r _ _)
    r (transvection_mem_blockMatrixGroup r) (blockMatrixGroup_commute r) hnontrivial

end DukePrimeDegree

end

end OAI
