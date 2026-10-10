import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockTransverse
import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantMeasureGroup

namespace OAI

/-!
# Compact corrections from the closure of one root block

Haar patches are taken in the closed root-generated subgroup. This
closure still preserves the same finite measure. Continuity preserves
the exact normalization of the within-block matrix part, so no abstract
Lie-subgroup or homogeneous-orbit statement is needed for these patches.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma singleBlock_closure_le_stabilizer {n : ℕ}
    (S : Set (Fin n)) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hH : singleBlockRootGroup S ≤ invariantRightSubgroup μ) :
    (singleBlockRootGroup S).topologicalClosure ≤ invariantRightSubgroup μ :=
  (singleBlockRootGroup S).topologicalClosure_minimal hH (isClosed_invariantRightSubgroup μ)

lemma singleBlock_closure_le_blockComplement {n : ℕ} (S : Set (Fin n)) :
    (singleBlockRootGroup S).topologicalClosure ≤ blockMatrixGroup (blockComplementSetoid S) :=
  (singleBlockRootGroup S).topologicalClosure_minimal
    (singleBlockRootGroup_le_blockComplement S)
    (isClosed_blockMatrixGroup (blockComplementSetoid S))

lemma withinBlockPart_singleBlock_closure_commutes {n : ℕ}
    (S : Set (Fin n)) (g : G n) (c : ℝ)
    (hdiag : ∀ i ∈ S, g.val i i = c)
    (hzero : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → g.val i j = 0)
    (u : G n) (hu : u ∈ (singleBlockRootGroup S).topologicalClosure) :
    slMatrixConjugation u (withinBlockPart (blockComplementSetoid S) g.val) =
      withinBlockPart (blockComplementSetoid S) g.val := by
  let M := withinBlockPart (blockComplementSetoid S) g.val
  have hclosed : IsClosed {v : G n | slMatrixConjugation v M = M} :=
    isClosed_eq (by unfold slMatrixConjugation; fun_prop) continuous_const
  exact closure_minimal
    (fun v hv => withinBlockPart_singleBlock_commutes S g c hdiag hzero v hv) hclosed hu

theorem withinBlockPart_singleBlock_closure_conjugation {n : ℕ}
    (S : Set (Fin n)) (g : G n) (c : ℝ)
    (hdiag : ∀ i ∈ S, g.val i i = c)
    (hzero : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → g.val i j = 0)
    (u : G n) (hu : u ∈ (singleBlockRootGroup S).topologicalClosure) :
    withinBlockPart (blockComplementSetoid S) (u * g * u⁻¹).val =
      withinBlockPart (blockComplementSetoid S) g.val := by
  let r := blockComplementSetoid S
  have hb : u ∈ blockMatrixGroup r := singleBlock_closure_le_blockComplement S hu
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
    withinBlockPart_mul_left r u.val _ (cross_zero_of_mem_blockMatrixGroup r u hb),
    withinBlockPart_mul_right r g.val u⁻¹.val
      (cross_zero_of_mem_blockMatrixGroup r u⁻¹ ((blockMatrixGroup r).inv_mem hb))]
  simpa only [slMatrixConjugation, inv_inv, Matrix.mul_assoc] using
    withinBlockPart_singleBlock_closure_commutes S g c hdiag hzero u⁻¹
      ((singleBlockRootGroup S).topologicalClosure.inv_mem hu)

end DukePrimeDegree

end

end OAI
