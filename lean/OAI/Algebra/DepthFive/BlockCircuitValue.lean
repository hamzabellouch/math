import OAI.Algebra.DepthFive.BlockCircuit
import OAI.Algebra.DepthFive.IndexedCircuitValue
import OAI.Algebra.DepthFive.BlockMiddleSemantics
import OAI.Algebra.DepthFive.ImmBlocks

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BlockData

variable {n : ℕ}

@[simp] theorem indexedCircuit_bottomValue (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) (v : Fin n × Fin n × Fin n) :
    (indexedCircuit K blocks z).bottomValue v = MvPolynomial.X v := by
  simp [IndexedDepth5Circuit.bottomValue, indexedCircuit, d5LeafValue]

@[simp] theorem indexedCircuit_lowerValue (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) (p : Lower blocks) :
    (indexedCircuit K blocks z).lowerValue p = lowerMonomial K blocks p := by
  simp [IndexedDepth5Circuit.lowerValue, indexedCircuit, lowerMonomial,
    IndexedDepth5Circuit.bottomValue, d5LeafValue]

@[simp] theorem indexedCircuit_middleValue (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) (m : Middle blocks) :
    (indexedCircuit K blocks z).middleValue m =
      immBlock K n (blocks.get m.1) m.2.1 m.2.2 := by
  change ((middleInputs K blocks m).map (fun e =>
    MvPolynomial.C e.1 * (indexedCircuit K blocks z).lowerValue e.2)).sum = _
  simp_rw [indexedCircuit_lowerValue]
  exact middleInputs_value K blocks m

@[simp] theorem indexedCircuit_upperValue (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) (p : Upper blocks z) :
    (indexedCircuit K blocks z).upperValue p =
      ((upperInputs blocks z p).map (fun e =>
        immBlock K n (blocks.get e.1) e.2.1 e.2.2)).prod := by
  change ((upperInputs blocks z p).map
    (fun m => (indexedCircuit K blocks z).middleValue m)).prod = _
  simp only [indexedCircuit_middleValue]

/-- The block circuit computes the corresponding entry of the product of block matrices. -/
theorem indexedCircuit_circuitValue (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) :
    (indexedCircuit K blocks z).circuitValue =
      ((blocks.map (immBlock K n)).prod) z z := by
  change ((outputInputs K blocks z).map (fun e =>
    MvPolynomial.C e.1 * (indexedCircuit K blocks z).upperValue e.2)).sum = _
  simp only [indexedCircuit_upperValue, outputInputs, List.map_ofFn,
    Function.comp_def, MvPolynomial.C_1, one_mul, List.sum_ofFn]
  change (∑ k : Fin (matrixEntryPaths (List.finRange blocks.length) z z).length,
    (((matrixEntryPaths (List.finRange blocks.length) z z).get k).map
      (fun e => immBlock K n (blocks.get e.1) e.2.1 e.2.2)).prod) = _
  rw [matrixEntryPaths_fin_sum_prod (fun j : Fin blocks.length =>
    immBlock K n (blocks.get j))]
  simp [← List.ofFn_eq_map]

/-- Semantic correctness after converting all gate indices to `Fin`. -/
theorem circuit_value (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) :
    Problem335.circuitValue (circuit K blocks z) =
      ((blocks.map (immBlock K n)).prod) z z := by
  rw [circuit, IndexedDepth5Circuit.circuitValue_toDepth5Circuit,
    indexedCircuit_circuitValue]

/-- Any partition of the layers produces a circuit computing the qualified IMM polynomial. -/
theorem circuit_value_eq_imm (K : Type*) [CommSemiring K]
    (hn : 0 < n) (blocks : List (List (Fin n)))
    (hblocks : blocks.flatten = List.finRange n) :
    Problem335.circuitValue (circuit K blocks ⟨0, hn⟩) = imm K n := by
  rw [circuit_value, imm_eq_blocks_prod hn blocks hblocks]

end Problem335.BlockData

end

end OAI
