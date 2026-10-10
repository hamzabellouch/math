import OAI.Algebra.DepthFive.BlockCircuitValue
import OAI.Algebra.DepthFive.BlockPartition
import OAI.Algebra.DepthFive.CeilArithmetic

namespace OAI

noncomputable section

namespace Problem335

/-- The canonical block circuit at block width `ceilSqrt n`. -/
def immUpperCircuit (K : Type*) [CommSemiring K] (n : ℕ) (hn : 0 < n) :
    Depth5Circuit K n :=
  BlockData.circuit K (layerBlocks n (ceilSqrt n)) ⟨0, hn⟩

@[simp] theorem immUpperCircuit_outputDegree (K : Type*) [CommSemiring K]
    (n : ℕ) (hn : 0 < n) : (immUpperCircuit K n hn).outputDegree = n := by
  simp [immUpperCircuit]

theorem immUpperCircuit_size (K : Type*) [CommSemiring K]
    (n : ℕ) (hn : 0 < n) : circuitSize (immUpperCircuit K n hn) ≤ upperGateBound n := by
  have ht : 0 < ceilSqrt n := ceilSqrt_pos hn
  have hb : layerBlocks n (ceilSqrt n) ≠ [] := by
    intro h
    have hlen := layerBlocks_length (n := n) ht
    rw [h, List.length_nil] at hlen
    have hp := ceilDiv_pos hn ht
    omega
  have hne : ∀ b : Fin (layerBlocks n (ceilSqrt n)).length,
      (layerBlocks n (ceilSqrt n)).get b ≠ [] := by
    intro b
    exact layerBlocks_nonempty ht (List.get_mem ..)
  have hlower := BlockData.card_lower_le (layerBlocks n (ceilSqrt n))
    (ceilSqrt n) hn hne (layerBlocks_get_length_le ht)
  have hlen := layerBlocks_length (n := n) ht
  rw [immUpperCircuit, BlockData.circuit_size, BlockData.card_middle,
    BlockData.card_upper _ hb]
  calc
    _ ≤ 2 * n ^ 3 + (layerBlocks n (ceilSqrt n)).length * n ^ (ceilSqrt n + 1) +
        (layerBlocks n (ceilSqrt n)).length * n ^ 2 +
        n ^ ((layerBlocks n (ceilSqrt n)).length - 1) + 1 := by omega
    _ = upperGateBound n := by
      rw [hlen]
      simp only [upperGateBound]
      omega

@[simp] theorem immUpperCircuit_value (K : Type*) [CommSemiring K]
    (n : ℕ) (hn : 0 < n) : circuitValue (immUpperCircuit K n hn) = imm K n := by
  exact BlockData.circuit_value_eq_imm K hn (layerBlocks n (ceilSqrt n))
    (layerBlocks_flatten n (ceilSqrt n))

/-- A homogeneous depth-five circuit attaining the explicit block-expansion gate budget. -/
theorem exists_imm_circuit_le_upperGateBound (K : Type*) [CommSemiring K]
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : Depth5Circuit K n, circuitValue c = imm K n ∧ circuitSize c ≤ upperGateBound n := by
  have hn0 : 0 < n := by omega
  exact ⟨immUpperCircuit K n hn0, immUpperCircuit_value K n hn0,
    immUpperCircuit_size K n hn0⟩

end Problem335

end

end OAI
