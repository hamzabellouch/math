import OAI.Algebra.DepthFive.IndexedCircuit
import OAI.Algebra.DepthFive.UpperBlockData

namespace OAI

noncomputable section

namespace Problem335.BlockData

variable {n : ℕ}

theorem middleInputs_empty_degree (K : Type*) [One K]
    (blocks : List (List (Fin n))) (m : Middle blocks)
    (h : middleInputs K blocks m = []) : middleDegree blocks m = 0 := by
  by_cases hb : blocks.get m.1 = []
  · change (blocks.get m.1).length = 0
    rw [hb]
    rfl
  · have hc := congrArg List.length h
    simp only [middleInputs, List.length_ofFn, List.length_nil] at hc
    have hp := matrixEntryPaths_length (blocks.get m.1) hb m.2.1 m.2.2
    have hn : 0 < n := Nat.zero_lt_of_lt m.2.1.isLt
    have hpos : 0 < (paths blocks m).length := by
      rw [paths, hp, Fintype.card_fin]
      exact Nat.pow_pos hn
    omega

theorem outputInputs_empty_degree (K : Type*) [One K]
    (blocks : List (List (Fin n))) (z : Fin n)
    (h : outputInputs K blocks z = []) : (blocks.map List.length).sum = 0 := by
  by_cases hb : blocks = []
  · simp [hb]
  · have hc := congrArg List.length h
    simp only [outputInputs, List.length_ofFn, List.length_nil] at hc
    have hp := matrixEntryPaths_length (List.finRange blocks.length)
      (by simpa using hb) z z
    have hn : 0 < n := Nat.zero_lt_of_lt z.isLt
    have hpos : 0 < (upperPaths blocks z).length := by
      rw [upperPaths, hp, Fintype.card_fin]
      exact Nat.pow_pos hn
    omega

/-- The actual homogeneous five-layer block-expansion circuit, before finite reindexing. -/
def indexedCircuit (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) :
    IndexedDepth5Circuit K n
      (Fin n × Fin n × Fin n) (Fin n × Fin n × Fin n)
      (Lower blocks) (Middle blocks) (Upper blocks z) where
  leaves := D5Leaf.variable
  bottomInputs v := [(1, v)]
  bottomDegree _ := 1
  bottomHomogeneous := by
    intro i entry h
    simp only [List.mem_singleton] at h
    subst entry
    rfl
  bottomEmpty := by simp
  lowerInputs := lowerInputs blocks
  middleInputs := middleInputs K blocks
  middleDegree := middleDegree blocks
  middleHomogeneous := by
    intro m entry h
    simpa using middleInputs_homogeneous K blocks m entry h
  middleEmpty := middleInputs_empty_degree K blocks
  upperInputs := upperInputs blocks z
  outputInputs := outputInputs K blocks z
  outputDegree := (blocks.map List.length).sum
  outputHomogeneous := by
    intro entry _
    exact upperInputs_degree blocks z entry.2
  outputEmpty := outputInputs_empty_degree K blocks z

/-- The qualified `Fin`-indexed circuit produced by block expansion. -/
def circuit (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) : Depth5Circuit K n :=
  (indexedCircuit K blocks z).toDepth5Circuit

@[simp] theorem circuit_outputDegree (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) :
    (circuit K blocks z).outputDegree = (blocks.map List.length).sum := rfl

theorem circuit_size (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) :
    circuitSize (circuit K blocks z) = 2 * n ^ 3 +
      Fintype.card (Lower blocks) + Fintype.card (Middle blocks) +
        Fintype.card (Upper blocks z) + 1 := by
  rw [circuit, IndexedDepth5Circuit.circuitSize_toDepth5Circuit]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

end Problem335.BlockData

end

end OAI
