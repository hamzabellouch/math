import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Distributions

namespace OAI

/-! Fixed rational distributions and their entropy and capacity formulas. -/

namespace MatrixMultiplication.AllFieldParameters

def placements (s : Shape) : List Shape :=
  [shape (s 0) (s 1) (s 2), shape (s 0) (s 2) (s 1),
   shape (s 1) (s 0) (s 2), shape (s 1) (s 2) (s 0),
   shape (s 2) (s 0) (s 1), shape (s 2) (s 1) (s 0)]

theorem initialMultiplicity_counts_placements : ∀ s ∈ sortedInitial,
    (placements s).eraseDups.length = initialMultiplicity s := by decide +kernel

theorem parents_nodup : sortedInitial.Nodup ∧ positiveInitial.Nodup ∧
    positiveSecond.Nodup ∧ zeroSecond.Nodup := by decide +kernel

theorem split_keys_nodup : (splitKeys positiveInitial).Nodup ∧
    (splitKeys positiveSecond).Nodup := by decide +kernel

theorem binary_keys_nodup : binaryKeys.Nodup := by decide +kernel

theorem pair_keys_nodup : pairKeys.Nodup := by decide +kernel

theorem stageA_children_nodup : ∀ s ∈ positiveInitial, (below s).Nodup := by decide +kernel

theorem stageB_children_nodup : ∀ s ∈ positiveSecond, (below s).Nodup := by decide +kernel

theorem ordered_pairs_nodup : ∀ t ∈ zeroSecond, (orderedPairs t).Nodup := by decide +kernel

theorem initial_placements_partition :
    (sortedInitial.flatMap (fun s => (placements s).eraseDups)).Perm (shapes 16) := by
  decide +kernel

end MatrixMultiplication.AllFieldParameters

end OAI
