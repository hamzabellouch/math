import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseTrialLaw
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartPadding

namespace OAI

/-! # Observation programs ignore their unused suffix -/
namespace ContingencyTables.DensePrograms
lemma wordChunk_take_blocks (n k : ℕ) (bits : List Bool) (i : ℕ) (hi : i<n) :
    wordChunk ((k,bits.take (n*k)),i)=wordChunk ((k,bits),i) := by
  have h := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hi)
  unfold wordChunk
  dsimp only
  rw [List.drop_take,List.take_take,min_eq_left]
  exact Nat.le_sub_of_add_le (by simpa only [Nat.succ_mul,Nat.add_comm] using h)
end ContingencyTables.DensePrograms

namespace ContingencyTables.CompanionObservationQueriesProgram
open DensePrograms
attribute [local irreducible] queryWidth queryPair output RootedLabelWeightProgram.output

lemma output_take (cs : Config×Config) (codes : List (List ℕ)) (bits : List Bool) :
    output (cs,(codes,bits.take (codes.length*blockWidth cs)))=output (cs,(codes,bits)) := by
  unfold output indices
  apply List.map_congr_left
  intro i hi
  apply congrArg queryPair
  change (cs,(codes.getD i [],wordChunk ((blockWidth cs,bits.take (codes.length*blockWidth cs)),i)))=
    (cs,(codes.getD i [],wordChunk ((blockWidth cs,bits),i)))
  rw [wordChunk_take_blocks codes.length (blockWidth cs) bits i (List.mem_range.mp hi)]

end ContingencyTables.CompanionObservationQueriesProgram

namespace ContingencyTables.CompanionObservedUpdateProgram
attribute [local irreducible] output queryInput finishInput
lemma output_take (cs : Configs) (base : Base) (bits : List Bool) :
    output ((cs,base),bits.take (base.1.1.2.length*CompanionObservationQueriesProgram.blockWidth cs))=
      output ((cs,base),bits) := by
  unfold output finishInput queryInput
  rw [CompanionObservationQueriesProgram.output_take]
end ContingencyTables.CompanionObservedUpdateProgram

namespace ContingencyTables.CompanionPhaseTrialProgram
attribute [local irreducible] output updateInput trajectory
  CompanionObservedUpdateProgram.output CompanionTrajectoryProgram.output
lemma output_take (base : Frame×CompanionTrajectoryProgram.Input) (bits : List Bool) :
    output (base,bits.take ((CompanionTrajectoryProgram.output base.2).length*
      CompanionObservationQueriesProgram.blockWidth base.1.1))=output (base,bits) := by
  unfold output updateInput storedInput returnInput trajectory catalogue
  dsimp only
  exact CompanionObservedUpdateProgram.output_take base.1.1
    (((PairedCatalogProgram.catalog base.2.1.1.2,CompanionTrajectoryProgram.output base.2),
      base.1.2.1),base.1.2.2) bits
end ContingencyTables.CompanionPhaseTrialProgram

end OAI
