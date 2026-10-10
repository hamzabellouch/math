import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitializedRestartProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartDataLaw
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartScheduleSemantics

namespace OAI

/-! # Literal inputs and disjoint slices of initialized restarts -/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS CommonBasesFPRAS FairBits DensePrograms
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction) (bits : List Bool) : Input :=
  ((CompanionRestartInitializer.data A C K H T N R L epsilon z v,
    List.ofFn (fun i : Fin j => (matrixCode (w (i.val+1)),estimates i))),bits)

lemma stages_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction) (bits : List Bool) :
    stages (data A C K H T N R L j epsilon z v w estimates bits)=
      CompanionRestartProgram.stagesData A C K j
        ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon) z v (List.replicate bits.length false) w := by
  unfold stages indices data
  rw [List.length_ofFn,DirectedBFSCode.range_eq_map]
  simp only [List.map_map,Function.comp_def]
  rw [←List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext i
  unfold stageAt reserve
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,
    List.map_const']
  rfl

lemma initialWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction) (bits : List Bool) :
    initialWidth (data A C K H T N R L j epsilon z v w estimates bits)=
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)) :=
  CompanionRestartInitializer.width_data A C K H T N R L epsilon z v

 /-- Exact physical splitting: the initializer sees the first block,
 the restart loop sees the remaining block, and all markers are fixed. -/
theorem output_split (A : Instance (Fin m) (Fin n)) (C K H T N R L j s : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction)
    (bits : Fin (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+s) → Bool) :
    output (data A C K H T N R L j epsilon z v w estimates (List.ofFn bits))=
      CompanionRestartProgram.output
        ((CompanionRestartProgram.stagesData A C K j
          ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon) z v
          (List.replicate (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+s) false) w,
          CompanionRestartInitializer.output
            (CompanionRestartInitializer.data A C K H T N R L epsilon z v,
              List.ofFn (splitWordEquiv
                (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))) s bits).1)),
          List.ofFn (splitWordEquiv
            (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))) s bits).2) := by
  unfold output prepare initialCode initialInput
  rw [stages_data,initialWidth_data,List.length_ofFn]
  dsimp only [data]
  rw [ofFn_split_take,ofFn_split_drop]

end
end ContingencyTables.CompanionInitializedRestartProgram

end OAI
