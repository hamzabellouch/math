import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionRealize
import OAI.Combinatorics.KMedianRecovery.Recovery.ListSetExtra

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm
open WordOperations WordList BinaryArithmetic
variable {n q a p r b T L : ℕ}
noncomputable def selected (x : List Bool) : List Bool := BinaryCategorical.output BinaryCompletion.saving (discardPrefix x)
noncomputable def selected_computes : PolyComputes selected :=
  discardPrefix_computes.comp (BinaryCategorical.output_computes BinaryCompletion.saving_computes)
noncomputable def input (x : List Bool) : List Bool := Set.run (Set.pack (extractPrefix x) (9:ℕ).bits (selected x))
attribute [local irreducible] selected Set.run
noncomputable def input_computes : PolyComputes input :=
  (Set.pack_computes extractPrefix_computes (const_computes (9:ℕ).bits) selected_computes).comp Set.run_computes
noncomputable def run (x : List Bool) : List Bool := BinaryCompletionRealize.run (input x)
noncomputable def run_computes : PolyComputes run := input_computes.comp BinaryCompletionRealize.run_computes
noncomputable def choices (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) : List (Fin q) :=
  BinaryCategorical.drawn (Categorical.Selected.greedyRun part (BinaryCategorical.rule part hp)
    (fun S=>(BinaryCompletion.savingQ k base distance weight redBase redDistance S:ℝ)) seed.1).2 seed.2
lemma choices_toFinset (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) :
    (choices k base distance weight redBase redDistance part hp seed).toFinset=
      Categorical.Selected.greedyOutput part (BinaryCategorical.rule part hp)
        (fun S=>(BinaryCompletion.savingQ k base distance weight redBase redDistance S:ℝ)) seed :=
  BinaryCategorical.drawn_toFinset _ _
lemma choices_feasible (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) :
    Categorical.PartitionFeasible part (choices k base distance weight redBase redDistance part hp seed).toFinset := by
  rw [choices_toFinset]
  exact Categorical.Selected.greedyOutput_feasible _ _ _ _
lemma run_pack (F S Q : Finset (Fin n)) (part : Fin q→Fin a) (hp : Function.Surjective part)
    (o : Fin a→Fin q) (loc : Fin q→Fin n) (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n)
    (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) :
    let xs := choices k base distance weight redBase redDistance part hp seed
    run (pairBits (BinaryCompletionRealize.pack F S Q part o loc redLoc blueLoc blueDest k base distance weight redBase redDistance [],
      BinaryCategorical.outputPack (BinaryCompletion.contextBits k base distance weight redBase redDistance) part seed))=
      BinaryFinSet.encode (Completion.Canonical.realize F S Q part o loc redLoc blueLoc blueDest xs
        (BinaryRationalSort.indexSet (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k)) := by
  dsimp only
  unfold run input selected
  rw [discardPrefix_pairBits,extractPrefix_pairBits,BinaryCategorical.output_pack BinaryCompletion.saving _ _
    (BinaryCompletion.saving_pack k base distance weight redBase redDistance) part hp seed]
  change BinaryCompletionRealize.run (Set.run (Set.pack _ (9:ℕ).bits
    (encode ((choices k base distance weight redBase redDistance part hp seed).map BinaryCategorical.elemBits))))=_
  rw [BinaryCompletionRealize.pack,Set.run_encode _ _ (by simp)]
  change BinaryCompletionRealize.run
    (BinaryCompletionRealize.pack F S Q part o loc redLoc blueLoc blueDest k base distance weight redBase redDistance
      (choices k base distance weight redBase redDistance part hp seed))=_
  exact BinaryCompletionRealize.run_pack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
end MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm

end OAI
