import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BranchContext
import OAI.Combinatorics.KMedianRecovery.Branching.BlueProgram
import OAI.Combinatorics.KMedianRecovery.Algorithms.CompletionAlgorithm

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFair
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Categorical.Explicit
variable {n q a p r c : ℕ}
noncomputable def context (x : List Bool) : List Bool := encode
  [field 10 (extractPrefix x),field 3 (extractPrefix x),Count.run (field 4 (extractPrefix x))]
noncomputable def context_computes : PolyComputes context :=
  cons_computes (extractPrefix_computes.comp (field_computes 10))
    (cons_computes (extractPrefix_computes.comp (field_computes 3))
      (cons_computes ((extractPrefix_computes.comp (field_computes 4)).comp Count.run_computes) (const_computes [])))
noncomputable def prepared (x : List Bool) : List Bool := BinaryCategorical.Prepare.run (pairBits (context x,discardPrefix x))
noncomputable def prepared_computes : PolyComputes prepared :=
  (context_computes.pair discardPrefix_computes).comp BinaryCategorical.Prepare.run_computes
attribute [local irreducible] prepared
noncomputable def run (x : List Bool) : List Bool := BinaryCompletionAlgorithm.run (pairBits (extractPrefix x,prepared x))
noncomputable def run_computes : PolyComputes run :=
  (extractPrefix_computes.pair prepared_computes).comp BinaryCompletionAlgorithm.run_computes
section Correct
variable (F S Q : Finset (Fin n)) (part : Fin q→Fin a) (hp : Function.Surjective part)
    (o : Fin a→Fin q) (loc : Fin q→Fin n) (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin c→Fin n)
    (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
local notation "data" => BinaryCompletionRealize.pack F S Q part o loc redLoc blueLoc blueDest k base distance weight redBase redDistance []
local notation "ctx" => BinaryCompletion.contextBits k base distance weight redBase redDistance
lemma context_pack (raw : List Bool) : context (pairBits (data,raw))=encode [ctx,BinaryCategorical.partBits part,List.replicate a true] := by
  simp only [context,extractPrefix_pairBits,BinaryCompletionRealize.pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.table,Count.run_encode,List.length_ofFn]
  rfl
noncomputable def result
    (bits : Categorical.BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool) : Finset (Fin n) :=
  let xs:=BinaryCompletionAlgorithm.choices k base distance weight redBase redDistance part hp
    (Categorical.binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits)
  Completion.Canonical.realize F S Q part o loc redLoc blueLoc blueDest xs
    (BinaryRationalSort.indexSet (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k)
lemma run_pack
    (bits : Categorical.BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool) :
    run (pairBits (data,BinaryCategorical.Tape.raw q a (exponent a) (samples q a) bits))=
      BinaryFinSet.encode (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits) := by
  rw [run,prepared,context_pack]
  simp only [discardPrefix_pairBits,extractPrefix_pairBits]
  rw [show pairBits (encode [ctx,BinaryCategorical.partBits part,List.replicate a true],
    BinaryCategorical.Tape.raw q a (exponent a) (samples q a) bits)=BinaryCategorical.Prepare.pack ctx part bits from rfl]
  rw [BinaryCategorical.Prepare.run_pack,BinaryCompletionAlgorithm.run_pack (hp:=hp)]
  rfl
lemma run_flat (s : Fin (BinaryCategorical.Tape.M q a (exponent a) (samples q a)+BinaryCategorical.Tape.K a (exponent a))→Bool) :
    run (pairBits (data,List.ofFn s))=BinaryFinSet.encode
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance
        (BinaryCategorical.Tape.layout q a (exponent a) (samples q a) s)) := by
  rw [←BinaryCategorical.Tape.raw_layout q a (exponent a) (samples q a) s]
  exact run_pack F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance _
end Correct
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
lemma table_id (m : ℕ) : table (id : Fin m→Fin m)=encode (Finset.univ : Finset (Fin m)) := by
  rw [table,encode_eq,Fin.sort_univ,List.ofFn_eq_map]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryFinSet
namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open WordOperations WordList BinaryBranchContext
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
noncomputable def blueInput (x : List Bool) : List Bool := encode [oracle x,classOf 2 x,field 7 x]
noncomputable def blueInput_computes : PolyComputes (blueInput) :=
  (cons_computes oracle_computes (cons_computes (classOf_computes 2) (cons_computes (field_computes 7) (const_computes []))))
attribute [local irreducible] blueInput
noncomputable def records (x : List Bool) : List Bool := BinaryBlueRecords.run (blueInput x)
noncomputable def records_computes : PolyComputes (records) := by
  unfold records
  have computes := blueInput_computes.comp BinaryBlueRecords.run_computes
  simpa only [Function.comp_def] using computes
attribute [local irreducible] records
noncomputable def bluePack (x : List Bool) : List Bool := encode [records x,field 2 x,field 8 x,field 10 x,field 11 x]
noncomputable def bluePack_computes : PolyComputes (bluePack) :=
  (cons_computes records_computes (cons_computes (field_computes 2) (cons_computes (field_computes 8) (cons_computes (field_computes 10) (cons_computes (field_computes 11) (const_computes []))))))
attribute [local irreducible] bluePack
noncomputable def best (d : ℕ) (x : List Bool) : List Bool := BinaryBlueProgram.run d (bluePack x)
noncomputable def best_computes (d : ℕ) : PolyComputes (best d) := by
  unfold best
  have computes := bluePack_computes.comp (BinaryBlueProgram.run_computes d)
  simpa only [Function.comp_def] using computes
attribute [local irreducible] best
noncomputable def plan (d : ℕ) (x : List Bool) : List Bool := BinaryBlueOutput.run (pairBits (best d x,field 8 x))
noncomputable def plan_computes (d : ℕ) : PolyComputes (plan d) :=
  ((best_computes d).pair (field_computes 8)).comp BinaryBlueOutput.run_computes
attribute [local irreducible] plan
noncomputable def rowInput (x : List Bool) : List Bool := encode [oracle x,greenOracle x,locations x,classOf 1 x,field 9 x]
noncomputable def rowInput_computes : PolyComputes (rowInput) :=
  (cons_computes oracle_computes (cons_computes greenOracle_computes (cons_computes locations_computes (cons_computes (classOf_computes 1) (cons_computes (field_computes 9) (const_computes []))))))
attribute [local irreducible] rowInput
noncomputable def rows (x : List Bool) : List Bool := BinaryBranchRows.run (rowInput x)
noncomputable def rows_computes : PolyComputes (rows) :=
  rowInput_computes.comp BinaryBranchRows.run_computes
attribute [local irreducible] rows
noncomputable def completion (d : ℕ) (x : List Bool) : List Bool := encode [field 2 x,field 3 x,extractPrefix (field 5 x),parts x,origins x,locations x,classOf 1 x,field 0 (plan d x),field 1 (plan d x),[],rows x]
noncomputable def completion_computes (d : ℕ) : PolyComputes (completion d) :=
  (cons_computes (field_computes 2) (cons_computes (field_computes 3) (cons_computes ((field_computes 5).comp extractPrefix_computes) (cons_computes parts_computes (cons_computes origins_computes (cons_computes locations_computes (cons_computes (classOf_computes 1) (cons_computes ((plan_computes d).comp (field_computes 0)) (cons_computes ((plan_computes d).comp (field_computes 1)) (cons_computes (const_computes []) (cons_computes rows_computes (const_computes []))))))))))))
attribute [local irreducible] completion
noncomputable def run (d : ℕ) (x : List Bool) : List Bool := BinaryCompletionFair.run (pairBits (completion d (extractPrefix x),discardPrefix x))
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  ((extractPrefix_computes.comp (completion_computes d)).pair discardPrefix_computes).comp BinaryCompletionFair.run_computes
attribute [local irreducible] run
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => BinaryBranchContext.pack δ D F S Δ s colors label k c extra
local notation "blue" => Finset.filter (fun i=>colors i=2) (S\RationalSampling.State.deleted s)
local notation "red" => Finset.filter (fun i=>colors i=1) (S\RationalSampling.State.deleted s)
local notation "green" => Finset.filter (fun i=>colors i=0) (S\RationalSampling.State.deleted s)
local notation "score" => (fun u v=>RationalSampling.assignmentWeight δ D S Δ s u*δ u v)
lemma blueInput_pack : blueInput data=BinaryBlueRecords.pack δ D S Δ s blue label := by
  have hc:=classOf_pack δ D F S Δ s colors label k c extra (2:Fin 3)
  change classOf 2 data=_ at hc
  rw [blueInput,oracle_pack,hc]
  simp only [BinaryBranchContext.pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryBlueRecords.pack]
lemma records_pack : records data=BinaryBlueItem.records (fun i=>i.val.bits) (fun i=>i.val.bits) blue label score := by
  rw [records,blueInput_pack,BinaryBlueRecords.run_pack]
lemma bluePack_pack : bluePack data=BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c := by
  rw [bluePack,records_pack]
  simp only [BinaryBranchContext.pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryBlueProgram.pack]
  rw [BinaryFinSet.table_id]
variable (hH : ∀ i,(balls δ F s i).Nonempty)
local notation "loc" => Completion.CopyGround.location (balls δ F s) hH
local notation "wt" => (fun i=>RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum red i))
local notation "rb" => (fun i=>RationalSampling.reference δ green Δ (RationalSampling.State.mk ∅ (RationalSampling.State.leaves s)) (SortedIndex.enum red i))
local notation "bas" => (fun i=>RationalSampling.reference δ S Δ s (SortedIndex.enum D i))
local notation "dst" => (fun i e=>δ (SortedIndex.enum D i) (loc e))
local notation "rd" => (fun i e=>δ (SortedIndex.enum red i) (loc e))
lemma rowInput_pack : rowInput data=BinaryBranchRows.pack δ D S green Δ s loc (SortedIndex.enum red) k := by
  have hc:=classOf_pack δ D F S Δ s colors label k c extra (1:Fin 3)
  change classOf 1 data=_ at hc
  rw [rowInput,oracle_pack,greenOracle_pack,locations_pack δ D F S Δ s colors label k c extra hH,hc]
  simp only [BinaryBranchContext.pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryBranchRows.pack,
    BinaryFinSet.table_enum]
lemma rows_pack : rows data=BinaryCompletion.contextBits k bas dst wt rb rd := by
  rw [rows,rowInput_pack δ D F S Δ s colors label k c extra hH,BinaryBranchRows.run_pack]
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
