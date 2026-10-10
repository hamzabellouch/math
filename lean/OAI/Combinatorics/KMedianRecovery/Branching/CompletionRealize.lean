import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.RationalSurrogate
import OAI.Combinatorics.KMedianRecovery.Branching.CategoricalRawPrep
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionRealizeMath

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionRealize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n q a p r b : ℕ}
def pack (F S Q : Finset (Fin n)) (part : Fin q→Fin a) (o : Fin a→Fin q) (loc : Fin q→Fin n)
    (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n) (k : ℕ)
    (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ) (weight redBase : Fin r→ℚ)
    (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) : List Bool :=
  encode [BinaryFinSet.encode F,BinaryFinSet.encode S,BinaryFinSet.encode Q,
    BinaryFinSet.table part,BinaryFinSet.table o,BinaryFinSet.table loc,
    BinaryFinSet.table redLoc,BinaryFinSet.table blueLoc,BinaryFinSet.table blueDest,
    encode (xs.map BinaryCategorical.elemBits),BinaryCompletion.contextBits k base distance weight redBase redDistance]
noncomputable def fillInput (x : List Bool) : List Bool := encode [field 3 x,field 4 x,field 9 x]
noncomputable def fillInput_computes : PolyComputes fillInput :=
  cons_computes (field_computes 3) (cons_computes (field_computes 4) (cons_computes (field_computes 9) (const_computes [])))
noncomputable def filled (x : List Bool) : List Bool := BinaryFinSet.image
  (pairBits (field 5 x,BinaryCompletionFill.run (fillInput x)))
attribute [local irreducible] fillInput BinaryCompletionFill.run BinaryFinSet.image
noncomputable def filled_computes : PolyComputes filled :=
  ((field_computes 5).pair (fillInput_computes.comp BinaryCompletionFill.run_computes)).comp BinaryFinSet.image_computes
noncomputable def redValues (x : List Bool) : List Bool := BinaryCompletion.redValues (pairBits (field 10 x,field 9 x))
noncomputable def redValues_computes : PolyComputes redValues := by
  have redValuesComputes :=
    ((field_computes 10).pair (field_computes 9)).comp BinaryCompletion.redValues_computes
  unfold redValues
  simpa only [Function.comp_def] using redValuesComputes
noncomputable def redIndices (x : List Bool) : List Bool := BinaryNatSet.sort
  (BinaryRationalSort.rawIndices (pairBits (field 0 (field 10 x),redValues x)))
attribute [local irreducible] redValues BinaryNatSet.sort BinaryRationalSort.rawIndices
noncomputable def redIndices_computes : PolyComputes redIndices :=
  ((((field_computes 10).comp (field_computes 0)).pair redValues_computes).comp BinaryRationalSort.rawIndices_computes).comp BinaryNatSet.sort_computes
noncomputable def red (x : List Bool) : List Bool := BinaryFinSet.image (pairBits (field 6 x,redIndices x))
attribute [local irreducible] redIndices
noncomputable def red_computes : PolyComputes red := ((field_computes 6).pair redIndices_computes).comp BinaryFinSet.image_computes
noncomputable def blue (x : List Bool) : List Bool := BinaryNatSet.sort (field 7 x)
noncomputable def blue_computes : PolyComputes blue := (field_computes 7).comp BinaryNatSet.sort_computes
noncomputable def dest (x : List Bool) : List Bool := BinaryNatSet.sort (field 8 x)
noncomputable def dest_computes : PolyComputes dest := (field_computes 8).comp BinaryNatSet.sort_computes
noncomputable def removed (x : List Bool) : List Bool := BinaryNatSet.union
  (pairBits (BinaryNatSet.union (pairBits (field 2 x,red x)),blue x))
attribute [local irreducible] red blue dest BinaryNatSet.union
noncomputable def removed_computes : PolyComputes removed :=
  ((((field_computes 2).pair red_computes).comp BinaryNatSet.union_computes).pair blue_computes).comp BinaryNatSet.union_computes
noncomputable def remain (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (field 1 x,removed x))
attribute [local irreducible] removed BinaryNatSet.diff
noncomputable def remain_computes : PolyComputes remain := ((field_computes 1).pair removed_computes).comp BinaryNatSet.diff_computes
noncomputable def added (x : List Bool) : List Bool := BinaryNatSet.union (pairBits (filled x,dest x))
attribute [local irreducible] filled
noncomputable def added_computes : PolyComputes added := (filled_computes.pair dest_computes).comp BinaryNatSet.union_computes
noncomputable def core (x : List Bool) : List Bool := BinaryNatSet.union (pairBits (remain x,added x))
attribute [local irreducible] remain added
noncomputable def core_computes : PolyComputes core := (remain_computes.pair added_computes).comp BinaryNatSet.union_computes
noncomputable def runInput (x : List Bool) : List Bool := encode [field 0 x,core x,lengthBits (field 1 x)]
attribute [local irreducible] core
noncomputable def runInput_computes : PolyComputes runInput :=
  cons_computes (field_computes 0) (cons_computes core_computes
    (cons_computes ((field_computes 1).comp lengthBits_computes) (const_computes [])))
noncomputable def run (x : List Bool) : List Bool := BinaryCompletionPad.run (runInput x)
noncomputable def run_computes : PolyComputes run := runInput_computes.comp BinaryCompletionPad.run_computes
section Correct
variable (F S Q : Finset (Fin n)) (part : Fin q→Fin a) (o : Fin a→Fin q) (loc : Fin q→Fin n)
    (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n) (k : ℕ)
    (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ) (weight redBase : Fin r→ℚ)
    (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q))
local notation "data" => pack F S Q part o loc redLoc blueLoc blueDest k base distance weight redBase redDistance xs
local notation "v" => (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset)
lemma fillInput_pack : fillInput data=BinaryCompletionFill.pack part o xs := by
  simp only [fillInput,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rfl
lemma filled_pack : filled data=BinaryFinSet.encode (Completion.Canonical.filled part o loc xs) := by
  rw [filled,fillInput_pack,BinaryCompletionFill.run_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryCompletionFill.elemBits]
  exact BinaryFinSet.image_ofFn loc (Completion.Canonical.pick part o xs)
lemma redValues_pack : redValues data=encode (List.ofFn (fun i=>BinaryRational.encode (v i))) := by
  simp only [redValues,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryCompletion.redValues_pack]
lemma redIndices_pack : redIndices data=BinaryFinSet.encode (BinaryRationalSort.indexSet v k) := by
  rw [redIndices,redValues_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryCompletion.contextBits,BinaryFinSet.bottom_pack]
lemma red_pack : red data=BinaryFinSet.encode ((BinaryRationalSort.indexSet v k).image redLoc) := by
  rw [red,redIndices_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.image_pack]
lemma blue_pack : blue data=BinaryFinSet.encode (Finset.univ.image blueLoc) := by
  simp only [blue,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.sort_table]
lemma dest_pack : dest data=BinaryFinSet.encode (Finset.univ.image blueDest) := by
  simp only [dest,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.sort_table]
lemma removed_pack : removed data=BinaryFinSet.encode (Q∪(BinaryRationalSort.indexSet v k).image redLoc∪Finset.univ.image blueLoc) := by
  rw [removed,red_pack,blue_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.union_pack]
lemma remain_pack : remain data=BinaryFinSet.encode (S\(Q∪(BinaryRationalSort.indexSet v k).image redLoc∪Finset.univ.image blueLoc)) := by
  rw [remain,removed_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.diff_pack]
lemma added_pack : added data=BinaryFinSet.encode (Completion.Canonical.filled part o loc xs∪Finset.univ.image blueDest) := by
  rw [added,filled_pack,dest_pack,BinaryFinSet.union_pack]
lemma run_pack : run data=BinaryFinSet.encode (Completion.Canonical.realize F S Q part o loc redLoc blueLoc blueDest xs (BinaryRationalSort.indexSet v k)) := by
  rw [run,runInput,core,remain_pack,added_pack,BinaryFinSet.union_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFinSet.encode_lengthBits,BinaryFinSet.pad_pack]
  rfl
end Correct
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

end OAI
