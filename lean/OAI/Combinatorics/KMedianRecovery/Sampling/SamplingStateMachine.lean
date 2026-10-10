import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestLeafMachine
import OAI.Combinatorics.KMedianRecovery.Recovery.ReferenceBridge
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalMenus

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
def encode (s : RationalSampling.State n) : List Bool := pairBits (BinaryFinSet.encode s.deleted,BinaryNearestLeaf.leavesBits s.leaves)
def optionBits (s : Option (RationalSampling.State n)) : List Bool := WordList.encode (s.toList.map encode)
lemma arrays_eq (s : RationalSampling.State n) :
    fromArrays s.deleted (fun i=>s.leaves[i.val].1) (fun i=>s.leaves[i.val].2)=s := by
  cases s with
  | mk T zs=>
    simp only [fromArrays]
    congr 1
    exact List.ofFn_get zs
noncomputable def remove (x : List Bool) : List Bool := pairBits
  (BinaryNatSet.union (pairBits (extractPrefix (extractPrefix x),WordList.encode [discardPrefix x])),discardPrefix (extractPrefix x))
noncomputable def remove_computes : PolyComputes remove :=
  (((extractPrefix_computes.comp extractPrefix_computes).pair
    (cons_computes discardPrefix_computes (const_computes []))).comp BinaryNatSet.union_computes).pair
    (extractPrefix_computes.comp discardPrefix_computes)
lemma remove_pair (s : RationalSampling.State n) (v : Fin n) : remove (pairBits (encode s,v.val.bits))=encode (s.remove v) := by
  have hv : WordList.encode [v.val.bits]=BinaryFinSet.encode {v} := by
    simp [BinaryFinSet.encode,BinaryFinSet.values,BinaryNatSet.encode,BinaryNatSet.pack]
  simp only [remove,extractPrefix_pairBits,discardPrefix_pairBits,encode]
  rw [hv,BinaryFinSet.union_pack]
  congr 1
  simp only [RationalSampling.State.remove,Finset.union_singleton]
noncomputable def add (x : List Bool) : List Bool :=
  pairBits (extractPrefix (extractPrefix x),discardPrefix (extractPrefix x)++WordList.encode [discardPrefix x])
noncomputable def add_computes : PolyComputes add := (extractPrefix_computes.comp extractPrefix_computes).pair
  ((extractPrefix_computes.comp discardPrefix_computes).append (cons_computes discardPrefix_computes (const_computes [])))
lemma add_pair (s : RationalSampling.State n) (w : Fin n) (R : ℚ) :
    add (pairBits (encode s,BinarySamplingReference.leafBits w R))=encode (s.add w R) := by
  simp only [add,extractPrefix_pairBits,discardPrefix_pairBits,encode,RationalSampling.State.add,
    BinaryNearestLeaf.leavesBits,List.map_append,List.map_cons,List.map_nil,encode_append]
noncomputable def keep (x : List Bool) : Bool := decide
  (value (UnaryResources.lengthBits (Count.run (discardPrefix (discardPrefix x))))≤value (extractPrefix x) ∧
   value (UnaryResources.lengthBits (Count.run (extractPrefix (discardPrefix x))))≤value (extractPrefix x))
noncomputable def keep_computes : PolyComputes (fun x=>[keep x]) := by
  simpa only [keep,Bool.decide_and,Function.comp_def] using (NatOps.le (((discardPrefix_computes.comp discardPrefix_computes).comp Count.run_computes).comp UnaryResources.lengthBits_computes)
    extractPrefix_computes).and
      (NatOps.le (((discardPrefix_computes.comp extractPrefix_computes).comp Count.run_computes).comp UnaryResources.lengthBits_computes)
        extractPrefix_computes)
noncomputable def retain (x : List Bool) : List Bool := if keep x then WordList.encode [discardPrefix x] else []
noncomputable def retain_computes : PolyComputes retain := keep_computes.cond
  (cons_computes discardPrefix_computes (const_computes [])) (const_computes [])
lemma retain_pair (m : ℕ) (s : RationalSampling.State n) : retain (pairBits (m.bits,encode s))=optionBits (RationalSampling.retain m s) := by
  have he : keep (pairBits (m.bits,encode s))=decide (s.leaves.length ≤ m ∧ s.deleted.card ≤ m) := by
    simp only [keep,encode,BinaryNearestLeaf.leavesBits,BinaryFinSet.encode_eq,extractPrefix_pairBits,discardPrefix_pairBits,
      Count.run_encode,List.length_map,UnaryResources.lengthBits_eq,List.length_replicate,value_bits,Finset.length_sort]
  rw [retain,he,discardPrefix_pairBits]
  simp only [RationalSampling.retain,optionBits,decide_eq_true_eq]
  split_ifs <;> rfl

def context (Δ : ℚ) (S : Finset (Fin n)) (s : RationalSampling.State n) : List Bool :=
  WordList.encode [n.bits,BinaryRational.encode Δ,BinaryFinSet.encode (S\s.deleted),BinaryNearestLeaf.leavesBits s.leaves]
noncomputable def referenceInput (x : List Bool) : List Bool := extractPrefix x++WordList.encode [discardPrefix x]
noncomputable def referenceInput_computes : PolyComputes referenceInput :=
  extractPrefix_computes.append (cons_computes discardPrefix_computes (const_computes []))
lemma referenceInput_pair (δ : Fin n→Fin n→ℚ) (Δ : ℚ) (S : Finset (Fin n)) (s : RationalSampling.State n) (w : Fin n) :
    referenceInput (pairBits (context Δ S s,RationalMatrix.rowEncode (δ w)))=
      BinarySamplingReference.pack Δ (S\s.deleted) (fun i=>s.leaves[i.val].1) (fun i=>s.leaves[i.val].2) (δ w) := by
  have hl : BinaryNearestLeaf.leavesBits s.leaves=WordList.encode
      (List.ofFn (fun i : Fin s.leaves.length=>BinarySamplingReference.leafBits s.leaves[i.val].1 s.leaves[i.val].2)) := by
    unfold BinaryNearestLeaf.leavesBits
    congr 1
    exact (congrArg (List.map (fun z=>BinarySamplingReference.leafBits z.1 z.2)) (List.ofFn_get s.leaves)).symm.trans
      List.map_ofFn
  simp only [referenceInput,context,extractPrefix_pairBits,discardPrefix_pairBits,←encode_append,BinarySamplingReference.pack,hl]
  rfl
noncomputable def reference (x : List Bool) : List Bool := BinarySamplingReference.run (referenceInput x)
noncomputable def reference_computes : PolyComputes reference := referenceInput_computes.comp BinarySamplingReference.run_computes
lemma reference_pair (δ : Fin n→Fin n→ℚ) (Δ : ℚ) (S : Finset (Fin n)) (s : RationalSampling.State n) (w : Fin n) :
    reference (pairBits (context Δ S s,RationalMatrix.rowEncode (δ w)))=
      pairBits (BinaryRational.encode (RationalSampling.reference δ S Δ s w),(chosenId δ S Δ s w).bits) := by
  rw [reference,referenceInput_pair,BinarySamplingReference.run_pack]
  simp only [values_finset,arrays_eq]
  rfl
end MetricKMedianRecovery.BitMachine.BinarySamplingState

namespace MetricKMedianRecovery.BitMachine.BinarySamplingOracle
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinarySamplingState.context Δ S s]
noncomputable def row (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,field 0 (extractPrefix x)))
noncomputable def row_computes : PolyComputes row :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes
lemma row_pair (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (w : Fin n) :
    row (pairBits (pack δ D S Δ s,w.val.bits))=RationalMatrix.rowEncode (δ w) := by
  simp only [row,pack,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,Option.getD_some,RationalMatrix.encode,lookup_ofFn]
noncomputable def reference (x : List Bool) : List Bool := BinarySamplingState.reference (pairBits (field 2 (extractPrefix x),row x))
noncomputable def reference_computes : PolyComputes reference :=
  ((extractPrefix_computes.comp (field_computes 2)).pair row_computes).comp BinarySamplingState.reference_computes
lemma reference_pair (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (w : Fin n) :
    reference (pairBits (pack δ D S Δ s,w.val.bits))=
      pairBits (BinaryRational.encode (RationalSampling.reference δ S Δ s w),(RationalSampling.chosenId δ S Δ s w).bits) := by
  rw [reference,row_pair]
  simp only [pack,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  exact BinarySamplingState.reference_pair δ Δ S s w
noncomputable def weight (x : List Bool) : ℚ := max 0 (BinaryRational.decode (extractPrefix (reference x)))
noncomputable def weight_computes : PolyComputes (fun x=>BinaryRational.encode (weight x)) :=
  RatOps.max (RatOps.const 0) (RatOps.ofWords (reference_computes.comp extractPrefix_computes))
lemma weight_pair (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (w : Fin n) :
    weight (pairBits (pack δ D S Δ s,w.val.bits))=RationalSampling.clientWeight δ S Δ s w := by
  rw [weight,reference_pair,extractPrefix_pairBits,BinaryRational.decode_encode]
  rfl
noncomputable def weights (x : List Bool) : List Bool := mapWith (fun y=>BinaryRational.encode (weight y)) (pairBits (x,field 1 x))
noncomputable def weights_computes : PolyComputes weights := by
  have computation := (id_computes.pair (field_computes 1)).comp (mapWith_computes weight_computes)
  unfold weights
  simpa only [Function.comp_def, id_eq] using computation
lemma weights_pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) :
    weights (pack δ D S Δ s)=RationalArray.encode ((D.sort (·≤·)).map (RationalSampling.clientWeight δ S Δ s)) := by
  unfold weights
  have hfield : field 1 (pack δ D S Δ s)=BinaryFinSet.encode D := by simp [pack,field_encode]
  rw [hfield,BinaryFinSet.encode_eq,mapWith_encode]
  simp only [List.map_map,Function.comp_def,weight_pair,RationalArray.encode]
noncomputable def total (x : List Bool) : ℚ := BinaryRational.decode (RationalArray.sumWords (weights x))
noncomputable def total_computes : PolyComputes (fun x=>BinaryRational.encode (total x)) :=
  RatOps.ofWords (weights_computes.comp RationalArray.sumWords_computes)
lemma total_pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) :
    total (pack δ D S Δ s)=RationalSampling.totalWeight δ D S Δ s := by
  rw [total,weights_pack,RationalArray.sumWords_encode,BinaryRational.decode_encode]
  unfold RationalSampling.totalWeight
  rw [←List.sum_toFinset _ (Finset.sort_nodup D (·≤·)),Finset.sort_toFinset]
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

end OAI
