import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.MetricArrays
import OAI.Combinatorics.KMedianRecovery.Branching.BranchWeights
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalCap

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q p r : ℕ}
def contextBits (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) : List Bool :=
  encode [k.bits,encode (List.ofFn (fun i=>rowBits (base i) (distance i))),
    encode (List.ofFn (fun i=>weightedRowBits (weight i) (redBase i) (redDistance i)))]
noncomputable def clientValues (x : List Bool) : List Bool :=
  mapWith cap (pairBits (discardPrefix x,field 1 (extractPrefix x)))
noncomputable def clientValues_computes : PolyComputes clientValues := by
  have clientValuesComputes :=
    (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 1))).comp (mapWith_computes cap_computes)
  unfold clientValues
  simpa only [Function.comp_def] using clientValuesComputes
noncomputable def redValues (x : List Bool) : List Bool :=
  mapWith weightedCap (pairBits (discardPrefix x,field 2 (extractPrefix x)))
noncomputable def redValues_computes : PolyComputes redValues := by
  have redValuesComputes :=
    (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp (mapWith_computes weightedCap_computes)
  unfold redValues
  simpa only [Function.comp_def] using redValuesComputes
lemma clientValues_pack (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) :
    clientValues (pairBits (contextBits k base distance weight redBase redDistance,encode (xs.map BinaryCategorical.elemBits)))=
      encode (List.ofFn (fun i=>BinaryRational.encode (capped (base i) (distance i) xs.toFinset))) := by
  simp only [clientValues,contextBits,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,mapWith_ofFn,cap_pack]
lemma redValues_pack (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) :
    redValues (pairBits (contextBits k base distance weight redBase redDistance,encode (xs.map BinaryCategorical.elemBits)))=
      encode (List.ofFn (fun i=>BinaryRational.encode (weight i*capped (redBase i) (redDistance i) xs.toFinset))) := by
  simp only [redValues,contextBits,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,mapWith_ofFn,weightedCap_pack]

def surrogateQ (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (S : Finset (Fin q)) : ℚ :=
  (∑ i,capped (base i) (distance i) S)+
    (BinaryRationalSort.bottomValues (fun i=>weight i*capped (redBase i) (redDistance i) S) k).sum
lemma surrogateQ_cast (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (S : Finset (Fin q)) :
    (surrogateQ k base distance weight redBase redDistance S:ℝ)=
      Completion.surrogate 0 k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) S := by
  simp only [surrogateQ,Rat.cast_add,Rat.cast_sum,BinaryRationalSort.bottom_sum_cast,
    Rat.cast_mul,capped_cast,Completion.surrogate,zero_add]
noncomputable def surrogate (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (RationalArray.sumWords (clientValues x))+
    BinaryRational.decode (BinaryRationalSort.sumBottom (pairBits (field 0 (extractPrefix x),redValues x))))
noncomputable def surrogate_computes : PolyComputes surrogate := by
  have surrogateComputes :=
    RatOps.add (RatOps.ofWords (clientValues_computes.comp RationalArray.sumWords_computes))
      (RatOps.ofWords (((extractPrefix_computes.comp (field_computes 0)).pair redValues_computes).comp BinaryRationalSort.sumBottom_computes))
  unfold surrogate
  simpa only [Function.comp_def] using surrogateComputes
lemma surrogate_pack (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) :
    surrogate (pairBits (contextBits k base distance weight redBase redDistance,encode (xs.map BinaryCategorical.elemBits)))=
      BinaryRational.encode (surrogateQ k base distance weight redBase redDistance xs.toFinset) := by
  unfold surrogate
  rw [clientValues_pack,redValues_pack]
  simp only [extractPrefix_pairBits,contextBits,field_encode,List.getElem?_cons_zero,Option.getD_some,
    BinaryRationalSort.sumBottom_pack]
  rw [show encode (List.ofFn (fun i=>BinaryRational.encode (capped (base i) (distance i) xs.toFinset)))=
    RationalArray.encode (List.ofFn (fun i=>capped (base i) (distance i) xs.toFinset)) by
      simp only [RationalArray.encode,List.map_ofFn,Function.comp_def]]
  rw [RationalArray.sumWords_encode,BinaryRational.decode_encode,BinaryRational.decode_encode,List.sum_ofFn]
  rfl

def savingQ (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (S : Finset (Fin q)) : ℚ :=
  surrogateQ k base distance weight redBase redDistance ∅-surrogateQ k base distance weight redBase redDistance S
lemma savingQ_cast (K : ℝ) (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (S : Finset (Fin q)) :
    (savingQ k base distance weight redBase redDistance S:ℝ)=
      Completion.saving K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) S := by
  simp only [savingQ,Rat.cast_sub,surrogateQ_cast,Completion.saving,Completion.surrogate]
  ring
noncomputable def saving (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (surrogate (pairBits (extractPrefix x,[])))-
    BinaryRational.decode (surrogate x))
noncomputable def saving_computes : PolyComputes saving :=
  RatOps.sub (RatOps.ofWords ((extractPrefix_computes.pair (const_computes [])).comp surrogate_computes))
    (RatOps.ofWords surrogate_computes)
lemma saving_pack (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) :
    saving (pairBits (contextBits k base distance weight redBase redDistance,encode (xs.map BinaryCategorical.elemBits)))=
      BinaryRational.encode (savingQ k base distance weight redBase redDistance xs.toFinset) := by
  unfold saving
  rw [extractPrefix_pairBits,surrogate_pack]
  rw [show ([]:List Bool)=encode (([]:List (Fin q)).map BinaryCategorical.elemBits) from rfl,surrogate_pack]
  simp only [BinaryRational.decode_encode,List.toFinset_nil,savingQ]
end MetricKMedianRecovery.BitMachine.BinaryCompletion

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRows
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n q r : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S G : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (loc : Fin q→Fin n) (red : Fin r→Fin n) (k : ℕ) : List Bool :=
  encode [BinarySamplingOracle.pack δ D S Δ s,BinarySamplingOracle.pack δ D G Δ ⟨∅,s.leaves⟩,
    BinaryFinSet.table loc,BinaryFinSet.table red,k.bits]
noncomputable def oracleInput (j : ℕ) (x : List Bool) : List Bool := pairBits (field j (extractPrefix x),discardPrefix x)
noncomputable def oracleInput_computes (j : ℕ) : PolyComputes (oracleInput j) :=
  (extractPrefix_computes.comp (field_computes j)).pair discardPrefix_computes
noncomputable def row (x : List Bool) : List Bool := BinarySamplingOracle.row (oracleInput 0 x)
noncomputable def row_computes : PolyComputes row := by
  have rowComputes := (oracleInput_computes 0).comp BinarySamplingOracle.row_computes
  unfold row
  simpa only [Function.comp_def] using rowComputes
noncomputable def distances (x : List Bool) : List Bool := BinaryIndexMap.run (pairBits (row x,field 2 (extractPrefix x)))
noncomputable def distances_computes : PolyComputes distances := by
  have distancesComputes :=
    (row_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp BinaryIndexMap.run_computes
  unfold distances
  simpa only [Function.comp_def] using distancesComputes
noncomputable def base (j : ℕ) (x : List Bool) : List Bool := extractPrefix (BinarySamplingOracle.reference (oracleInput j x))
noncomputable def base_computes (j : ℕ) : PolyComputes (base j) :=
  ((oracleInput_computes j).comp BinarySamplingOracle.reference_computes).comp extractPrefix_computes
noncomputable def capRow (j : ℕ) (x : List Bool) : List Bool := encode [base j x,distances x]
noncomputable def capRow_computes (j : ℕ) : PolyComputes (capRow j) :=
  cons_computes (base_computes j) (cons_computes distances_computes (const_computes []))
noncomputable def weight (x : List Bool) : List Bool := BinaryAssignmentWeight.run (pairBits
  (discardPrefix x,BinaryAssignmentWeight.identities (field 0 (extractPrefix x))))
noncomputable def weight_computes : PolyComputes weight := by
  have weightComputes :=
    (discardPrefix_computes.pair ((extractPrefix_computes.comp (field_computes 0)).comp BinaryAssignmentWeight.identities_computes)).comp
      BinaryAssignmentWeight.run_computes
  unfold weight
  simpa only [Function.comp_def] using weightComputes
noncomputable def redRow (x : List Bool) : List Bool := pairBits (weight x,capRow 1 x)
noncomputable def redRow_computes : PolyComputes redRow := weight_computes.pair (capRow_computes 1)
section Correct
variable (δ : Fin n→Fin n→ℚ) (D S G : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (loc : Fin q→Fin n) (red : Fin r→Fin n) (k : ℕ)
local notation "data" => pack δ D S G Δ s loc red k
lemma row_pair (u : Fin n) : row (pairBits (data,u.val.bits))=RationalMatrix.rowEncode (δ u) := by
  simp only [row,oracleInput,pack,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_zero,Option.getD_some,BinarySamplingOracle.row_pair]
lemma distances_pair (u : Fin n) : distances (pairBits (data,u.val.bits))=
    encode (List.ofFn (fun e=>BinaryRational.encode (δ u (loc e)))) := by
  rw [distances,row_pair]
  simp only [extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,
    Option.getD_some,BinaryFinSet.table,RationalMatrix.rowEncode_eq,BinaryIndexMap.run,mapWith_ofFn,
    BinaryIndexMap.item,extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn]
lemma base_zero (u : Fin n) : base 0 (pairBits (data,u.val.bits))=BinaryRational.encode (RationalSampling.reference δ S Δ s u) := by
  simp only [base,oracleInput,pack,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_zero,Option.getD_some,BinarySamplingOracle.reference_pair,extractPrefix_pairBits]
lemma base_one (u : Fin n) : base 1 (pairBits (data,u.val.bits))=BinaryRational.encode (RationalSampling.reference δ G Δ ⟨∅,s.leaves⟩ u) := by
  simp only [base,oracleInput,pack,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinarySamplingOracle.reference_pair,extractPrefix_pairBits]
lemma capRow_zero (u : Fin n) : capRow 0 (pairBits (data,u.val.bits))=
    BinaryCompletion.rowBits (RationalSampling.reference δ S Δ s u) (fun e=>δ u (loc e)) := by
  rw [capRow,base_zero,distances_pair]; rfl
lemma capRow_one (u : Fin n) : capRow 1 (pairBits (data,u.val.bits))=
    BinaryCompletion.rowBits (RationalSampling.reference δ G Δ ⟨∅,s.leaves⟩ u) (fun e=>δ u (loc e)) := by
  rw [capRow,base_one,distances_pair]; rfl
lemma weight_pair (u : Fin n) : weight (pairBits (data,u.val.bits))=
    BinaryRational.encode (RationalSampling.assignmentWeight δ D S Δ s u) := by
  simp only [weight,pack,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    Option.getD_some,BinaryAssignmentWeight.run_pack]
lemma redRow_pair (u : Fin n) : redRow (pairBits (data,u.val.bits))=
    BinaryCompletion.weightedRowBits (RationalSampling.assignmentWeight δ D S Δ s u)
      (RationalSampling.reference δ G Δ ⟨∅,s.leaves⟩ u) (fun e=>δ u (loc e)) := by
  rw [redRow,weight_pair,capRow_one]; rfl
end Correct
noncomputable def clients (x : List Bool) : List Bool := mapWith (capRow 0) (pairBits (x,field 1 (field 0 x)))
noncomputable def clients_computes : PolyComputes clients := by
  have clientsComputes :=
    (id_computes.pair ((field_computes 0).comp (field_computes 1))).comp (mapWith_computes (capRow_computes 0))
  unfold clients
  simpa only [Function.comp_def,id_eq] using clientsComputes
noncomputable def reds (x : List Bool) : List Bool := mapWith redRow (pairBits (x,field 3 x))
noncomputable def reds_computes : PolyComputes reds := by
  have redsComputes :=
    (id_computes.pair (field_computes 3)).comp (mapWith_computes redRow_computes)
  unfold reds
  simpa only [Function.comp_def,id_eq] using redsComputes
noncomputable def run (x : List Bool) : List Bool := encode [field 4 x,clients x,reds x]
noncomputable def run_computes : PolyComputes run := cons_computes (field_computes 4)
  (cons_computes clients_computes (cons_computes reds_computes (const_computes [])))
lemma run_pack (δ : Fin n→Fin n→ℚ) (D S G : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (loc : Fin q→Fin n) (red : Fin r→Fin n) (k : ℕ) :
    run (pack δ D S G Δ s loc red k)=BinaryCompletion.contextBits k
      (fun i=>RationalSampling.reference δ S Δ s (SortedIndex.enum D i))
      (fun i e=>δ (SortedIndex.enum D i) (loc e))
      (fun i=>RationalSampling.assignmentWeight δ D S Δ s (red i))
      (fun i=>RationalSampling.reference δ G Δ ⟨∅,s.leaves⟩ (red i))
      (fun i e=>δ (red i) (loc e)) := by
  have hD : field 1 (field 0 (pack δ D S G Δ s loc red k))=BinaryFinSet.encode D := by
    simp [pack,BinarySamplingOracle.pack,field_encode]
  have hR : field 3 (pack δ D S G Δ s loc red k)=BinaryFinSet.table red := by simp [pack,field_encode]
  have hC : clients (pack δ D S G Δ s loc red k)=encode (List.ofFn (fun i=>
      BinaryCompletion.rowBits (RationalSampling.reference δ S Δ s (SortedIndex.enum D i))
        (fun e=>δ (SortedIndex.enum D i) (loc e)))) := by
    rw [clients,hD,←BinaryFinSet.table_enum D]
    simp only [BinaryFinSet.table,mapWith_ofFn,capRow_zero]
  have hRe : reds (pack δ D S G Δ s loc red k)=encode (List.ofFn (fun i=>
      BinaryCompletion.weightedRowBits (RationalSampling.assignmentWeight δ D S Δ s (red i))
        (RationalSampling.reference δ G Δ ⟨∅,s.leaves⟩ (red i)) (fun e=>δ (red i) (loc e)))) := by
    rw [reds,hR]
    simp only [BinaryFinSet.table,mapWith_ofFn,redRow_pair]
  rw [run,hC,hRe]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryCompletion.contextBits]
end MetricKMedianRecovery.BitMachine.BinaryBranchRows

end OAI
