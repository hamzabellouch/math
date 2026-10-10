import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BranchWeights
import OAI.Combinatorics.KMedianRecovery.Branching.BlueMerge

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A R : Type*}
lemma choose_none (x : Candidate A) : choose x none=x := by cases x <;> rfl
lemma select_cond (p : R→Prop) [DecidablePred p] (f : R→Candidate A) (rs : List R) :
    select (rs.map (fun r=>if p r then f r else none))=select ((rs.filter p).map f) := by
  have h (s : Candidate A) : (rs.map (fun r=>if p r then f r else none)).foldl choose s=((rs.filter p).map f).foldl choose s := by
    induction rs generalizing s with
    | nil=>rfl
    | cons r rs ih=>
      by_cases hp : p r
      · simp [hp,ih]
      · simp [hp,choose_none,ih]
  exact h none
end MetricKMedianRecovery.BlueDP
namespace MetricKMedianRecovery.BitMachine.BinaryBlueChoice
lemma select_map {A R : Type*} (enc : A→List Bool) (f : R→BlueDP.Candidate A) (rs : List R) :
    select (WordList.encode (rs.map (fun r=>encode enc (f r))))=encode enc (BlueDP.select (rs.map f)) := by
  simpa only [List.map_map,Function.comp_def] using select_pack enc (rs.map f)
end MetricKMedianRecovery.BitMachine.BinaryBlueChoice
namespace MetricKMedianRecovery.BitMachine.BinaryBlueItem
open WordOperations WordList
variable {L R : Type*} [LinearOrder R] [LinearOrder L] {n : ℕ}
def atomEnc (el : L→List Bool) (er : R→List Bool) (a : BlueDP.Atom L R (Fin n)) : List Bool :=
  pairBits (el a.1,pairBits (er a.2.1,a.2.2.val.bits))
def record (el : L→List Bool) (er : R→List Bool) (label : R→L) (q : R→Fin n→ℚ) (r : R) : List Bool :=
  pairBits (er r,pairBits (el (label r),RationalArray.encode (List.ofFn (q r))))
def records (el : L→List Bool) (er : R→List Bool) (B : Finset R) (label : R→L) (q : R→Fin n→ℚ) : List Bool :=
  WordList.encode ((B.sort (·≤·)).map (record el er label q))
def targetL (x : List Bool) : List Bool := extractPrefix (extractPrefix x)
def targetY (x : List Bool) : List Bool := discardPrefix (extractPrefix x)
def sourceR (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
def sourceL (x : List Bool) : List Bool := extractPrefix (discardPrefix (discardPrefix x))
def sourceRow (x : List Bool) : List Bool := discardPrefix (discardPrefix (discardPrefix x))
noncomputable def targetL_computes : PolyComputes targetL := extractPrefix_computes.comp extractPrefix_computes
noncomputable def targetY_computes : PolyComputes targetY := extractPrefix_computes.comp discardPrefix_computes
noncomputable def sourceR_computes : PolyComputes sourceR := discardPrefix_computes.comp extractPrefix_computes
noncomputable def sourceL_computes : PolyComputes sourceL := (discardPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def sourceRow_computes : PolyComputes sourceRow := (discardPrefix_computes.comp discardPrefix_computes).comp discardPrefix_computes
noncomputable def price (x : List Bool) : List Bool := Lookup.run (pairBits (targetY x,sourceRow x))
noncomputable def price_computes : PolyComputes price := (targetY_computes.pair sourceRow_computes).comp Lookup.run_computes
noncomputable def response (x : List Bool) : List Bool := WordList.encode [pairBits (price x,
  WordList.encode [pairBits (targetL x,pairBits (sourceR x,targetY x))])]
noncomputable def response_computes : PolyComputes response :=
  cons_computes (price_computes.pair (cons_computes (targetL_computes.pair (sourceR_computes.pair targetY_computes)) (const_computes []))) (const_computes [])
noncomputable def op (x : List Bool) : List Bool := if WordEq.eq (pairBits (sourceL x,targetL x)) then response x else []
noncomputable def op_computes : PolyComputes op :=
  ((sourceL_computes.pair targetL_computes).comp WordEq.eq_computes).cond response_computes (const_computes [])
omit [LinearOrder R] in
lemma op_pack (el : L→List Bool) (er : R→List Bool) (hel : Function.Injective el) (label : R→L) (q : R→Fin n→ℚ) (r : R) (l : L) (y : Fin n) :
    op (pairBits (pairBits (el l,y.val.bits),record el er label q r))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (atomEnc el er))
        (if label r=l then some (q r y,[(l,r,y)]) else none) := by
  simp only [op,sourceL,targetL,record,extractPrefix_pairBits,discardPrefix_pairBits,WordEq.eq_pair,hel.eq_iff,decide_eq_true_eq]
  split_ifs with h
  · simp only [response,price,targetY,sourceRow,sourceR,targetL,extractPrefix_pairBits,discardPrefix_pairBits,
      RationalArray.encode,List.map_ofFn,lookup_ofFn,BinaryBlueChoice.encode,BinaryBlueMerge.listEnc,List.map_cons,List.map_nil,atomEnc,Function.comp_apply]
  · rfl
noncomputable def run (x : List Bool) : List Bool := BinaryBlueChoice.select (mapWith op x)
noncomputable def run_computes : PolyComputes run := (mapWith_computes op_computes).comp BinaryBlueChoice.select_computes
lemma run_pack (el : L→List Bool) (er : R→List Bool) (hel : Function.Injective el) (B : Finset R) (label : R→L) (q : R→Fin n→ℚ) (l : L) (y : Fin n) :
    run (pairBits (pairBits (el l,y.val.bits),records el er B label q))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (atomEnc el er)) (BlueDP.item B label q l y) := by
  simp only [run,records,mapWith_encode,List.map_map,Function.comp_def,op_pack el er hel]
  rw [BinaryBlueChoice.select_map,BlueDP.select_cond]
  congr 1
  unfold BlueDP.item
  have hn := (Finset.sort_nodup B (·≤·)).filter (fun r=>decide (label r=l))
  have hp := (Finset.pairwise_sort B (·≤·)).filter (fun r=>decide (label r=l))
  have hs := (List.toFinset_sort (r:=(·≤·)) hn).mpr hp
  have he : (B.filter (label ·=l)).sort (·≤·)=(B.sort (·≤·)).filter (fun r=>decide (label r=l)) := by
    simpa only [List.toFinset_filter,Finset.sort_toFinset,decide_eq_true_eq] using hs
  rw [he]
end MetricKMedianRecovery.BitMachine.BinaryBlueItem

namespace MetricKMedianRecovery.BitMachine.BinaryBlueRecords
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (B : Finset (Fin n)) (label : Fin n→Fin m) : List Bool :=
  encode [BinarySamplingOracle.pack δ D S Δ s,BinaryFinSet.encode B,BinaryFinSet.table label]
noncomputable def oracleInput (x : List Bool) : List Bool := pairBits (field 0 (extractPrefix x),discardPrefix x)
noncomputable def oracleInput_computes : PolyComputes oracleInput :=
  (extractPrefix_computes.comp (field_computes 0)).pair discardPrefix_computes
noncomputable def row (x : List Bool) : List Bool := BinarySamplingOracle.row (oracleInput x)
noncomputable def row_computes : PolyComputes row := by
  unfold row
  have computes := oracleInput_computes.comp BinarySamplingOracle.row_computes
  simpa only [Function.comp_def] using computes
noncomputable def weight (x : List Bool) : List Bool := BinaryAssignmentWeight.run (pairBits
  (discardPrefix x,BinaryAssignmentWeight.identities (field 0 (extractPrefix x))))
noncomputable def weight_computes : PolyComputes weight := by
  unfold weight
  have computes := (discardPrefix_computes.pair ((extractPrefix_computes.comp (field_computes 0)).comp BinaryAssignmentWeight.identities_computes)).comp
    BinaryAssignmentWeight.run_computes
  simpa only [Function.comp_def] using computes
noncomputable def scaled (x : List Bool) : List Bool := RationalMatrix.vectorScale (pairBits (weight x,row x))
noncomputable def scaled_computes : PolyComputes scaled := by
  unfold scaled
  have computes := (weight_computes.pair row_computes).comp RationalMatrix.vectorScale_computes
  simpa only [Function.comp_def] using computes
noncomputable def tag (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,field 2 (extractPrefix x)))
noncomputable def tag_computes : PolyComputes tag :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp Lookup.run_computes
noncomputable def op (x : List Bool) : List Bool := pairBits (discardPrefix x,pairBits (tag x,scaled x))
noncomputable def op_computes : PolyComputes op := discardPrefix_computes.pair (tag_computes.pair scaled_computes)
lemma op_pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (B : Finset (Fin n)) (label : Fin n→Fin m) (r : Fin n) :
    op (pairBits (pack δ D S Δ s B label,r.val.bits))=
      BinaryBlueItem.record (fun i=>i.val.bits) (fun i=>i.val.bits) label
        (fun u v=>RationalSampling.assignmentWeight δ D S Δ s u*δ u v) r := by
  have h0 : field 0 (pack δ D S Δ s B label)=BinarySamplingOracle.pack δ D S Δ s := by
    simp only [pack,field_encode,List.getElem?_cons_zero,Option.getD_some]
  have h2 : field 2 (pack δ D S Δ s B label)=BinaryFinSet.table label := by
    simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  have hw : weight (pairBits (pack δ D S Δ s B label,r.val.bits))=
      BinaryRational.encode (RationalSampling.assignmentWeight δ D S Δ s r) := by
    simp only [weight,extractPrefix_pairBits,discardPrefix_pairBits,h0,BinaryAssignmentWeight.run_pack]
  have hr : row (pairBits (pack δ D S Δ s B label,r.val.bits))=RationalMatrix.rowEncode (δ r) := by
    simp only [row,oracleInput,extractPrefix_pairBits,discardPrefix_pairBits,h0,BinarySamplingOracle.row_pair]
  simp only [op,tag,scaled,extractPrefix_pairBits,discardPrefix_pairBits,h2,hw,hr,
    BinaryFinSet.table,lookup_ofFn]
  rw [RationalMatrix.vectorScale_encode]
  simp only [BinaryBlueItem.record,RationalArray.encode,RationalMatrix.rowEncode_eq,
    Pi.smul_apply,smul_eq_mul,List.map_ofFn,Function.comp_def]
noncomputable def run (x : List Bool) : List Bool := mapWith op (pairBits (x,field 1 x))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := (id_computes.pair (field_computes 1)).comp (mapWith_computes op_computes)
  simpa only [Function.comp_def,id_eq] using computes
lemma run_pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (B : Finset (Fin n)) (label : Fin n→Fin m) : run (pack δ D S Δ s B label)=
      BinaryBlueItem.records (fun i=>i.val.bits) (fun i=>i.val.bits) B label
        (fun u v=>RationalSampling.assignmentWeight δ D S Δ s u*δ u v) := by
  unfold run
  rw [show field 1 (pack δ D S Δ s B label)=BinaryFinSet.encode B by simp [pack,field_encode]]
  simp only [BinaryFinSet.encode_eq,mapWith_encode,List.map_map,Function.comp_def,op_pack,BinaryBlueItem.records]
end MetricKMedianRecovery.BitMachine.BinaryBlueRecords

end OAI
