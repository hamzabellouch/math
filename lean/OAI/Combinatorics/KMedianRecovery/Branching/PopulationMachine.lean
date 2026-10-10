import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FilterItem

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPopulation
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] WordList.mapWith
def near (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix x)≤BinaryRational.decode (extractPrefix x))
noncomputable def near_computes : PolyComputes (fun x=>[near x]) :=
  RatOps.le (RatOps.ofWords discardPrefix_computes) (RatOps.ofWords extractPrefix_computes)
noncomputable def count (x : List Bool) : List Bool :=
  UnaryResources.lengthBits (Count.run (filterWith near x))
noncomputable def count_computes : PolyComputes count :=
  ((filterWith_computes near_computes).comp Count.run_computes).comp UnaryResources.lengthBits_computes
lemma count_pack (q : ℚ) (ds : List ℚ) :
    count (pairBits (BinaryRational.encode q,RationalArray.encode ds))=(ds.filter (fun d=>decide (d≤q))).length.bits := by
  simp only [count,RationalArray.encode,filterWith_encode,List.filter_map,near,extractPrefix_pairBits,
    discardPrefix_pairBits,Function.comp_def,BinaryRational.decode_encode,Count.run_encode,List.length_map,UnaryResources.lengthBits_eq,List.length_replicate]
noncomputable def candidate (x : List Bool) : ℚ :=
  max (BinaryRational.decode (discardPrefix x))
    (BinaryRational.decode (field 0 (extractPrefix x)) /
      ((value (field 1 (extractPrefix x)):ℚ)*value (count (pairBits (discardPrefix x,field 2 (extractPrefix x))))))
noncomputable def candidate_computes : PolyComputes (fun x=>BinaryRational.encode (candidate x)) :=
  RatOps.max (RatOps.ofWords discardPrefix_computes)
    (RatOps.div (RatOps.ofWords (extractPrefix_computes.comp (field_computes 0)))
      (RatOps.mul (RatOps.nat (extractPrefix_computes.comp (field_computes 1)))
        (RatOps.nat ((discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp count_computes))))
def pack (P : ℚ) (m : ℕ) (ds : List ℚ) : List Bool :=
  encode [BinaryRational.encode P,m.bits,RationalArray.encode ds]
def candidateQ (P : ℚ) (m : ℕ) (ds : List ℚ) (d : ℚ) : ℚ :=
  max d (P / ((m:ℚ)*(ds.filter (fun t=>decide (t≤d))).length))
lemma candidate_pack (P d : ℚ) (m : ℕ) (ds : List ℚ) :
    candidate (pairBits (pack P m ds,BinaryRational.encode d))=candidateQ P m ds d := by
  simp only [candidate,pack,candidateQ,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryRational.decode_encode,count_pack,value_bits]
noncomputable def candidates (x : List Bool) : List Bool :=
  mapWith (fun z=>BinaryRational.encode (candidate z)) (pairBits (x,field 2 x))
noncomputable def candidates_computes : PolyComputes candidates :=
  (id_computes.pair (field_computes 2)).comp (mapWith_computes candidate_computes)
def radiusQ (P : ℚ) (m : ℕ) (ds : List ℚ) : ℚ := RationalMin.minimum (ds.map (candidateQ P m ds))
lemma candidates_pack (P : ℚ) (m : ℕ) (ds : List ℚ) :
    candidates (pack P m ds)=RationalArray.encode (ds.map (candidateQ P m ds)) := by
  unfold candidates
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  change mapWith (fun z=>BinaryRational.encode (candidate z)) (pairBits (pack P m ds,RationalArray.encode ds))=_
  simp only [RationalArray.encode,mapWith_encode,List.map_map,Function.comp_def,candidate_pack]
noncomputable def run (x : List Bool) : List Bool := RationalMin.run (candidates x)
noncomputable def run_computes : PolyComputes run := candidates_computes.comp RationalMin.run_computes
lemma run_pack (P : ℚ) (m : ℕ) (ds : List ℚ) : run (pack P m ds)=BinaryRational.encode (radiusQ P m ds) := by
  rw [run,candidates_pack,RationalMin.run_encode]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
