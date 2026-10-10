import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BranchPrefix
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoveryContext
import OAI.Combinatorics.KMedianRecovery.Geometry.MetricCost2

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] context zeroContext BinaryRandomizedBranch.Prefix.run BinaryRandomizedZeroBranch.Prefix.run
noncomputable def atBranch (d : ℕ) (x : List Bool) : List Bool :=
  BinaryRandomizedBranch.Prefix.run d (pairBits (context x,src 9 x))
noncomputable def atBranch_computes (d : ℕ) : PolyComputes (atBranch d) :=
  (context_computes.pair (src_computes 9)).comp (BinaryRandomizedBranch.Prefix.run_computes d)
noncomputable def promote (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (discardPrefix x,pairBits ([],[])))
noncomputable def promote_computes : PolyComputes promote := extractPrefix_computes.pair (discardPrefix_computes.pair (const_computes _))
noncomputable def atZero (x : List Bool) : List Bool :=
  BinaryRandomizedZeroBranch.Prefix.run (pairBits (zeroContext (promote x),src 9 x))
noncomputable def atZero_computes : PolyComputes atZero :=
  ((promote_computes.comp zeroContext_computes).pair (src_computes 9)).comp BinaryRandomizedZeroBranch.Prefix.run_computes
noncomputable def range (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (field 6 x++[true])
noncomputable def range_computes : PolyComputes range := ((field_computes 6).append (const_computes _)).comp BinaryEllipsoidInitial.indices_computes
noncomputable def blueRange (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (field 7 x)
noncomputable def blueRange_computes : PolyComputes blueRange := (field_computes 7).comp BinaryEllipsoidInitial.indices_computes
noncomputable def choices (x : List Bool) : List Bool := cross (pairBits (range x,cross (pairBits (range x,blueRange x))))
noncomputable def choices_computes : PolyComputes choices :=
  (range_computes.pair ((range_computes.pair blueRange_computes).comp cross_computes)).comp cross_computes
noncomputable def candidateWords (d : ℕ) (x : List Bool) : List Bool :=
  mapWith atZero (pairBits (x,range x))++ mapWith (atBranch d) (pairBits (x,choices x))
attribute [local irreducible] mapWith
noncomputable def candidateWords_computes (d : ℕ) : PolyComputes (candidateWords d) :=
  (PolyComputes.comp (f := fun input=>pairBits (input,range input)) (g := mapWith atZero)
    (id_computes.pair range_computes) (mapWith_computes atZero_computes)).append
    (PolyComputes.comp (f := fun input=>pairBits (input,choices input)) (g := mapWith (atBranch d))
      (id_computes.pair choices_computes) (mapWith_computes (atBranch_computes d)))
noncomputable def metricContext (x : List Bool) : List Bool := encode [field 0 x,field 1 x]
noncomputable def metricContext_computes : PolyComputes metricContext := cons_computes (field_computes 0) (cons_computes (field_computes 1) (const_computes []))
noncomputable def run (d : ℕ) (x : List Bool) : List Bool := BinaryMetricBest.run
  (pairBits (metricContext x,pairBits (field 3 x,candidateWords d x)))
attribute [local irreducible] metricContext candidateWords
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  (metricContext_computes.pair ((field_computes 3).pair (candidateWords_computes d))).comp BinaryMetricBest.run_computes
section Exact
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool)
local notation "data" => pack δ D F S Δ s m extra raw
lemma range_pack : range data=encode (List.ofFn (fun q:Fin (n+1)=>q.val.bits)) := by
  simp only [range,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    ←List.replicate_one (a:=true),←List.replicate_add,BinaryEllipsoidInitial.indices_replicate]
lemma blueRange_pack : blueRange data=encode (List.ofFn (fun b:Fin m=>b.val.bits)) := by
  simp only [blueRange,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryEllipsoidInitial.indices_replicate]
lemma choices_pack : choices data=encode ((List.ofFn (fun q:Fin (n+1)=>q)).flatMap (fun q=>
    (List.ofFn (fun c:Fin (n+1)=>c)).flatMap (fun c=>List.ofFn (fun b:Fin m=>choiceBits q.val c.val b.val)))) := by
  rw [choices,range_pack,blueRange_pack,cross_encode,cross_encode]
  simp only [flatMap_ofFn,List.map_flatten,List.map_ofFn,Function.comp_def,choiceBits]
lemma candidateWords_pack (d : ℕ) : candidateWords d data=encode
    ((List.ofFn (fun q:Fin (n+1)=>atZero (pairBits (data,q.val.bits))))++
      (List.ofFn (fun q:Fin (n+1)=>q)).flatMap (fun q=>(List.ofFn (fun c:Fin (n+1)=>c)).flatMap
        (fun c=>List.ofFn (fun b:Fin m=>atBranch d (pairBits (data,choiceBits q.val c.val b.val)))))) := by
  rw [candidateWords,range_pack,choices_pack,mapWith_ofFn,mapWith_encode,←encode_append]
  simp only [List.map_flatMap,List.map_ofFn,Function.comp_def]
lemma metricContext_pack : metricContext data=BinaryMetricBest.context δ D := by
  simp only [metricContext,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryMetricBest.context]
lemma run_of_candidates (d : ℕ) (xs : List (Finset (Fin n)))
    (hxs : candidateWords d data=encode (xs.map BinaryFinSet.encode)) :
    run d data=BinaryFinSet.encode (BinaryMetricBest.best δ D S xs) := by
  rw [run,metricContext_pack,hxs]
  have he : field 3 data=BinaryFinSet.encode S := by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [he]
  exact BinaryMetricBest.run_pack δ D S xs
end Exact
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
