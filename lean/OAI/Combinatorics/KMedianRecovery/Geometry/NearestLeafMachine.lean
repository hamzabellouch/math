import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplingReference
import OAI.Combinatorics.KMedianRecovery.Machines.MenuMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNearestLeaf
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
def leavesBits (zs : List (Fin n×ℚ)) : List Bool := encode (zs.map (fun z=>BinarySamplingReference.leafBits z.1 z.2))
noncomputable def distance (x : List Bool) : ℚ :=
  BinaryRational.decode (Lookup.run (pairBits (extractPrefix (discardPrefix x),extractPrefix x)))+
    BinaryRational.decode (discardPrefix (discardPrefix x))
noncomputable def distance_computes : PolyComputes (fun x=>BinaryRational.encode (distance x)) :=
  RatOps.add (RatOps.ofWords (((discardPrefix_computes.comp extractPrefix_computes).pair extractPrefix_computes).comp Lookup.run_computes))
    (RatOps.ofWords (discardPrefix_computes.comp discardPrefix_computes))
lemma distance_pair (row : Fin n→ℚ) (z : Fin n×ℚ) :
    distance (pairBits (RationalMatrix.rowEncode row,BinarySamplingReference.leafBits z.1 z.2))=row z.1+z.2 := by
  simp only [distance,BinarySamplingReference.leafBits,extractPrefix_pairBits,discardPrefix_pairBits,
    RationalMatrix.rowEncode_eq,lookup_ofFn,BinaryRational.decode_encode]
noncomputable def distances (x : List Bool) : List Bool := mapWith (fun z=>BinaryRational.encode (distance z)) x
noncomputable def distances_computes : PolyComputes distances := mapWith_computes distance_computes
lemma distances_pair (row : Fin n→ℚ) (zs : List (Fin n×ℚ)) :
    distances (pairBits (RationalMatrix.rowEncode row,leavesBits zs))=RationalArray.encode (zs.map (fun z=>row z.1+z.2)) := by
  simp only [distances,leavesBits,mapWith_encode,List.map_map,Function.comp_def,distance_pair,RationalArray.encode]
noncomputable def empty (x : List Bool) : Bool := decide (discardPrefix x=[])
noncomputable def empty_computes : PolyComputes (fun x=>[empty x]) := discardPrefix_computes.comp isEmpty_computes
noncomputable def run (x : List Bool) : List Bool :=
  if empty x then [] else encode [RationalMin.run (distances x)]
noncomputable def run_computes : PolyComputes run := by
  have computation := empty_computes.cond (const_computes [])
    (cons_computes (distances_computes.comp RationalMin.run_computes) (const_computes []))
  unfold run
  simpa only [Function.comp_def, encode] using computation
lemma run_pair (row : Fin n→ℚ) (zs : List (Fin n×ℚ)) :
    run (pairBits (RationalMatrix.rowEncode row,leavesBits zs))=
      BinaryMenu.optBits (if zs=[] then none else some (RationalMin.minimum (zs.map (fun z=>row z.1+z.2)))) := by
  simp only [run,empty,discardPrefix_pairBits,decide_eq_true_eq,distances_pair,RationalMin.run_encode]
  cases zs with
  | nil=>simp [leavesBits,encode,BinaryMenu.optBits]
  | cons z zs=>simp only [leavesBits,List.map_cons,encode,cons_ne_nil,ite_false,List.cons_ne_nil,BinaryMenu.optBits,
      Option.toList_some,List.map_cons,List.map_nil]
end MetricKMedianRecovery.BitMachine.BinaryNearestLeaf

end OAI
