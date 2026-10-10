import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Score
import OAI.Combinatorics.KMedianRecovery.Branching.CategoricalScore

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)

def capped {E : Type*} (base : ℚ) (distance : E→ℚ) (S : Finset E) : ℚ := S.fold min base distance
lemma minimum_capped {E : Type*} [DecidableEq E] (b : ℚ) (d : E→ℚ) (xs : List E) :
    RationalMin.minimum (b::xs.map d)=capped b d xs.toFinset := by
  simp only [RationalMin.minimum,List.head?_cons,Option.getD_some,List.foldl_cons,min_self]
  rw [List.foldl_eq_foldr]
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.map_cons,List.foldr_cons,List.toFinset_cons,capped,Finset.fold_insert_idem] at *
    rw [ih]
lemma capped_cast {E : Type*} (b : ℚ) (d : E→ℚ) (S : Finset E) :
    (capped b d S:ℝ)=Completion.cappedCost (b:ℝ) (fun e=>(d e:ℝ)) S := by
  classical
  induction S using Finset.induction_on with
  | empty=>rfl
  | @insert e S he ih=>
    simp only [capped,Completion.cappedCost,Finset.fold_insert he,Rat.cast_min] at *
    rw [ih]

def rowBits {q : ℕ} (b : ℚ) (d : Fin q→ℚ) : List Bool :=
  encode [BinaryRational.encode b,encode (List.ofFn (fun e=>BinaryRational.encode (d e)))]
noncomputable def look (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,extractPrefix x))
noncomputable def look_computes : PolyComputes look :=
  (discardPrefix_computes.pair extractPrefix_computes).comp Lookup.run_computes
noncomputable def offers (x : List Bool) : List Bool :=
  mapWith look (pairBits (field 1 (discardPrefix x),extractPrefix x))
attribute [local irreducible] mapWith
noncomputable def offers_computes : PolyComputes offers := by
  unfold offers
  exact ((discardPrefix_computes.comp (field_computes 1)).pair extractPrefix_computes).comp (mapWith_computes look_computes)
lemma offers_pack {q : ℕ} (b : ℚ) (d : Fin q→ℚ) (xs : List (Fin q)) :
    offers (pairBits (encode (xs.map BinaryCategorical.elemBits),rowBits b d))=
      encode (xs.map (fun e=>BinaryRational.encode (d e))) := by
  simp only [offers,rowBits,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,mapWith_encode,List.map_map,
    Function.comp_def,look,BinaryCategorical.elemBits,lookup_ofFn]
noncomputable def cap (x : List Bool) : List Bool :=
  RationalMin.run (cons (field 0 (discardPrefix x)) (offers x))
noncomputable def cap_computes : PolyComputes cap :=
  (cons_computes (discardPrefix_computes.comp (field_computes 0)) offers_computes).comp RationalMin.run_computes
attribute [local irreducible] RationalMin.run
lemma cap_pack {q : ℕ} (b : ℚ) (d : Fin q→ℚ) (xs : List (Fin q)) :
    cap (pairBits (encode (xs.map BinaryCategorical.elemBits),rowBits b d))=
      BinaryRational.encode (capped b d xs.toFinset) := by
  unfold cap
  rw [offers_pack]
  simp only [discardPrefix_pairBits,rowBits,field_encode,List.getElem?_cons_zero,Option.getD_some]
  rw [show cons (BinaryRational.encode b) (encode (xs.map (fun e=>BinaryRational.encode (d e))))=
    RationalArray.encode (b::xs.map d) by
      simp only [RationalArray.encode,List.map_cons,List.map_map,Function.comp_def,encode]]
  rw [RationalMin.run_encode,minimum_capped]

def weightedRowBits {q : ℕ} (w b : ℚ) (d : Fin q→ℚ) : List Bool := pairBits (BinaryRational.encode w,rowBits b d)
noncomputable def weightedCap (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (extractPrefix (discardPrefix x))*
    BinaryRational.decode (cap (pairBits (extractPrefix x,discardPrefix (discardPrefix x)))))
noncomputable def weightedCap_computes : PolyComputes weightedCap :=
  RatOps.mul (RatOps.ofWords (discardPrefix_computes.comp extractPrefix_computes))
    (RatOps.ofWords ((extractPrefix_computes.pair (discardPrefix_computes.comp discardPrefix_computes)).comp cap_computes))
lemma weightedCap_pack {q : ℕ} (w b : ℚ) (d : Fin q→ℚ) (xs : List (Fin q)) :
    weightedCap (pairBits (encode (xs.map BinaryCategorical.elemBits),weightedRowBits w b d))=
      BinaryRational.encode (w*capped b d xs.toFinset) := by
  simp only [weightedCap,weightedRowBits,extractPrefix_pairBits,discardPrefix_pairBits,cap_pack,
    BinaryRational.decode_encode]
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
