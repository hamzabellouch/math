import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.FiniteMachine
import OAI.Combinatorics.KMedianRecovery.Geometry.LocalSets

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
open WordOperations
lemma flatMapWith_map {α β : Type*} (f : List Bool→List Bool) (ctx : List Bool)
    (xs : List α) (enc : α→List Bool) (out : β→List Bool) (g : α→List β)
    (h : ∀ a∈xs,f (pairBits (ctx,enc a))=encode ((g a).map out)) :
    flatMapWith f (pairBits (ctx,encode (xs.map enc)))=encode ((xs.flatMap g).map out) := by
  simp only [flatMapWith,Function.comp_apply,mapWith_encode,Flatten.run_encode,List.map_map,
    Function.comp_def,List.map_flatMap,Flatten.encode_flatMap]
  congr 1
  exact List.map_congr_left h
end MetricKMedianRecovery.BitMachine.WordList

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCandidates
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryLocalSets
noncomputable def widths (w : ℕ) : List Bool→List Bool :=
  match w with
  | 0=>fun _=>encode [[]]
  | w+1=>fun x=>widths w x++flatMapWith insertEach (pairBits (widths w x,x))
noncomputable def widths_computes (w : ℕ) : PolyComputes (widths w) := by
  induction w with
  | zero=>exact const_computes _
  | succ w ih=>
    unfold widths
    have computes := ih.append ((ih.pair id_computes).comp (flatMapWith_computes insertEach_computes))
    simpa only [Function.comp_def,id_eq] using computes
lemma widths_pack {m : ℕ} (fs : List (Label (Fin m))) (w : ℕ) :
    widths w (labels fs)=encode ((LocalSearch.widthLists fs w).map setBits) := by
  induction w with
  | zero=>
    simp only [widths,LocalSearch.widthLists,List.map_cons,List.map_nil,setBits,labels,BinaryLabel.orderedSort,Finset.sort_empty]
    rfl
  | succ w ih=>
    simp only [widths,ih,LocalSearch.widthLists,List.map_append,encode_append]
    congr 1
    apply flatMapWith_map
    intro a _
    exact insertEach_pack _ a
noncomputable def sameSize (x : List Bool) : Bool := decide (value (size (extractPrefix x))=value (size (discardPrefix x)))
noncomputable def sameSize_computes : PolyComputes (fun x=>[sameSize x]) :=
  NatOps.eq (extractPrefix_computes.comp size_computes) (discardPrefix_computes.comp size_computes)
lemma sameSize_pack {m : ℕ} (S T : Finset (Label (Fin m))) :
    sameSize (pairBits (setBits S,setBits T))=decide (T.card=S.card) := by
  simp only [sameSize,extractPrefix_pairBits,discardPrefix_pairBits,size_pack,value_bits,eq_comm]
noncomputable def removed (w : ℕ) (x : List Bool) : List Bool :=
  mapWith diff (pairBits (discardPrefix x,widths w (extractPrefix x)))
noncomputable def removed_computes (w : ℕ) : PolyComputes (removed w) := by
  unfold removed
  have computes := (discardPrefix_computes.pair (extractPrefix_computes.comp (widths_computes w))).comp (mapWith_computes diff_computes)
  simpa only [Function.comp_def] using computes
lemma removed_pack {m : ℕ} (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) (w : ℕ) :
    removed w (pairBits (labels fs,setBits S))=encode (((LocalSearch.widthLists fs w).map (fun R=>S\R)).map setBits) := by
  simp only [removed,extractPrefix_pairBits,discardPrefix_pairBits,widths_pack,mapWith_encode,
    List.map_map,Function.comp_def,diff_pack]
noncomputable def raw (w : ℕ) (x : List Bool) : List Bool :=
  crossWith BinaryFiniteContext.union (pairBits (removed w x,widths w (extractPrefix x)))
noncomputable def raw_computes (w : ℕ) : PolyComputes (raw w) :=
  ((removed_computes w).pair (extractPrefix_computes.comp (widths_computes w))).comp
    (crossWith_computes BinaryFiniteContext.union_computes)
lemma raw_pack {m : ℕ} (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) (w : ℕ) :
    raw w (pairBits (labels fs,setBits S))=encode (((LocalSearch.widthLists fs w).flatMap
      (fun R=>(LocalSearch.widthLists fs w).map (fun A=>(S\R)∪A))).map setBits) := by
  simp only [raw,removed_pack,extractPrefix_pairBits,widths_pack,crossWith_encode,List.flatMap_map,
    List.map_map,Function.comp_def,BinaryFiniteContext.union_pack,List.map_flatMap]
noncomputable def run (w : ℕ) (x : List Bool) : List Bool :=
  filterWith sameSize (pairBits (discardPrefix x,raw w x))
noncomputable def run_computes (w : ℕ) : PolyComputes (run w) :=
  (discardPrefix_computes.pair (raw_computes w)).comp (filterWith_computes sameSize_computes)
lemma run_pack {m : ℕ} (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) (w : ℕ) :
    run w (pairBits (labels fs,setBits S))=encode ((LocalSearch.exchangeList fs S w).map setBits) := by
  simp only [run,discardPrefix_pairBits,raw_pack,filterWith_encode,List.filter_map,
    Function.comp_def,sameSize_pack,LocalSearch.exchangeList]
end MetricKMedianRecovery.BitMachine.BinaryLocalCandidates

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCost
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def entry (x : List Bool) : List Bool :=
  BinaryLabel.row (pairBits (pairBits (extractPrefix (extractPrefix x),discardPrefix x),discardPrefix (extractPrefix x)))
noncomputable def entry_computes : PolyComputes entry :=
  (((extractPrefix_computes.comp extractPrefix_computes).pair discardPrefix_computes).pair
    (extractPrefix_computes.comp discardPrefix_computes)).comp BinaryLabel.row_computes
lemma entry_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (j : Fin d) (a : Label (Fin m)) :
    entry (pairBits (pairBits (Rectangular.encode distance,j.val.bits),BinaryLabel.encode a))=
      BinaryRational.encode (rows distance a j) := by
  simp only [entry,extractPrefix_pairBits,discardPrefix_pairBits,BinaryLabel.row_pack]
noncomputable def near (x : List Bool) : List Bool := RationalMin.run
  (mapWith entry (pairBits (pairBits (field 0 (extractPrefix x),discardPrefix x),field 2 (extractPrefix x))))
noncomputable def near_computes : PolyComputes near := by
  unfold near
  have computes := ((((extractPrefix_computes.comp (field_computes 0)).pair discardPrefix_computes).pair
    (extractPrefix_computes.comp (field_computes 2))).comp (mapWith_computes entry_computes)).comp RationalMin.run_computes
  simpa only [Function.comp_def] using computes
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,setBits S]
def connection {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) (j : Fin d) : ℚ :=
  RationalMin.minimum ((BinaryLabel.orderedSort S).map (fun a=>rows distance a j))
lemma near_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) (j : Fin d) :
    near (pairBits (pack distance S,j.val.bits))=BinaryRational.encode (connection distance S j) := by
  simp only [near,extractPrefix_pairBits,discardPrefix_pairBits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [setBits,labels,mapWith_encode,List.map_map,Function.comp_def,entry_pack]
  simpa only [RationalArray.encode,List.map_map,Function.comp_def,connection] using
    RationalMin.run_encode ((BinaryLabel.orderedSort S).map (fun a=>rows distance a j))
noncomputable def run (x : List Bool) : List Bool := RationalArray.sumWords
  (mapWith near (pairBits (x,BinaryEllipsoidInitial.indices (field 1 x))))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := ((id_computes.pair ((field_computes 1).comp BinaryEllipsoidInitial.indices_computes)).comp
    (mapWith_computes near_computes)).comp RationalArray.sumWords_computes
  simpa only [Function.comp_def,id_eq] using computes
def cost {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) : ℚ := ∑ j,connection distance S j
lemma run_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) :
    run (pack distance S)=BinaryRational.encode (cost distance S) := by
  have hi : field 1 (pack distance S)=List.replicate d true := by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [run,hi,BinaryEllipsoidInitial.indices_replicate,mapWith_ofFn,near_pack]
  simpa only [RationalArray.encode,List.map_ofFn,Function.comp_def,List.sum_ofFn,cost] using
    RationalArray.sumWords_encode (List.ofFn (connection distance S))
noncomputable def rank (x : List Bool) : List Bool := (⌈BinaryRational.decode (run x)⌉₊).bits
noncomputable def rank_computes : PolyComputes rank := RatOps.natCeil (RatOps.ofWords run_computes)
lemma rank_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) :
    rank (pack distance S)=(⌈cost distance S⌉₊).bits := by rw [rank,run_pack,BinaryRational.decode_encode]
end MetricKMedianRecovery.BitMachine.BinaryLocalCost

end OAI
