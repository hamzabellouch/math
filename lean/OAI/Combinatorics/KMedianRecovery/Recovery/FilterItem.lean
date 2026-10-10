import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RowInput

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
noncomputable def filterItem (p : List Bool → Bool) (x : List Bool) : List Bool :=
  if p x then encode [discardPrefix x] else []
noncomputable def filterItem_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (filterItem p) := by
  have h := hp.cond (cons_computes discardPrefix_computes (const_computes [])) (const_computes [])
  change PolyComputes (fun x=>if p x then encode [discardPrefix x] else [])
  convert h using 1
  rfl
noncomputable def filterWith (p : List Bool → Bool) : List Bool → List Bool := flatMapWith (filterItem p)
noncomputable def filterWith_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (filterWith p) := flatMapWith_computes (filterItem_computes hp)
lemma filterWith_encode (p : List Bool → Bool) (ctx : List Bool) (ws : List (List Bool)) :
    filterWith p (pairBits (ctx,encode ws))=encode (ws.filter (fun w=>p (pairBits (ctx,w)))) := by
  unfold filterWith
  rw [flatMapWith_encode (filterItem p) ctx ws (fun w=>if p (pairBits (ctx,w)) then [w] else []) (by
    intro w _; simp only [filterItem,discardPrefix_pairBits]; split <;> rfl)]
  congr 1
  induction ws with
  | nil=>rfl
  | cons w ws ih=>cases h : p (pairBits (ctx,w)) <;> simp [h,ih]
end WordList
namespace BinaryFiniteInsert
open WordList BinaryPhaseFirst EffectiveOpenability
lemma canonical_list {m : ℕ} (W : Finset (Fin m)) :
    ((List.ofFn (fun i : Fin m=>i)).filter (fun i=>decide (i∈W)))=(subtypeList W).map Subtype.val := by
  apply List.Pairwise.eq_of_mem_iff (r:= (· < ·))
  · apply List.Pairwise.filter
    simp only [List.pairwise_ofFn]
    exact fun _ _ h=>h
  · simp only [subtypeList,List.map_ofFn,Function.comp_def,List.pairwise_ofFn]
    exact fun _ _ h=>(W.orderEmbOfFin rfl).strictMono h
  · intro i
    simp only [List.mem_filter,List.mem_ofFn,exists_apply_eq_apply,true_and,decide_eq_true_eq,List.mem_map]
    exact ⟨fun hi=>⟨⟨i,hi⟩,mem_subtypeList W _,rfl⟩,fun ⟨j,_,hj⟩=>hj ▸ j.property⟩

def old : List Bool → List Bool := extractPrefix ∘ extractPrefix
noncomputable def old_computes : PolyComputes old := extractPrefix_computes.comp extractPrefix_computes
def new : List Bool → List Bool := discardPrefix ∘ extractPrefix
noncomputable def new_computes : PolyComputes new := extractPrefix_computes.comp discardPrefix_computes
noncomputable def keep (x : List Bool) : Bool :=
  if natEq (pairBits (new x,discardPrefix x)) then true else contains (pairBits (discardPrefix x,old x))
noncomputable def keep_computes : PolyComputes (fun x=>[keep x]) := by
  have h := ((new_computes.pair discardPrefix_computes).comp natEq_computes).cond
    (const_computes [true]) ((discardPrefix_computes.pair old_computes).comp contains_computes)
  convert h using 1
  funext x
  cases he : natEq (pairBits (new x,discardPrefix x)) <;> simp only [keep,he,Function.comp_apply,Bool.false_eq_true,ite_false,ite_true]
lemma keep_pack {m : ℕ} (W : Finset (Fin m)) (i j : Fin m) :
    keep (pairBits (pairBits (BinaryOpeningActivity.indices ((subtypeList W).map Subtype.val),i.val.bits),j.val.bits))=
      decide (j∈insert i W) := by
  simp only [keep,old,new,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,natEq,
    value_bits,contains_finset,Finset.mem_insert,decide_eq_true_eq,← Fin.ext_iff]
  by_cases h : i=j <;> simp [h,eq_comm]
noncomputable def run : List Bool → List Bool := filterWith keep
noncomputable def run_computes : PolyComputes run := filterWith_computes keep_computes
lemma run_pack {m : ℕ} (W : Finset (Fin m)) (i : Fin m) :
    run (pairBits (pairBits (BinaryOpeningActivity.indices ((subtypeList W).map Subtype.val),i.val.bits),
      BinaryOpeningActivity.indices (List.ofFn (fun j : Fin m=>j))))=
      BinaryOpeningActivity.indices ((subtypeList (insert i W)).map Subtype.val) := by
  unfold run
  change filterWith keep (pairBits (pairBits (BinaryOpeningActivity.indices ((subtypeList W).map Subtype.val),i.val.bits),
    encode ((List.ofFn (fun j : Fin m=>j)).map (fun j=>j.val.bits))))=_
  rw [filterWith_encode]
  have hf : List.filter (fun w=>keep (pairBits (pairBits
      (BinaryOpeningActivity.indices ((subtypeList W).map Subtype.val),i.val.bits),w)))
      ((List.ofFn (fun j : Fin m=>j)).map (fun j=>j.val.bits))=
        (((List.ofFn (fun j : Fin m=>j)).filter (fun j=>decide (j∈insert i W))).map (fun j=>j.val.bits)) := by
    rw [List.filter_map]
    simp only [Function.comp_def,keep_pack]
  rw [hf,canonical_list]
  rfl
end BinaryFiniteInsert
end MetricKMedianRecovery.BitMachine

end OAI
