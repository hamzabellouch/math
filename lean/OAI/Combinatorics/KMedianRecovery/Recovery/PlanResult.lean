import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.CoupledLoop
import OAI.Combinatorics.KMedianRecovery.Machines.SensitiveMachine
import OAI.Combinatorics.KMedianRecovery.Machines.CoupledPrimitives

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPlanResult
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

def sf (n : ℕ) : List Bool→List Bool := field n ∘ field 0
noncomputable def sf_computes (n : ℕ) : PolyComputes (sf n) := (field_computes 0).comp (field_computes n)
def rf (n : ℕ) : List Bool→List Bool := field n ∘ field 3
noncomputable def rf_computes (n : ℕ) : PolyComputes (rf n) := (field_computes 3).comp (field_computes n)
noncomputable def success (x : List Bool) : Bool := decide (value (rf 0 x)=0)
noncomputable def success_computes : PolyComputes (fun x=>[success x]) := by
  simpa only [success,value_bits] using NatOps.eq (rf_computes 0) (const_computes (0:ℕ).bits)
noncomputable def rightHeight (x : List Bool) : List Bool := if success x then rf 1 x else rf 2 x
noncomputable def rightHeight_computes : PolyComputes rightHeight := success_computes.cond (rf_computes 1) (rf_computes 2)
noncomputable def price : List Bool→List Bool := field 7 ∘ sf 0
noncomputable def price_computes : PolyComputes price := (sf_computes 0).comp (field_computes 7)
noncomputable def root : List Bool→List Bool := field 1 ∘ sf 10
noncomputable def root_computes : PolyComputes root := (sf_computes 10).comp (field_computes 1)
noncomputable def common : List Bool→List Bool := BinarySensitive.common ∘ field 0
noncomputable def common_computes : PolyComputes common := (field_computes 0).comp BinarySensitive.common_computes
noncomputable def leafInput (x : List Bool) : List Bool := encode [field 1 x,field 2 x,price x,sf 3 x,root x,common x,rf 1 x,rightHeight x,rf 3 x,rf 4 x]
noncomputable def leafInput_computes : PolyComputes leafInput :=
  list_computes [field 1,field 2,price,sf 3,root,common,rf 1,rightHeight,rf 3,rf 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨field_computes 1⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨price_computes⟩
    · exact ⟨sf_computes 3⟩
    · exact ⟨root_computes⟩
    · exact ⟨common_computes⟩
    · exact ⟨rf_computes 1⟩
    · exact ⟨rightHeight_computes⟩
    · exact ⟨rf_computes 3⟩
    · exact ⟨rf_computes 4⟩)
noncomputable def finishInput (x : List Bool) : List Bool :=
  encode [BinaryCoupled.leafBank (leafInput x),price x,BinaryCoupled.leafPrefix (leafInput x),rf 3 x]
noncomputable def finishInput_computes : PolyComputes finishInput :=
  list_computes [BinaryCoupled.leafBank ∘ leafInput,price,BinaryCoupled.leafPrefix ∘ leafInput,rf 3] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨leafInput_computes.comp BinaryCoupled.leafBank_computes⟩
    · exact ⟨price_computes⟩
    · exact ⟨leafInput_computes.comp BinaryCoupled.leafPrefix_computes⟩
    · exact ⟨rf_computes 3⟩)
noncomputable def run (x : List Bool) : List Bool := if success x then
  pairBits ([],BinaryCoupled.finish (finishInput x)) else pairBits ([true],BinaryCoupled.leafResult (leafInput x))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using success_computes.cond
    ((const_computes []).pair (finishInput_computes.comp BinaryCoupled.finish_computes))
    ((const_computes [true]).pair (leafInput_computes.comp BinaryCoupled.leafResult_computes))
def pack {m : ℕ} (sensitive : List Bool) (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m))))
    (R : CanonicalLengthSearch.Result (Label (Fin m))) : List Bool := encode [sensitive,setBits B,historyBits P,BinaryLengthSearch.resultBits R]
lemma leafInput_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q B : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U P : List (List (Label (Fin m)))) (J : Plan (Label (Fin m)))
    (R : CanonicalLengthSearch.Result (Label (Fin m))) :
    leafInput (pack (BinarySensitive.pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J) B P R)=
      match R with
      | .success s W=>BinaryCoupled.leafPack B P lam key J.root (J.common H) s s W []
      | .bracket l u A Z=>BinaryCoupled.leafPack B P lam key J.root (J.common H) l u A Z := by
  have hc:=(BinarySensitive.views_pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J).1
  have hr:=(BinarySensitive.views_pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J).2.2.2
  simp only [BinarySensitive.jf,Function.comp_apply] at hr
  unfold leafInput common
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Function.comp_apply]
  rw [hc]
  simp only [root,sf,Function.comp_apply,field_encode,List.getElem?_cons_zero,Option.getD_some]
  rw [hr]
  cases R <;> simp only [price,sf,rf,rightHeight,success,Function.comp_apply,BinarySensitive.pack,BinaryFiniteContext.pack,
    BinaryLengthSearch.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    value_bits,decide_true,one_ne_zero,decide_false,ite_true,Bool.false_eq_true,ite_false,BinaryCoupled.leafPack]
  all_goals rfl
lemma run_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q B : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U P : List (List (Label (Fin m)))) (J : Plan (Label (Fin m)))
    (R : CanonicalLengthSearch.Result (Label (Fin m))) :
    run (pack (BinarySensitive.pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J) B P R)=
      BinaryCoupled.outcomeBits (match R with
      | .success s W=>.inl (CanonicalCoupledMerge.finish (insert (leaf key (parent J.root) s) B) lam (P++[J.common H++[leaf key (parent J.root) s]]) W)
      | .bracket l u A Z=>.inr (leafState B P lam key (parent J.root) (J.common H) l u A Z)) := by
  have hl:=leafInput_pack distance loc F Q B v z lam n q key b k N H T U P J R
  unfold run
  cases R with
  | success s W=>
    simp only [success,rf,Function.comp_apply,pack,BinaryLengthSearch.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,decide_true,ite_true] at *
    unfold finishInput
    rw [hl]
    simp only [price,sf,rf,Function.comp_apply,BinarySensitive.pack,BinaryFiniteContext.pack,
      field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
    have hu:=(BinaryCoupled.endLeaf_pack B P lam key J.root (J.common H) s s W []).2
    unfold BinaryCoupled.leafBank BinaryCoupled.leafPrefix
    rw [hu]
    simp only [BinaryCoupled.leafPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
    change pairBits ([],BinaryCoupled.finish (encode [BinaryFiniteContext.union (pairBits (setBits B,labels [leaf key (parent J.root) s])),_,_,_]))=_
    rw [BinaryFiniteContext.union_list_pack]
    simp only [List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty]
    rw [show historyBits P++cons (labels (J.common H)++cons (BinaryLabel.encode (leaf key (parent J.root) s)) []) []=
      historyBits (P++[J.common H++[leaf key (parent J.root) s]]) by
      rw [BinaryCoupled.historyBits_append,BinaryCoupled.historyBits_cons,BinaryFiniteContext.labels_append]; rfl]
    rw [BinaryCoupled.finish_pack]
    rfl
  | bracket l u A Z=>
    simp only [success,rf,Function.comp_apply,pack,BinaryLengthSearch.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,one_ne_zero,decide_false,Bool.false_eq_true,ite_false] at *
    rw [hl,BinaryCoupled.leafResult_pack]
    rfl
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
lemma original_order {m : ℕ} (a b : Fin m) : (a≤b) ↔ (@LE.le _ (labelLinearOrder.toLE) (original a) (original b)) := by
  rw [←not_lt,←not_lt,label_lt]
  simp [original,level,parent,rationalHeight]
lemma originalSort {m : ℕ} (F : Finset (Fin m)) :
    (F.sort (·≤·)).map original=BinaryLabel.orderedSort (F.image original) := by
  let f : Fin m↪Label (Fin m):=original
  have h:=Finset.map_sort f F (·≤·) (@LE.le _ (labelLinearOrder.toLE)) (fun a _ b _=>original_order a b)
  simpa only [f,Finset.map_eq_image,BinaryLabel.orderedSort] using h
noncomputable def copiedSet (x : List Bool) : List Bool := BinaryLabel.sort (mapWith BinaryLabel.copied x)
noncomputable def copiedSet_computes : PolyComputes copiedSet := (mapWith_computes BinaryLabel.copied_computes).comp BinaryLabel.sort_computes
lemma copiedSet_pack {m : ℕ} (key : ℕ) (S : Finset (Label (Fin m))) :
    copiedSet (pairBits (key.bits,setBits S))=setBits (S.image (copy key)) := by
  simp only [copiedSet,setBits,labels,mapWith_encode,List.map_map,Function.comp_def,BinaryLabel.copied_pack]
  rw [show (List.map (fun x=>BinaryLabel.encode (copy key x)) (BinaryLabel.orderedSort S)) =
    ((BinaryLabel.orderedSort S).map (copy key)).map BinaryLabel.encode by rw [List.map_map]; rfl]
  rw [BinaryLabel.sort_encode]
  apply congrArg (fun S : Finset (Label (Fin m))=>encode ((BinaryLabel.orderedSort S).map BinaryLabel.encode))
  ext a
  simp only [List.mem_toFinset,List.mem_map,BinaryLabel.orderedSort,Finset.mem_sort,Finset.mem_image]
noncomputable def pool (x : List Bool) : List Bool := union (pairBits (field 1 x,copiedSet (pairBits (field 2 x,field 0 x))))
noncomputable def pool_computes : PolyComputes pool :=
  ((field_computes 1).pair (((field_computes 2).pair (field_computes 0)).comp copiedSet_computes)).comp union_computes
lemma pool_pack {m : ℕ} (F B : Finset (Label (Fin m))) (key : ℕ) :
    pool (encode [setBits F,setBits B,key.bits])=setBits (PhaseMergePath.pool F B (copy key)) := by
  simp only [pool,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,copiedSet_pack,union_pack,PhaseMergePath.pool]
noncomputable def threeQ (x : List Bool) : List Bool := (3*value (field 2 x)).bits
noncomputable def threeQ_computes : PolyComputes threeQ := by
  change PolyComputes (fun x=>(3*value (field 2 x)).bits)
  simpa only [value_bits] using NatOps.mul (const_computes (3:ℕ).bits) (field_computes 2)
noncomputable def threeQOne (x : List Bool) : List Bool := (value (threeQ x)+1).bits
noncomputable def threeQOne_computes : PolyComputes threeQOne := by
  change PolyComputes (fun x=>(value (threeQ x)+1).bits)
  simpa only [value_bits] using NatOps.add threeQ_computes (const_computes (1:ℕ).bits)
noncomputable def bankFirst (x : List Bool) : List Bool := pool (encode [field 0 x,field 1 x,threeQ x])
noncomputable def bankFirst_computes : PolyComputes bankFirst :=
  (cons_computes (field_computes 0) (cons_computes (field_computes 1) (cons_computes threeQ_computes (const_computes [])))).comp pool_computes
noncomputable def banks (x : List Bool) : List Bool := pool (encode [field 0 x,bankFirst x,threeQOne x])
noncomputable def banks_computes : PolyComputes banks :=
  (cons_computes (field_computes 0) (cons_computes bankFirst_computes (cons_computes threeQOne_computes (const_computes [])))).comp pool_computes
lemma banks_pack {m : ℕ} (F : Finset (Fin m)) (B : Finset (Label (Fin m))) (q : ℕ) :
    banks (encode [setBits (F.image original),setBits B,q.bits])=setBits (CanonicalCoupledMerge.banks F B q) := by
  simp only [banks,bankFirst,threeQOne,threeQ,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,pool_pack,CanonicalCoupledMerge.banks]
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
