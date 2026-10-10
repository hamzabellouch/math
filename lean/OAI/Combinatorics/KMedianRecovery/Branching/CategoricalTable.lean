import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Op2
import OAI.Combinatorics.KMedianRecovery.Recovery.Advance

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {E : Type*} {a T : ℕ}
def optionBits (enc : E→List Bool) (o : Option E) : List Bool := encode (o.toList.map enc)
def tableBits (enc : E→List Bool) (r : Fin a→Fin T→Option E) : List Bool :=
  encode (List.ofFn (fun j=>encode (List.ofFn (fun t=>optionBits enc (r j t)))))
def choicesBits (enc : E→List Bool) (c : Fin a→E) : List Bool := encode (List.ofFn (fun j=>enc (c j)))
def seedBits (s : Fin a→Fin T) : List Bool := encode (List.ofFn (fun j=>(s j).val.bits))
def drawPack (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) : List Bool :=
  encode [tableBits enc r,seedBits s,skip.bits]
noncomputable def drawItems (x : List Bool) : List Bool := Zip.run (pairBits (Indices.run (field 1 x),field 1 x))
noncomputable def drawItems_computes : PolyComputes drawItems :=
  (((field_computes 1).comp Indices.run_computes).pair (field_computes 1)).comp Zip.run_computes
noncomputable def drawRow (x : List Bool) : List Bool :=
  Lookup.run (pairBits (extractPrefix (discardPrefix x),field 0 (extractPrefix x)))
noncomputable def drawRow_computes : PolyComputes drawRow :=
  ((discardPrefix_computes.comp extractPrefix_computes).pair
    (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes
noncomputable def drawPick (x : List Bool) : List Bool :=
  if value (extractPrefix (discardPrefix x))=value (field 2 (extractPrefix x)) then []
  else Lookup.run (pairBits (discardPrefix (discardPrefix x),drawRow x))
noncomputable def drawPick_computes : PolyComputes drawPick := by
  have h := (NatOps.eq (discardPrefix_computes.comp extractPrefix_computes)
    (extractPrefix_computes.comp (field_computes 2))).cond (const_computes [])
    (((discardPrefix_computes.comp discardPrefix_computes).pair drawRow_computes).comp Lookup.run_computes)
  unfold drawPick
  simpa only [decide_eq_true_eq,Function.comp_def] using h
noncomputable def draw (x : List Bool) : List Bool := flatMapWith drawPick (pairBits (x,drawItems x))
noncomputable def draw_computes : PolyComputes draw := (id_computes.pair drawItems_computes).comp (flatMapWith_computes drawPick_computes)
def omitted (r : Fin a→Fin T→Option E) (skip : ℕ) : Fin a→Fin T→Option E :=
  fun j t=>if j.val=skip then none else r j t
def drawn (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) : List E :=
  (List.ofFn (fun j=>(r j (s j)).toList)).flatten
lemma drawPick_pack (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) (j : Fin a) :
    drawPick (pairBits (drawPack enc r s skip,pairBits (j.val.bits,(s j).val.bits)))=
      optionBits enc (omitted r skip j (s j)) := by
  simp only [drawPick,drawRow,drawPack,tableBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,lookup_ofFn,omitted]
  split_ifs <;> rfl
lemma drawItems_pack (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) :
    drawItems (drawPack enc r s skip)=encode (List.ofFn (fun j=>pairBits (j.val.bits,(s j).val.bits))) := by
  simp only [drawItems,drawPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,seedBits,indices_ofFn,Zip.run_encode,zip_ofFn,List.map_ofFn,Function.comp_def]
lemma encode_flatten (wss : List (List (List Bool))) : encode wss.flatten=(wss.map encode).flatten := by
  induction wss with
  | nil=>rfl
  | cons ws wss ih=>simp only [List.flatten_cons,encode_append,List.map_cons,ih]
lemma draw_pack (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) :
    draw (drawPack enc r s skip)=encode ((drawn (omitted r skip) s).map enc) := by
  rw [draw,drawItems_pack]
  simp only [flatMapWith,Function.comp_apply,mapWith_ofFn,drawPick_pack,optionBits,Flatten.run_encode,
    drawn,List.map_flatten,encode_flatten,List.map_ofFn,Function.comp_def]
lemma drawn_toFinset [DecidableEq E] (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) :
    (drawn r s).toFinset=Categorical.draw a r s ∅ := by
  ext e
  simp only [drawn,List.mem_toFinset,List.mem_flatten,List.mem_ofFn,
    Categorical.mem_draw,Finset.notMem_empty,false_or]
  aesop
lemma omitted_update (r : Fin a→Fin T→Option E) (j : Fin a) :
    omitted r j.val=Function.update r j (fun _=>none) := by
  funext i t
  by_cases hi : i=j
  · subst i; simp [omitted]
  · have hv : i.val≠j.val:=fun h=>hi (Fin.ext h)
    simp only [omitted,ite_eq_right hv,Function.update_of_ne hi]
lemma omitted_end (r : Fin a→Fin T→Option E) : omitted r a=r := by
  funext j t
  exact ite_eq_right (Nat.ne_of_lt j.isLt)

def advancePack (enc : E→List Bool) (r : Fin a→Fin T→Option E) (t : Fin T) (c : Fin a→E) : List Bool :=
  encode [tableBits enc r,choicesBits enc c,t.val.bits]
noncomputable def advanceItem (x : List Bool) : List Bool :=
  Set.run (Set.pack (Lookup.run (pairBits (discardPrefix x,field 0 (extractPrefix x))))
    (field 2 (extractPrefix x)) (encode [Lookup.run (pairBits (discardPrefix x,field 1 (extractPrefix x)))]))
attribute [local irreducible] Set.run mapWith
noncomputable def advanceItem_computes : PolyComputes advanceItem := by
  unfold advanceItem
  have h0 := (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes
  have h1 := (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 1))).comp Lookup.run_computes
  exact (h0.pair ((extractPrefix_computes.comp (field_computes 2)).pair
    (cons_computes h1 (const_computes [])))).comp Set.run_computes
noncomputable def advance (x : List Bool) : List Bool :=
  mapWith advanceItem (pairBits (x,Indices.run (field 1 x)))
noncomputable def advance_computes : PolyComputes advance := by
  unfold advance
  exact (id_computes.pair ((field_computes 1).comp Indices.run_computes)).comp (mapWith_computes advanceItem_computes)
lemma advanceItem_pack (enc : E→List Bool) (r : Fin a→Fin T→Option E) (t : Fin T) (c : Fin a→E) (j : Fin a) :
    advanceItem (pairBits (advancePack enc r t c,j.val.bits))=
      encode (List.ofFn (fun ω=>optionBits enc (Categorical.advance r t c j ω))) := by
  simp only [advanceItem,advancePack,tableBits,choicesBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn]
  rw [Set.run_ofFn]
  apply congrArg encode
  apply congrArg List.ofFn
  funext ω
  by_cases hω : ω=t
  · subst ω; simp only [↓reduceIte,Categorical.advance,Function.update_self,optionBits,Option.toList_some,List.map_singleton]
  · simp only [ite_eq_right hω,Categorical.advance,Function.update_of_ne hω]
lemma advance_pack (enc : E→List Bool) (r : Fin a→Fin T→Option E) (t : Fin T) (c : Fin a→E) :
    advance (advancePack enc r t c)=tableBits enc (Categorical.advance r t c) := by
  simp only [advance,advancePack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    choicesBits,indices_ofFn,mapWith_ofFn]
  change encode (List.ofFn (fun j=>advanceItem (pairBits (advancePack enc r t c,j.val.bits))))=_
  simp only [advanceItem_pack,tableBits]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
