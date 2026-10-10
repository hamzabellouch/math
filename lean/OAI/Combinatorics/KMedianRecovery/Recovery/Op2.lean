import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.IfNat

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList.Flatten

def op (x : List Bool) : List Bool := Fold.accum x++Find.item x
noncomputable def op_computes : PolyComputes op := Fold.accum_computes.append Find.item_computes
lemma operation_eq (ctx a w : List Bool) : Fold.operation op ctx a w=a++w := by
  simp only [Fold.operation,op,Fold.accum,Find.item,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits]
lemma fold_eq (ws : List (List Bool)) (ctx a : List Bool) :
    ws.foldl (Fold.operation op ctx) a=a++ws.flatten := by
  induction ws generalizing a with
  | nil=>simp only [List.foldl_nil,List.flatten_nil,List.append_nil]
  | cons w ws ih=>simp only [List.foldl_cons,operation_eq,ih,List.flatten_cons,List.append_assoc]
lemma length_flatten_le (ws : List (List Bool)) : ws.flatten.length≤(encode ws).length := by
  induction ws with
  | nil=>rfl
  | cons w ws ih=>simp only [List.flatten_cons,List.length_append,encode,length_cons]; omega
noncomputable def run (x : List Bool) : List Bool := Fold.run op (3*Polynomial.X+3) (Fold.pack x [] [])
noncomputable def run_computes : PolyComputes run :=
  (Fold.pack_computes id_computes (const_computes []) (const_computes [])).comp
    (Fold.run_computes op_computes (3*Polynomial.X+3))
lemma run_encode (ws : List (List Bool)) : run (encode ws)=ws.flatten := by
  unfold run
  rw [Fold.run_encode op (3*Polynomial.X+3) [] [] ws (encode ws).length]
  · simp only [fold_eq,List.nil_append]
  · intro n
    simp only [fold_eq,List.nil_append]
    exact (length_flatten_le _).trans (length_encode_take ws n)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
lemma encode_flatMap {α : Type*} (ws : List α) (f : α → List (List Bool)) :
    encode (ws.flatMap f)=(ws.map (fun x=>encode (f x))).flatten := by
  induction ws with
  | nil=>rfl
  | cons a ws ih=>simp only [List.flatMap_cons,encode_append,List.map_cons,List.flatten_cons,ih]
end Flatten
noncomputable def flatMapWith (f : List Bool → List Bool) : List Bool → List Bool := Flatten.run ∘ mapWith f
noncomputable def flatMapWith_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (flatMapWith f) := (mapWith_computes hf).comp Flatten.run_computes
lemma flatMapWith_encode (f : List Bool → List Bool) (ctx : List Bool) (ws : List (List Bool))
    (g : List Bool → List (List Bool)) (h : ∀ w∈ws, f (pairBits (ctx,w))=encode (g w)) :
    flatMapWith f (pairBits (ctx,encode ws))=encode (ws.flatMap g) := by
  simp only [flatMapWith,Function.comp_apply,mapWith_encode,Flatten.run_encode,Flatten.encode_flatMap]
  congr 1
  apply List.map_congr_left
  exact h
end WordList
end MetricKMedianRecovery.BitMachine
namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList
noncomputable def crossWith (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  flatMapWith (fun w=>mapWith f (pairBits (discardPrefix w,extractPrefix w)))
    (pairBits (discardPrefix x,extractPrefix x))
noncomputable def crossWith_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (crossWith f) := by
  have mapComputes : PolyComputes
      (fun input=>mapWith f (pairBits (discardPrefix input,extractPrefix input))) := by
    simpa only [Function.comp_def] using
      (PolyComputes.comp (f:=fun input=>pairBits (discardPrefix input,extractPrefix input))
        (g:=mapWith f) (discardPrefix_computes.pair extractPrefix_computes) (mapWith_computes hf))
  unfold crossWith
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (discardPrefix input,extractPrefix input))
      (g:=flatMapWith (fun input=>mapWith f (pairBits (discardPrefix input,extractPrefix input))))
      (discardPrefix_computes.pair extractPrefix_computes) (flatMapWith_computes mapComputes))
lemma crossWith_encode (f : List Bool → List Bool) (xs ys : List (List Bool)) :
    crossWith f (pairBits (encode xs,encode ys))=
      encode (xs.flatMap (fun x=>ys.map (fun y=>f (pairBits (x,y))))) := by
  unfold crossWith
  simp only [extractPrefix_pairBits,discardPrefix_pairBits]
  apply flatMapWith_encode
  intro w _
  simp only [extractPrefix_pairBits,discardPrefix_pairBits,mapWith_encode]
noncomputable def cross : List Bool → List Bool := crossWith id
noncomputable def cross_computes : PolyComputes cross := crossWith_computes id_computes
lemma cross_encode (xs ys : List (List Bool)) :
    cross (pairBits (encode xs,encode ys))=encode (xs.flatMap (fun x=>ys.map (fun y=>pairBits (x,y)))) :=
  crossWith_encode id xs ys
end WordList
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma flatMap_ofFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : α → List β) :
    (List.ofFn f).flatMap g=(List.ofFn (fun j=>g (f j))).flatten := by
  change ((List.ofFn f).map g).flatten=_
  rw [List.map_ofFn]
  rfl
noncomputable def map (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  mapWith (f ∘ discardPrefix) (pairBits ([],x))
noncomputable def map_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (map f) := by
  unfold map
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],input)) (g:=mapWith (f ∘ discardPrefix))
      ((const_computes []).pair id_computes)
      (mapWith_computes (discardPrefix_computes.comp hf)))
lemma map_encode (f : List Bool → List Bool) (ws : List (List Bool)) :
    map f (encode ws)=encode (ws.map f) := by
  simp only [map,mapWith_encode,Function.comp_apply,discardPrefix_pairBits]
noncomputable def list_computes (fs : List (List Bool → List Bool)) (hs : ∀ f∈fs, PolyComputes f) :
    PolyComputes (fun x=>encode (fs.map (fun f=>f x))) := by
  induction fs with
  | nil=>exact const_computes []
  | cons f fs ih=>exact cons_computes (hs f (List.mem_cons_self ..)) (ih (fun g hg=>hs g (List.mem_cons_of_mem _ hg)))
end WordList
namespace BinaryOpeningEnumeration
open WordList EffectiveOpenability RationalOpenability BinaryOpeningPayment
noncomputable def clients : List Bool → List Bool := BinaryEllipsoidInitial.indices ∘ field 7
noncomputable def clients_computes : PolyComputes clients := (field_computes 7).comp BinaryEllipsoidInitial.indices_computes
noncomputable def doubles (x : List Bool) : List Bool := cross (pairBits (clients x,clients x))
noncomputable def doubles_computes : PolyComputes doubles := (clients_computes.pair clients_computes).comp cross_computes
noncomputable def triples (x : List Bool) : List Bool := cross (pairBits (field 8 x,doubles x))
noncomputable def triples_computes : PolyComputes triples := ((field_computes 8).pair doubles_computes).comp cross_computes
noncomputable def caps (x : List Bool) : List Bool := cross (pairBits (clients x,field 1 x))
noncomputable def caps_computes : PolyComputes caps := (clients_computes.pair (field_computes 1)).comp cross_computes
noncomputable def duals (x : List Bool) : List Bool := cross (pairBits (field 8 x,clients x))
noncomputable def duals_computes : PolyComputes duals := ((field_computes 8).pair clients_computes).comp cross_computes

def unaryTag (tag : ℕ) (x : List Bool) : List Bool := encode [tag.bits,x]
noncomputable def unaryTag_computes (tag : ℕ) : PolyComputes (unaryTag tag) :=
  cons_computes (const_computes tag.bits) (cons_computes id_computes (const_computes []))
def pairTag (tag : ℕ) (x : List Bool) : List Bool := encode [tag.bits,extractPrefix x,discardPrefix x]
noncomputable def pairTag_computes (tag : ℕ) : PolyComputes (pairTag tag) :=
  cons_computes (const_computes tag.bits)
    (cons_computes extractPrefix_computes (cons_computes discardPrefix_computes (const_computes [])))
def tripleTag (tag : ℕ) (x : List Bool) : List Bool :=
  encode [tag.bits,discardPrefix (discardPrefix x),extractPrefix x,extractPrefix (discardPrefix x)]
noncomputable def tripleTag_computes (tag : ℕ) : PolyComputes (tripleTag tag) :=
  cons_computes (const_computes tag.bits)
    (cons_computes (discardPrefix_computes.comp discardPrefix_computes)
      (cons_computes extractPrefix_computes (cons_computes (discardPrefix_computes.comp extractPrefix_computes) (const_computes []))))
def dualTag (x : List Bool) : List Bool := encode [(7:ℕ).bits,discardPrefix x,extractPrefix x]
noncomputable def dualTag_computes : PolyComputes dualTag :=
  cons_computes (const_computes (7:ℕ).bits)
    (cons_computes discardPrefix_computes (cons_computes extractPrefix_computes (const_computes [])))
def variableTag (x : List Bool) : List Bool :=
  encode [(1:ℕ).bits,extractPrefix x,extractPrefix (discardPrefix x),discardPrefix (discardPrefix x)]
noncomputable def variableTag_computes : PolyComputes variableTag :=
  cons_computes (const_computes (1:ℕ).bits)
    (cons_computes extractPrefix_computes (cons_computes (discardPrefix_computes.comp extractPrefix_computes)
      (cons_computes (discardPrefix_computes.comp discardPrefix_computes) (const_computes []))))
noncomputable def kinds (x : List Bool) : List Bool :=
  WordList.map (unaryTag 0) (clients x)++WordList.map (unaryTag 1) (clients x)++
  WordList.map (pairTag 2) (caps x)++WordList.map (unaryTag 3) (clients x)++
  encode [encode [(4:ℕ).bits]]++WordList.map (tripleTag 5) (triples x)++
  WordList.map (tripleTag 6) (triples x)++WordList.map dualTag (duals x)
noncomputable def kinds_computes : PolyComputes kinds := by
  have kindsComputes := (((((((clients_computes.comp (map_computes (unaryTag_computes 0))).append
    (clients_computes.comp (map_computes (unaryTag_computes 1)))).append
    (caps_computes.comp (map_computes (pairTag_computes 2)))).append
    (clients_computes.comp (map_computes (unaryTag_computes 3)))).append
    (const_computes (encode [encode [(4:ℕ).bits]]))).append
    (triples_computes.comp (map_computes (tripleTag_computes 5)))).append
    (triples_computes.comp (map_computes (tripleTag_computes 6)))).append
    (duals_computes.comp (map_computes dualTag_computes))
  unfold kinds
  simpa only [Function.comp_def] using kindsComputes
noncomputable def columns (x : List Bool) : List Bool :=
  WordList.map (unaryTag 0) (clients x)++WordList.map variableTag (triples x)
noncomputable def columns_computes : PolyComputes columns := by
  have columnsComputes := (clients_computes.comp (map_computes (unaryTag_computes 0))).append
    (triples_computes.comp (map_computes variableTag_computes))
  unfold columns
  simpa only [Function.comp_def] using columnsComputes

lemma clients_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : clients (pack distances F W v z lam eta i)=
      encode (List.ofFn (fun j : Fin d=>j.val.bits)) := by
  simp only [clients,Function.comp_apply,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryEllipsoidInitial.indices_replicate]
lemma kinds_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : kinds (pack distances F W v z lam eta i)=
      encode ((kindRows (List.ofFn (fun j : Fin d=>j)) (subtypeList W) (subtypeList F)).map BinaryOpeningConstant.kindWord) := by
  simp only [kinds,triples,doubles,caps,duals,clients_pack]
  simp only [pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryOpeningActivity.indices,
    List.map_map,Function.comp_def,cross_encode,map_encode,kindRows,List.map_append,List.map_cons,List.map_nil,
    encode_append,List.map_flatMap,List.map_flatten,List.flatMap_map,List.map_map,
    unaryTag,pairTag,tripleTag,dualTag,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryOpeningConstant.kindWord,List.map_ofFn,flatMap_ofFn]
lemma columns_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : columns (pack distances F W v z lam eta i)=
      encode (((List.ofFn (fun j : Fin d=>j)).map (fun j=>BinaryOpeningCoefficient.variableWord (F:=F) (.inl j)))++
        (subtypeList F).flatMap (fun f=>(List.ofFn (fun a : Fin d=>a)).flatMap (fun a=>
          (List.ofFn (fun j : Fin d=>j)).map (fun j=>BinaryOpeningCoefficient.variableWord (.inr (f,a,j)))))) := by
  simp only [columns,triples,doubles,clients_pack]
  simp only [pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryOpeningActivity.indices,
    List.map_map,Function.comp_def,cross_encode,map_encode,
    encode_append,List.map_flatMap,List.map_flatten,List.flatMap_map,List.map_map,
    unaryTag,variableTag,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryOpeningCoefficient.variableWord,List.map_ofFn,flatMap_ofFn]
end BinaryOpeningEnumeration
end MetricKMedianRecovery.BitMachine

end OAI
