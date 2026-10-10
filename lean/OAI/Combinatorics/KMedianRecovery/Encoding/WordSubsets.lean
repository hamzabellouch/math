import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Op2
import OAI.Combinatorics.KMedianRecovery.Machines.CappedFold

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Subsets
open WordOperations
variable {A : Type*}
def update (ss : List (List A)) (a : A) : List (List A) := ss++ss.map (fun s=>s++[a])
lemma fold_from (p xs : List A) : xs.foldl update p.sublists=(p++xs).sublists := by
  induction xs generalizing p with
  | nil=>simp
  | cons a xs ih=>
    rw [List.foldl_cons]
    change xs.foldl update (p.sublists++p.sublists.map (fun s=>s++[a]))=_
    rw [←List.sublists_concat,ih]
    simp only [List.append_assoc,List.singleton_append]
lemma fold_empty (xs : List A) : xs.foldl update [[]]=xs.sublists := by simpa using fold_from [] xs
noncomputable def addLast (x : List Bool) : List Bool := discardPrefix x++encode [extractPrefix x]
noncomputable def addLast_computes : PolyComputes addLast :=
  discardPrefix_computes.append (cons_computes extractPrefix_computes (const_computes []))
noncomputable def added (x : List Bool) : List Bool := mapWith addLast (pairBits (Find.item x,Fold.accum x))
noncomputable def added_computes : PolyComputes added := by
  unfold added
  simpa only [Function.comp_def] using
    (Find.item_computes.pair Fold.accum_computes).comp (mapWith_computes addLast_computes)
noncomputable def op (x : List Bool) : List Bool := Fold.accum x++added x
noncomputable def op_computes : PolyComputes op := Fold.accum_computes.append added_computes
lemma op_pack (ss : List (List (List Bool))) (a : List Bool) :
    op (pairBits ([],pairBits (a,encode (ss.map encode))))=encode ((update ss a).map encode) := by
  simp only [op,added,Fold.accum,Find.item,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    mapWith_encode,List.map_map,Function.comp_def,addLast,encode_append,update,List.map_append]
lemma length_encode_sublist (xs ys : List (List Bool)) (h : xs.Sublist ys) : (encode xs).length≤(encode ys).length := by
  induction h with
  | slnil=>rfl
  | @cons a xs ys h ih=>simp only [encode,length_cons];omega
  | @cons_cons a xs ys h ih=>simp only [encode,length_cons];omega
lemma encode_bound (ws : List (List Bool)) (B : ℕ) (h : ∀ w∈ws,w.length≤B) :
    (encode ws).length≤ws.length*(2*B+2) := by
  induction ws with
  | nil=>simp [encode]
  | cons w ws ih=>
    have hw:=h w (by simp)
    have ht:=ih (fun x hx=>h x (by simp [hx]))
    simp only [encode,length_cons,List.length_cons]
    nlinarith
lemma subset_bound (ws : List (List Bool)) :
    (encode (ws.sublists.map encode)).length≤2^ws.length*(2*(encode ws).length+2) := by
  have h:=encode_bound (ws.sublists.map encode) (encode ws).length (by
    intro w hw
    obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hw
    exact length_encode_sublist s ws (List.mem_sublists.mp hs))
  simpa only [List.length_map,List.length_sublists] using h
lemma prefix_bound (ws : List (List Bool)) (j : ℕ) :
    (encode ((ws.take j).sublists.map encode)).length≤2^ws.length*(2*(encode ws).length+2) := by
  apply (subset_bound (ws.take j)).trans
  apply Nat.mul_le_mul
  · exact Nat.pow_le_pow_right (by omega) (by simp only [List.length_take]; exact Nat.min_le_right ..)
  · have h:=length_encode_take ws j
    omega
noncomputable def cap (d : ℕ) : PolynomialCounter ((Polynomial.X+1)^d) := PolynomialCounter.choose _
noncomputable def run (d : ℕ) (x : List Bool) : List Bool :=
  CappedFold.run op (pairBits ((cap d).word x,Fold.pack (discardPrefix x) [] (encode [[]])))
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  ((cap d).computes.pair (Fold.pack_computes discardPrefix_computes (const_computes []) (const_computes (encode [[]])))).comp
    (CappedFold.run_computes op_computes)
lemma run_pack (d : ℕ) (ctx : List Bool) (ws : List (List Bool))
    (h : 2^ws.length*(2*(encode ws).length+2)≤((pairBits (ctx,encode ws)).length+1)^d) :
    run d (pairBits (ctx,encode ws))=encode (ws.sublists.map encode) := by
  unfold run
  rw [discardPrefix_pairBits]
  have hb (j : ℕ) : (encode (((ws.take j).foldl update [[]]).map encode)).length ≤ ((cap d).word (pairBits (ctx,encode ws))).length := by
    rw [fold_empty,(cap d).word_length]
    simp only [Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    exact (prefix_bound ws j).trans h
  have hh := CappedFold.run_typed (fun ss : List (List (List Bool))=>encode (ss.map encode)) id update op [] ((cap d).word (pairBits (ctx,encode ws))) op_pack [[]] ws hb
  simpa only [List.map_id,fold_empty,List.map_cons,List.map_nil,show encode ([] : List (List Bool))=[] from rfl] using hh
end MetricKMedianRecovery.BitMachine.WordList.Subsets

end OAI
