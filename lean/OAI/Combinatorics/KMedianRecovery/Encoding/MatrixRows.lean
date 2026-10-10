import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.WordTake

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows
open WordOperations WordList BinaryArithmetic
lemma slice_flatten {α : Type*} (xs : List (List α)) (n : ℕ) (h : ∀ x∈xs,x.length=n) (i : ℕ) :
    (xs.flatten.drop (n*i)).take n=(xs[i]?).getD [] := by
  induction xs generalizing i with
  | nil=>simp only [List.flatten_nil,List.drop_nil,List.take_nil,List.getElem?_nil,Option.getD_none]
  | cons x xs ih=>
    have hx:=h x List.mem_cons_self
    have ht : ∀ y∈xs,y.length=n := fun y hy=>h y (List.mem_cons_of_mem _ hy)
    cases i with
    | zero=>simp only [Nat.mul_zero,List.drop_zero,List.flatten_cons,List.getElem?_cons_zero,Option.getD_some]; rw [←hx,List.take_left]
    | succ i=>
      rw [Nat.mul_succ,Nat.add_comm,←List.drop_drop,List.flatten_cons,←hx,List.drop_left]
      simpa only [hx,List.getElem?_cons_succ] using ih ht i
noncomputable def offset (x : List Bool) : List Bool :=
  (value (UnaryResources.lengthBits (extractPrefix (extractPrefix x)))*value (discardPrefix x)).bits
noncomputable def offset_computes : PolyComputes offset :=
  NatOps.mul ((extractPrefix_computes.comp extractPrefix_computes).comp UnaryResources.lengthBits_computes) discardPrefix_computes
noncomputable def row (x : List Bool) : List Bool := Take.run (pairBits
  (UnaryResources.lengthBits (extractPrefix (extractPrefix x)),Drop.run (pairBits (offset x,discardPrefix (extractPrefix x)))))
attribute [local irreducible] offset Drop.run Take.run
noncomputable def row_computes : PolyComputes row :=
  (((extractPrefix_computes.comp extractPrefix_computes).comp UnaryResources.lengthBits_computes).pair
    ((offset_computes.pair (extractPrefix_computes.comp discardPrefix_computes)).comp Drop.run_computes)).comp Take.run_computes
noncomputable def run (x : List Bool) : List Bool :=
  mapWith row (pairBits (x,BinaryEllipsoidInitial.indices (extractPrefix x)))
attribute [local irreducible] mapWith
noncomputable def run_computes : PolyComputes run := by
  unfold run
  exact (id_computes.pair (extractPrefix_computes.comp BinaryEllipsoidInitial.indices_computes)).comp (mapWith_computes row_computes)
lemma row_pack (n : ℕ) (xs : List (List Bool)) (i : ℕ) :
    row (pairBits (pairBits (List.replicate n true,WordList.encode xs),i.bits))=
      WordList.encode ((xs.drop (n*i)).take n) := by
  simp only [row,offset,extractPrefix_pairBits,discardPrefix_pairBits,UnaryResources.lengthBits_eq,
    List.length_replicate,value_bits,Drop.run_encode,Take.run_encode]
lemma run_matrix {n : ℕ} (R : Fin n→Fin n→List Bool) :
    run (pairBits (List.replicate n true,WordList.encode ((List.ofFn (fun i=>List.ofFn (R i))).flatten)))=
      WordList.encode (List.ofFn (fun i=>WordList.encode (List.ofFn (R i)))) := by
  simp only [run,extractPrefix_pairBits,BinaryEllipsoidInitial.indices_replicate,mapWith_ofFn,row_pack]
  apply congrArg WordList.encode
  apply congrArg List.ofFn
  funext i
  apply congrArg WordList.encode
  rw [slice_flatten _ n (by intro x hx; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hx; exact List.length_ofFn) i,
    List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows

end OAI
