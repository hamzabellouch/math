import Mathlib
import OAI.Computability.QuantumFactoring.BitStackListCode
import OAI.Computability.QuantumFactoring.BitStackBooleans
import OAI.Computability.QuantumFactoring.BitStackIteration

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

def listScan (f : α×β→β) : List α×β→List α×β
  | ([],b)=>([],b)
  | (a::as,b)=>(as,f (a,b))

lemma listScan_iterate (f : α×β→β) (i : ℕ) (xs : List α) (b : β) :
    (listScan f)^[i] (xs,b)=(xs.drop i,(xs.take i).foldl (fun b a=>f (a,b)) b) := by
  induction i generalizing xs b with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil=>simpa [listScan] using ih [] b
    | cons a as=>simpa [listScan] using ih as (f (a,b))

lemma listCode_length_drop_le (ea : α→List Bool) (i : ℕ) (xs : List α) :
    (listCode ea (xs.drop i)).length≤(listCode ea xs).length := by
  have hh:=listCode_length_append ea (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at hh
  have hp:=listCode_length_pos ea (xs.take i)
  omega

lemma listCode_length_take_le (ea : α→List Bool) (i : ℕ) (xs : List α) :
    (listCode ea (xs.take i)).length≤(listCode ea xs).length := by
  have hh:=listCode_length_append ea (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at hh
  have hp:=listCode_length_pos ea (xs.drop i)
  omega

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {f : α×β→β}
noncomputable def listScanP (d : α) (p : Procedure (prodCode ea eb) eb f) :
    Procedure (prodCode (listCode ea) eb) (prodCode (listCode ea) eb) (listScan f) := by
  let xs:=first (listCode ea) eb
  let b:=second (listCode ea) eb
  let upd:=((listTail ea).comp xs).pair (p.comp (((listHead ea d).comp xs).pair b))
  exact ((choose upd (identity (prodCode (listCode ea) eb))).comp
    (((listEmpty ea).comp xs).pair (identity (prodCode (listCode ea) eb)))).congrFun
      (by rintro ⟨xs,b⟩;cases xs <;> rfl)

noncomputable def foldList (d : α) (p : Procedure (prodCode ea eb) eb f)
    (bound : Polynomial ℕ)
    (hsize : ∀ (xs : List α) b i,
      (eb ((xs.take i).foldl (fun b a=>f (a,b)) b)).length≤
        bound.eval ((listCode ea xs).length+(eb b).length)) :
    Procedure (prodCode (listCode ea) eb) eb (fun x=>x.1.foldl (fun b a=>f (a,b)) x.2) := by
  let s:=listScanP d p
  let rep:=s.iterate (Polynomial.C 2*Polynomial.X+1+bound) (by
    intro n x i _
    rw [listScan_iterate]
    simp only [prodCode,pairBits_length]
    have hs:=hsize x.1 x.2 i
    have hl:=listCode_length_drop_le ea i x.1
    have hm:=eval_nat_mono bound (by omega :
      (listCode ea x.1).length+(eb x.2).length≤n+(2*(listCode ea x.1).length+(eb x.2).length+1))
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let wc:=(length.precompose (listCode ea)).comp (first (listCode ea) eb)
  exact ((second (listCode ea) eb).comp (rep.comp (wc.pair (identity (prodCode (listCode ea) eb))))).congrFun
    (by
      rintro ⟨xs,b⟩
      change ((listScan f)^[(listCode ea xs).length] (xs,b)).2=xs.foldl (fun b a=>f (a,b)) b
      rw [listScan_iterate,List.take_of_length_le (list_length_le_code ea xs)])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
