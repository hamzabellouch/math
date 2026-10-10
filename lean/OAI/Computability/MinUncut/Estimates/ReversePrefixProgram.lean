import Mathlib
import OAI.Computability.MinUncut.Search.BlockEnumeration

namespace OAI

namespace MinUncut.Costed
open Turing.ToPartrec Polynomial Arena

def prefixStep (v : List ℕ) : List ℕ :=
  (v.headI+1)::((v.drop (2*v.headI+1)).headI)::v.tail

noncomputable def prefixStepProgram : PolyProgram prefixStep :=
  PolyProgram.succ.cons (((Expr.at (.add (.mul (.const 2) (.reg 0)) (.const 1))).program).cons PolyProgram.tail)

lemma prefixStep_safe (v : List ℕ) :
    (prefixStep v).length≤v.length+2 ∧ maximum (prefixStep v)≤ maximum v+1 := by
  have h0 := head_le_maximum v
  have ha := (head_le_maximum (v.drop (2*v.headI+1))).trans (maximum_drop v _)
  have ht := maximum_drop v 1
  have hl : v.tail.length≤v.length := by cases v <;> simp
  rw [List.drop_one] at ht
  simp only [prefixStep,List.length_cons,maximum_cons]
  exact ⟨by omega,max_le (by omega) (max_le (by omega) (by omega))⟩

noncomputable def reversePrefixProgram : PolyProgram
    (fun v=>(prefixStep^[v.headI] (0::v.tail)).tail) :=
  PolyProgram.tail.comp ((Arena.PolyProgram.safeIterate prefixStepProgram 2 1 prefixStep_safe).comp
    (PolyProgram.head.cons ((PolyProgram.const 0).cons PolyProgram.tail)))

lemma prefixStep_iter (xs rest : List ℕ) (i : ℕ) (hi : i≤xs.length) :
    prefixStep^[i] (0::(xs++rest))=i::((xs.take i).reverse++xs++rest) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hil : i<xs.length := by omega
    rw [Function.iterate_succ_apply',ih (by omega)]
    have hd : (((i::((xs.take i).reverse++xs++rest)).drop (2*i+1)).headI)=xs[i] := by
      have hlen : (xs.take i).reverse.length=i := by simp [Nat.min_eq_left (by omega : i≤xs.length)]
      have h1 : (i::((xs.take i).reverse++xs++rest)).drop (i+1)=xs++rest := by
        rw [List.drop_succ_cons]
        calc
          _ = (((xs.take i).reverse++xs++rest).drop (xs.take i).reverse.length) := by rw [hlen]
          _ = xs++rest := by rw [List.append_assoc,List.drop_left]
      rw [show 2*i+1=(i+1)+i by omega,←List.drop_drop,h1]
      have hk : ((xs++rest).drop i).headI=xs[i] := by
        rw [List.drop_append_of_le_length (by omega)]
        rw [List.drop_eq_getElem_cons hil]
        rfl
      exact hk
    simp only [prefixStep,List.headI_cons,List.tail_cons,hd]
    congr 1
    rw [List.take_succ_eq_append_getElem hil,List.reverse_append]
    rfl

lemma reversePrefix_spec (xs rest : List ℕ) :
    (prefixStep^[xs.length] (0::(xs++rest))).tail=xs.reverse++xs++rest := by
  rw [prefixStep_iter xs rest xs.length (le_refl _),List.tail_cons,List.take_length]

end MinUncut.Costed

namespace MinUncut.Costed.Blocks
noncomputable section

def emitted (es : List AExpr) (n : ℕ) (v : List ℕ) : List ℕ :=
  (List.range n).flatMap (fun i=>block es i v)
def retained (es : List AExpr) (n : ℕ) (v : List ℕ) : List ℕ :=
  (emitted es n v).reverse++v

lemma block_reverse (es : List AExpr) (i : ℕ) (v : List ℕ) :
    block es.reverse i v=(block es i v).reverse := by
  simp only [block,List.map_reverse]
lemma enumerate_reverse (es : List AExpr) (n : ℕ) (v : List ℕ) :
    (List.range n).reverse.flatMap (fun i=>block es.reverse i v)=(emitted es n v).reverse := by
  simp only [emitted,List.reverse_flatMap,Function.comp_def,block_reverse]
lemma length_emitted (es : List AExpr) (n : ℕ) (v : List ℕ) :
    (emitted es n v).length=n*es.length := by
  simp only [emitted,List.length_flatMap,length_block,List.map_const',List.length_range,
    List.sum_replicate,nsmul_eq_mul,Nat.cast_id]

def forward (es : List AExpr) (N : AExpr) : PolyProgram (fun v=>
    emitted es (N.eval v) v++retained es (N.eval v) v) :=
  (reversePrefixProgram.comp (PolyProgram.tail.comp (enumerate es.reverse N))).ofEq (by
    intro v
    simp only [Function.comp_def,List.tail_cons,enumerate_reverse,List.length_reverse,
      List.headI_cons]
    rw [←show (emitted es (N.eval v) v).reverse.length=N.eval v*es.length by
      simp only [List.length_reverse,length_emitted]]
    rw [reversePrefix_spec,List.reverse_reverse]
    exact List.append_assoc _ _ _)

end
end MinUncut.Costed.Blocks

end OAI
