import Mathlib
import OAI.Computability.QuantumFactoring.BitStackIteration
import OAI.Computability.QuantumFactoring.BitStackListOps
import OAI.Computability.QuantumFactoring.BitStackNaturals

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def tabStep (f : α→ℕ→β) (s : ℕ×(α×List β)) : ℕ×(α×List β) :=
  (s.1+1,s.2.1,f s.2.1 s.1::s.2.2)
def tabCode (ea : α→List Bool) (eb : β→List Bool) := prodCode unaryCode (prodCode ea (listCode eb))
lemma tabStep_iterate (f : α→ℕ→β) (j i : ℕ) (a : α) (ys : List β) :
    (tabStep f)^[j] (i,a,ys)=(i+j,a,((List.range' i j).map (f a)).reverse++ys) := by
  induction j with
  | zero=>simp
  | succ j ih=>
    rw [Function.iterate_succ_apply',ih]
    simp only [tabStep,List.range'_1_concat,List.map_append,List.map_cons,List.map_nil,
      List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
    simp only [Nat.add_assoc]
namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {f : α→ℕ→β}
noncomputable def tabStepP (p : Procedure (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Procedure (tabCode ea eb) (tabCode ea eb) (tabStep f) := by
  let i:=first unaryCode (prodCode ea (listCode eb))
  let rest:=second unaryCode (prodCode ea (listCode eb))
  let a:=(first ea (listCode eb)).comp rest
  let ys:=(second ea (listCode eb)).comp rest
  exact ((unarySuccessor.comp i).pair
    (a.pair ((listCons eb).comp ((p.comp (i.pair a)).pair ys)))).congrFun (by intro s;rfl)
noncomputable def tabulate (d : β)
    (p : Procedure (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Procedure (prodCode unaryCode ea) (listCode eb)
      (fun x=>(List.range x.1).map (f x.2)) := by
  let q:=(Polynomial.X+p.bound).comp (Polynomial.C 2*Polynomial.X+1)
  have hval (a : α) (i : ℕ) : (eb (f a i)).length≤q.eval (i+(ea a).length) := by
    have ho:=p.output_length_le (i,a)
    have hm:=eval_nat_mono (Polynomial.X+p.bound)
      (show (prodCode unaryCode ea (i,a)).length≤2*(i+(ea a).length)+1 by
        simp only [prodCode,pairBits_length,unaryCode,List.length_replicate];omega)
    simp only [Polynomial.eval_add,Polynomial.eval_X] at hm
    simpa only [q,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one] using ho.trans hm
  let rep:=(tabStepP p).iterate (Polynomial.X*(Polynomial.C 2*q+Polynomial.C 5)) (by
    rintro n ⟨i,a,ys⟩ j hj
    rw [tabStep_iterate]
    have len0 : (tabCode ea eb (i,a,ys)).length=2*i+2*(ea a).length+(listCode eb ys).length+2 := by
      simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate];omega
    have hv : ∀ k∈List.range' i j,(eb (f a k)).length≤q.eval (n+(tabCode ea eb (i,a,ys)).length) := by
      intro k hk
      have hk':=List.mem_range'.mp hk
      exact (hval a k).trans (eval_nat_mono q (by rw [len0];omega))
    have hmap:=listCode_length_map_bound eb (f a) (List.range' i j) _ hv
    have happ:=listCode_length_append eb (((List.range' i j).map (f a)).reverse) ys
    rw [listCode_length_rev] at happ
    simp only [List.length_range'] at hmap
    simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X] at *
    nlinarith)
  let inputN:=first unaryCode ea
  let inputA:=second unaryCode ea
  let start:=(constant (prodCode unaryCode ea) unaryCode 0).pair
    (inputA.pair (constant (prodCode unaryCode ea) (listCode eb) []))
  let result:=((second ea (listCode eb)).comp
    (second unaryCode (prodCode ea (listCode eb)))).comp (rep.comp (inputN.pair start))
  exact ((listReverse eb d).comp result).congrFun (by
    rintro ⟨n,a⟩
    change (((tabStep f)^[n] (0,a,[])).2.2).reverse=(List.range n).map (f a)
    rw [tabStep_iterate,List.append_nil,List.reverse_reverse,List.range_eq_range'])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
