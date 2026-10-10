import Mathlib
import OAI.Computability.QuantumFactoring.NetworkEmissionBounds

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
structure PackData where
  budget : ℕ
  value : Data
abbrev Pack:={s : PackData // s.value.Valid ∧ s.value.mass ≤ s.budget}
def packCode (s : Pack) : List Bool:=prodCode unaryCode dataCode (s.val.budget,s.val.value)
def pairPack (a b : Pack) : Pack:=
  ⟨⟨a.val.budget+b.val.budget,if a.val.value.inputs=b.val.value.inputs then pair a.val.value b.val.value else a.val.value⟩,by
    split
    · rename_i h
      exact ⟨pair_valid a.property.1 b.property.1 h,(pair_mass _ _).trans (Nat.add_le_add a.property.2 b.property.2)⟩
    · exact ⟨a.property.1,a.property.2.trans (Nat.le_add_right _ _)⟩⟩
def compPack (a b : Pack) : Pack:=
  ⟨⟨a.val.budget+b.val.budget,if a.val.value.outputs.length=b.val.value.inputs then comp a.val.value b.val.value else a.val.value⟩,by
    split
    · rename_i h
      exact ⟨comp_valid a.property.1 b.property.1 h,(comp_mass _ _).trans (Nat.add_le_add a.property.2 b.property.2)⟩
    · exact ⟨a.property.1,a.property.2.trans (Nat.le_add_right _ _)⟩⟩
lemma pairPack_inputs (a b : Pack) : (pairPack a b).val.value.inputs=a.val.value.inputs:=by
  unfold pairPack;split <;> rfl
lemma compPack_inputs (a b : Pack) : (compPack a b).val.value.inputs=a.val.value.inputs:=by
  unfold compPack;split <;> rfl
lemma pairPack_value (a b : Pack) (h : a.val.value.inputs=b.val.value.inputs) :
    (pairPack a b).val.value=pair a.val.value b.val.value:=by simp only [pairPack,ite_eq_left h]
lemma compPack_value (a b : Pack) (h : a.val.value.outputs.length=b.val.value.inputs) :
    (compPack a b).val.value=comp a.val.value b.val.value:=by simp only [compPack,ite_eq_left h]
lemma packCode_bound (s : Pack) : (packCode s).length≤104*(s.val.budget+1)^2:=by
  have hh:=dataCode_bound s.property.1 s.property.2
  simp only [packCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
  nlinarith [Nat.zero_le s.val.budget]
lemma packBudget_le_code (s : Pack) : s.val.budget≤(packCode s).length:=by
  simp only [packCode,prodCode,pairBits_length,unaryCode,List.length_replicate];omega
lemma packBudgets_le_code (xs : List Pack) : (xs.map (fun s=>s.val.budget)).sum≤(listCode packCode xs).length:=by
  induction xs with
  | nil=>simp
  | cons s xs ih=>
    have hh:=packBudget_le_code s
    simp only [List.map_cons,List.sum_cons,listCode_length_cons];omega
lemma fold_budget (f : Pack→Pack→Pack) (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget)
    (xs : List Pack) (a : Pack) : (xs.foldl f a).val.budget=a.val.budget+(xs.map (fun s=>s.val.budget)).sum:=by
  induction xs generalizing a with
  | nil=>simp
  | cons s xs ih=>rw [List.foldl_cons,ih,h,List.map_cons,List.sum_cons];omega

def selectPack (n : ℕ) (xs : List ℕ) (h : ∀i∈xs,i≤n) : Pack:=
  ⟨⟨n+xs.length,select n xs⟩,valid_select n xs h,by simp [Data.mass,Data.width,select]⟩
def emptyPack : Pack:=selectPack 0 [] (by simp)
def nodePack (n : ℕ) (o : Node) (h : o.Bound n) : Pack:=
  ⟨⟨n+2,node n o⟩,valid_node n o h,by simp [Data.mass,Data.width,node]⟩
def erasePack {n m : ℕ} (a : BooleanNetwork n m) : Pack:=
  ⟨⟨n+a.net.count+m,erase a⟩,erase_valid a,by simp only [Data.mass,Data.width,erase,eraseNet_length,List.length_ofFn];rfl⟩
namespace Emission
noncomputable def packViewP : Procedure packCode (prodCode unaryCode dataCode)
    (fun s=>(s.val.budget,s.val.value)):=(identity _).precompose _
noncomputable def packBudgetP : Procedure packCode unaryCode (fun s=>s.val.budget):=
  (first unaryCode dataCode).comp packViewP
noncomputable def packValueP : Procedure packCode dataCode (fun s=>s.val.value):=
  (second unaryCode dataCode).comp packViewP
noncomputable def pairPackP : Procedure (prodCode packCode packCode) packCode (fun x=>pairPack x.1 x.2):=by
  let a:=first packCode packCode
  let b:=second packCode packCode
  let av:=packValueP.comp a
  let bv:=packValueP.comp b
  let test:=binaryEq.comp ((dataInputP.comp av).pair (dataInputP.comp bv))
  let val:=conditional test (pairP.comp (av.pair bv)) av
  let bud:=unaryAdd.comp ((packBudgetP.comp a).pair (packBudgetP.comp b))
  exact (bud.pair val).result (by intro x;unfold pairPack packCode;split <;> simp_all)
noncomputable def compPackP : Procedure (prodCode packCode packCode) packCode (fun x=>compPack x.1 x.2):=by
  let a:=first packCode packCode
  let b:=second packCode packCode
  let av:=packValueP.comp a
  let bv:=packValueP.comp b
  let len:=(listLength Nat.bits 0).comp (dataOutputsP.comp av)
  let test:=binaryEq.comp (len.pair (dataInputP.comp bv))
  let val:=conditional test (compP.comp (av.pair bv)) av
  let bud:=unaryAdd.comp ((packBudgetP.comp a).pair (packBudgetP.comp b))
  exact (bud.pair val).result (by intro x;unfold compPack packCode;split <;> simp_all)
noncomputable def foldPack {f : Pack→Pack→Pack}
    (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget)
    (p : Procedure (prodCode packCode packCode) packCode (fun x=>f x.1 x.2)) :
    Procedure (prodCode (listCode packCode) packCode) packCode (fun x=>x.1.foldl f x.2):=
  foldList emptyPack (p.comp ((second packCode packCode).pair (first packCode packCode)))
    (Polynomial.C 104*(Polynomial.X+1)^2) (by
      intro xs a i
      have hh:=packCode_bound ((xs.take i).foldl f a)
      rw [fold_budget f h] at hh
      have hb:=packBudget_le_code a
      have hx:=(packBudgets_le_code (xs.take i)).trans (listCode_length_take_le packCode i xs)
      have hp:=Nat.pow_le_pow_left (by omega :
        a.val.budget+((xs.take i).map (fun s=>s.val.budget)).sum+1≤
          (listCode packCode xs).length+(packCode a).length+1) 2
      simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one]
      change (packCode ((xs.take i).foldl f a)).length≤104*((listCode packCode xs).length+(packCode a).length+1)^2
      exact hh.trans (Nat.mul_le_mul_left _ hp))
noncomputable def foldPairP : Procedure (prodCode (listCode packCode) packCode) packCode
    (fun x=>x.1.foldl pairPack x.2):=foldPack (by intros;rfl) pairPackP
noncomputable def foldCompP : Procedure (prodCode (listCode packCode) packCode) packCode
    (fun x=>x.1.foldl compPack x.2):=foldPack (by intros;rfl) compPackP
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI
