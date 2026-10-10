import Mathlib
import OAI.Computability.QuantumFactoring.NetworkEmissionPack

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
abbrev StackOp := Pack ⊕ Bool
def stackOpCode : StackOp→List Bool:=sumCode packCode boolCode
def stackStep (o : StackOp) (s : List Pack) : List Pack:=match o with
  | .inl a=>a::s
  | .inr b=>let a:=s.tail.headD emptyPack;let c:=s.headD emptyPack
    (if b then compPack a c else pairPack a c)::s.tail.tail
def stackBudget (s : List Pack) : ℕ:=(s.map (fun a=>a.val.budget)).sum
def opWeight : StackOp→ℕ | .inl a=>a.val.budget | .inr _=>0
lemma stackStep_budget (o : StackOp) (s : List Pack) :
    stackBudget (stackStep o s)≤ stackBudget s+opWeight o:=by
  cases o with
  | inl a=>simp [stackStep,stackBudget,opWeight,Nat.add_comm]
  | inr b=>
    cases s with
    | nil=>cases b <;> simp [stackStep,stackBudget,opWeight,emptyPack,selectPack,pairPack,compPack]
    | cons a s=>cases s with
      | nil=>cases b <;> simp [stackStep,stackBudget,opWeight,emptyPack,selectPack,pairPack,compPack]
      | cons c s=>cases b <;> simp [stackStep,stackBudget,opWeight,pairPack,compPack,Nat.add_comm,Nat.add_assoc]
lemma stackStep_length (o : StackOp) (s : List Pack) : (stackStep o s).length≤ s.length+1:=by
  cases o <;> simp [stackStep,List.length_tail];omega
lemma stackFold_budget (ops : List StackOp) (s : List Pack) :
    stackBudget (ops.foldl (fun s o=>stackStep o s) s)≤ stackBudget s+(ops.map opWeight).sum:=by
  induction ops generalizing s with
  | nil=>simp
  | cons o ops ih=>
    have hs:=stackStep_budget o s
    have hh:=ih (stackStep o s)
    simp only [List.foldl_cons,List.map_cons,List.sum_cons]
    omega
lemma stackFold_length (ops : List StackOp) (s : List Pack) :
    (ops.foldl (fun s o=>stackStep o s) s).length≤ s.length+ops.length:=by
  induction ops generalizing s with
  | nil=>simp
  | cons o ops ih=>
    have hs:=stackStep_length o s
    have hh:=ih (stackStep o s)
    simp only [List.foldl_cons,List.length_cons];omega
lemma opWeight_le_code (o : StackOp) : opWeight o≤(stackOpCode o).length:=by
  cases o with
  | inl a=>have h:=packBudget_le_code a;simp only [stackOpCode,sumCode,List.length_cons,opWeight];omega
  | inr b=>simp [opWeight]
lemma opWeights_le_code (ops : List StackOp) : (ops.map opWeight).sum≤(listCode stackOpCode ops).length:=by
  induction ops with
  | nil=>simp
  | cons o ops ih=>
    have hh:=opWeight_le_code o
    simp only [List.map_cons,List.sum_cons,listCode_length_cons];omega
lemma stackCode_bound (s : List Pack) :
    (listCode packCode s).length≤ s.length*(208*(stackBudget s+1)^2+2)+1:=by
  have hh:=listCode_length_bound packCode s (104*(stackBudget s+1)^2) (by
    intro a ha
    have hb : a.val.budget≤ stackBudget s:=List.single_le_sum (fun _ _=>Nat.zero_le _) _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
    exact (packCode_bound a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)))
  convert hh using 1; ring

end ExactQuantumFactoring.NetworkEmission
end

end OAI
