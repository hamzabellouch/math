import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGAdd

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
namespace Emission
noncomputable def knownP : Procedure (prodCode graphCode refCode) boolCode
    (fun x=>known x.1 x.2) := by
  let r:=first graphCode refCode
  let a:=second graphCode refCode
  let idx:=(first Nat.bits boolCode).comp a
  let d:=(listGet declCode .zero).comp (idx.pair (decls.comp r))
  exact (zeroDecl.comp d).congrFun (by
    rintro ⟨g,⟨i,b⟩⟩
    simp only [Function.comp_apply]
    have he : (g.decls.drop i).headD Decl.zero=g.decls[i]?.getD Decl.zero := by
      rw [List.headD_eq_head?_getD,List.head?_drop]
    simp only [he]
    unfold known
    cases g.decls[i]?.getD Decl.zero <;> rfl)
def knownStep (x : Ref×(Graph×ℕ)) : Graph×ℕ :=
  (x.2.1,x.2.2+(if known x.2.1 x.1 then 1 else 0))
lemma knownStep_fold (xs : List Ref) (g : Graph) (acc : ℕ) :
    xs.foldl (fun s a=>knownStep (a,s)) (g,acc)=(g,acc+countKnown g xs) := by
  induction xs generalizing acc with
  | nil=>simp
  | cons a as ih=>
    rw [List.foldl_cons]
    change as.foldl (fun s a=>knownStep (a,s)) (g,acc+(if known g a then 1 else 0))=_
    rw [ih,countKnown_cons,Nat.add_assoc]
noncomputable def knownStepP : Procedure (prodCode refCode (prodCode graphCode unaryCode))
    (prodCode graphCode unaryCode) knownStep := by
  let a:=first refCode (prodCode graphCode unaryCode)
  let rest:=second refCode (prodCode graphCode unaryCode)
  let g:=(first graphCode unaryCode).comp rest
  let acc:=(second graphCode unaryCode).comp rest
  let test:=knownP.comp (g.pair a)
  exact (conditional test (g.pair (unarySuccessor.comp acc)) rest).congrFun (by
    intro x
    unfold knownStep
    split <;> simp_all)
noncomputable def countKnownUnaryP : Procedure (prodCode graphCode (listCode refCode)) unaryCode
    (fun x=>countKnown x.1 x.2) := by
  let fold:=foldList (0,false) knownStepP (Polynomial.C 2*Polynomial.X) (by
    rintro xs ⟨g,acc⟩ i
    rw [knownStep_fold]
    have hh : countKnown g (xs.take i)≤xs.length :=
      (List.length_filter_le _ _).trans (by simp only [List.length_take];omega)
    have hc:=list_length_le_code refCode xs
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega)
  let g:=first graphCode (listCode refCode)
  let xs:=second graphCode (listCode refCode)
  exact ((second graphCode unaryCode).comp (fold.comp (xs.pair
    (g.pair (Procedure.constant _ unaryCode 0))))).congrFun (by
      intro x
      change (x.2.foldl (fun s a=>knownStep (a,s)) (x.1,0)).2=countKnown x.1 x.2
      rw [knownStep_fold,Nat.zero_add])
noncomputable def countKnownP : Procedure (prodCode graphCode (listCode refCode)) Nat.bits
    (fun x=>countKnown x.1 x.2) := unaryToBits.comp countKnownUnaryP
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
