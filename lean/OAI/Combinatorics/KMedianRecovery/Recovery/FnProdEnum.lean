import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Op2

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalOpenability
lemma ofFn_prodEnum {α : Type*} {m n : ℕ} (f : Fin m × Fin n → α) :
    List.ofFn (fun i=>f (finProdFinEquiv.symm i))=
      (List.ofFn (fun i : Fin m=>i)).flatMap (fun i=>List.ofFn (fun j : Fin n=>f (i,j))) := by
  rw [List.ofFn_mul]
  change _ = ((List.ofFn (fun i : Fin m=>i)).map (fun i=>List.ofFn (fun j : Fin n=>f (i,j)))).flatten
  rw [List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he : (⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩ : Fin (m*n))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*n+j.val=j.val+n*i.val
    ring
  rw [he,Equiv.symm_apply_apply]
lemma ofFn_variableEnum {α : Type*} {m d : ℕ} (F : Finset (Fin m)) (f : Variables (Fin d) F → α) :
    List.ofFn (fun j=>f (variableEnum d F j))=
      (List.ofFn (fun j : Fin d=>j)).map (fun j=>f (.inl j))++
      (subtypeList F).flatMap (fun g=>(List.ofFn (fun a : Fin d=>a)).flatMap (fun a=>
        (List.ofFn (fun j : Fin d=>j)).map (fun j=>f (.inr (g,a,j))))) := by
  let g : Fin (F.card*(d*d)) → α := fun j=>f (.inr ((F.orderIsoOfFin rfl) (finProdFinEquiv.symm j).1,
    finProdFinEquiv.symm (finProdFinEquiv.symm j).2))
  have he : (fun j=>f (variableEnum d F j))=Fin.append (fun j=>f (.inl j)) g := by
    funext j
    refine Fin.addCases (fun k=>?_) (fun k=>?_) j
    · simp [variableEnum]
    · simp [variableEnum,Fin.append_right,g]
  rw [he,List.ofFn_fin_append]
  simp only [List.map_ofFn,Function.comp_def]
  congr 1
  change List.ofFn (fun j=>(fun p=>f (.inr ((F.orderIsoOfFin rfl) p.1,finProdFinEquiv.symm p.2)))
    (finProdFinEquiv.symm j))=_
  rw [ofFn_prodEnum (fun p : Fin F.card × Fin (d*d)=>f (.inr ((F.orderIsoOfFin rfl) p.1,finProdFinEquiv.symm p.2)))]
  simp only [subtypeList,BitMachine.WordList.flatMap_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  rw [ofFn_prodEnum (fun p : Fin d × Fin d=>f (.inr ((F.orderIsoOfFin rfl) j,p)))]
  simp only [BitMachine.WordList.flatMap_ofFn]
end MetricKMedianRecovery.EffectiveOpenability

end OAI
