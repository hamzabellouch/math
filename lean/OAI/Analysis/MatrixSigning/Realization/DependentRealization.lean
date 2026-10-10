import Mathlib
import OAI.Analysis.MatrixSigning.Realization.FaceArrayRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*}

def finFamilyCode (ea : α → Word) (n : α → ℕ) (p : Σ a,Fin (n a)) : Word :=
  prodCode ea natCode (p.1,p.2.val)

def Realizes.tabulateFin {ea : α → Word} {eb : β → Word} {n : α → ℕ}
    {f : (Σ a,Fin (n a)) → β} (r : Realizes (finFamilyCode ea n) eb f)
    (rn : Realizes ea natCode n) :
    Realizes ea (listCode eb) (fun a => List.ofFn (fun i => f ⟨a,i⟩)) :=
  let pairs := ((identity ea).both (rn.then range)).then (identity (prodCode ea natCode)).mapCtx
  let typed := pairs.changeOutput (listCode (finFamilyCode ea n))
    (fun a => (List.finRange (n a)).map (fun i => (⟨a,i⟩ : Σ a,Fin (n a)))) (by
      intro a
      simp only [listCode,FramedMapRoutine.tape,List.flatMap_map,finFamilyCode,id_eq]
      rw [range_finRange,List.flatMap_map])
  (typed.then r.map).congr (by
    intro a
    rw [List.map_map]
    exact List.ofFn_eq_map.symm)

def familyFirst {ea : α → Word} {n : α → ℕ} :
    Realizes (finFamilyCode ea n) ea (fun p => p.1) :=
  (first ea natCode).reindex (finFamilyCode ea n) (fun p => (p.1,p.2.val)) (fun _ => rfl)
def familyIndex {ea : α → Word} {n : α → ℕ} :
    Realizes (finFamilyCode ea n) natCode (fun p => p.2.val) :=
  (second ea natCode).reindex (finFamilyCode ea n) (fun p => (p.1,p.2.val)) (fun _ => rfl)

end CurrentKS.Realization

end

end OAI
