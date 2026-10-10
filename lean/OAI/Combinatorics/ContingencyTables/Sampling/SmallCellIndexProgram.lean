import OAI.Combinatorics.ContingencyTables.Sampling.ProfileRepairProgram
import OAI.Combinatorics.MatchingCount.Machines.TreeIndex

namespace OAI

/-! # Executable indices for small cells and their crossing cells -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def cellLookupRealizer : Realizer (fun z : (ℕ×ℕ)×List (ℕ×ℕ) => z.2.idxOf z.1) :=
  indexOf (pairEqual natEqual natEqual)

theorem polynomial_cellLookup : PolynomialTime cellLookupRealizer :=
  polynomial_indexOf (polynomial_pairEqual polynomial_natEqual polynomial_natEqual)

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

def cellCatalog : List (ℕ×ℕ) :=
  List.ofFn (fun i => ((e i).val.1.val,(e i).val.2.val))

lemma cellCatalog_nodup : (cellCatalog small e).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  apply e.injective
  apply Subtype.ext
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

lemma mem_cellCatalog (t : Fin m×Fin n) :
    (t.1.val,t.2.val)∈cellCatalog small e ↔ small t.1 t.2=true := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
    have he : (e i).val=t := Prod.ext (Fin.ext (congrArg Prod.fst hi))
      (Fin.ext (congrArg Prod.snd hi))
    exact he ▸ (e i).property
  · intro h
    apply List.mem_ofFn.mpr
    exact ⟨e.symm ⟨t,h⟩,by simp only [Equiv.apply_symm_apply]⟩

/-- Ordinary list search gives precisely the semantic small-cell index;
large crossing cells get the out-of-range index without extra cases. -/
theorem cellCatalog_index (t : Fin m×Fin n) :
    (cellCatalog small e).idxOf (t.1.val,t.2.val)=cellIndex small e t := by
  by_cases ht : small t.1 t.2=true
  · let i := e.symm ⟨t,ht⟩
    have hi : (cellCatalog small e)[i.val]'(by simp only [cellCatalog,List.length_ofFn]; exact i.isLt)=
        (t.1.val,t.2.val) := by
      simp only [cellCatalog,List.getElem_ofFn]
      change ((e i).val.1.val,(e i).val.2.val)=(t.1.val,t.2.val)
      simp only [i,Equiv.apply_symm_apply]
    rw [←hi]
    rw [(cellCatalog_nodup small e).idxOf_getElem]
    exact (cellIndex_eq small e i t).mpr (by simp only [i,Equiv.apply_symm_apply])
  · rw [List.idxOf_eq_length ((mem_cellCatalog small e t).not.mpr ht)]
    simp only [cellCatalog,List.length_ofFn,cellIndex,dite_eq_right ht]

end
end ContingencyTables.SmallGraphProfiles

end OAI
