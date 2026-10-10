import OAI.Combinatorics.ContingencyTables.Sampling.SmallLineSumProgram
import OAI.Combinatorics.ContingencyTables.Sampling.SmallPatternProgram

namespace OAI

/-! # Binary execution of the complemented small column view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def complementValues (z : ℕ×List ℕ) : List ℕ := z.2.map (fun a => z.1-a)

def complementValuesRealizer : Realizer complementValues := mapWith subtract

theorem polynomial_complementValues : PolynomialTime complementValuesRealizer :=
  polynomial_mapWith polynomial_subtract

lemma complementValues_ofFn {n : ℕ} (U : ℕ) (v : Fin n → ℕ) :
    complementValues (U,List.ofFn v)=List.ofFn (fun i => U-v i) := by
  simp only [complementValues,List.map_ofFn,Function.comp_def]

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open PaddedCompletions ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

/-- The arithmetic complement needs no underflow assumption: it agrees
with the natural subtraction already present in the physical view. -/
theorem lookupComplement_eq (B : Fin m → Fin n → ℕ) (z : SmallProfile small) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (i : Fin m) (j : Fin n) :
    lookupView ((cellCatalog small e,complementValues (U,viewList small e z true)),(i.val,j.val))=
      smallQ small B z i j := by
  let v : SmallProfile small := fun a => U-z (a.1,true)
  have hc : complementValues (U,viewList small e z true)=viewList small e v false := by
    simp only [viewList,complementValues_ofFn]
    rfl
  rw [hc,lookupView_eq]
  by_cases hs : small i j=true
  · simp only [smallView,smallQ,hs,dite_true,v,hU ⟨(i,j),hs⟩]
  · simp [smallView,smallQ,hs]

theorem complementedColumnSum_eq (B : Fin m → Fin n → ℕ) (z : SmallProfile small)
    (U : ℕ) (hU : ∀ a : Cells small,B a.val.1 a.val.2=U)
    (r : Fin m → ℕ) (j : Fin n) :
    lineSum false (((cellCatalog small e,complementValues (U,viewList small e z true)),
      List.ofFn r),j.val)=smallColumn small B (smallView small z true) j := by
  have he : lineSum false (((cellCatalog small e,complementValues (U,viewList small e z true)),
      List.ofFn r),j.val)=∑ i,smallQ small B z i j := by
    apply lineSum_eq_sum false _ List.length_ofFn
    intro i
    exact lookupComplement_eq small e B z U hU i j
  rw [he]
  unfold smallColumn
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : small i j=true
  · simp only [smallQ,smallView,hs,dite_true,ite_true]
  · simp [smallQ,hs]

theorem storedRowSum_eq (z : SmallProfile small) (c : Fin n → ℕ) (i : Fin m) :
    lineSum true (((cellCatalog small e,viewList small e z false),List.ofFn c),i.val)=
      smallRow small (smallView small z false) i := by
  rw [rowSum_eq]
  unfold smallRow
  apply Finset.sum_congr rfl
  intro j _
  by_cases hs : small i j=true
  · simp only [hs,ite_true]
  · simp [smallView,hs]

end
end ContingencyTables.SmallGraphProfiles

end OAI
