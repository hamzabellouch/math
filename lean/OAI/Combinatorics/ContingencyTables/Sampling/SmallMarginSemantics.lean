import OAI.Combinatorics.ContingencyTables.Sampling.SmallMarginTestProgram
import OAI.Combinatorics.ContingencyTables.Sampling.SmallResidualTotals

namespace OAI

/-! # The executable margin tests characterize physical feasibility -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open PaddedCompletions ProfilePrograms FirstPaperPhysicalMarginal

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem validRows_iff (z : SmallProfile small) (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ) :
    validMargins true (((cellCatalog small e,viewList small e z false),
      (List.ofFn r,List.ofFn c)),U)=true ↔
      ∀ i,smallRow small (smallView small z false) i≤r i ∧
        (r i<U → smallRow small (smallView small z false) i=r i) := by
  rw [validMargins_iff]
  simp only [marginList,ite_true,List.length_ofFn]
  constructor
  · intro h i
    have hi := h i.val i.isLt
    simpa only [lineArgument,Bool.not_true,marginList,Bool.false_eq_true,ite_false,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,
      Fin.eta,storedRowSum_eq] using hi
  · intro h i hi
    have hh := h ⟨i,hi⟩
    have he := storedRowSum_eq small e z c (⟨i,hi⟩ : Fin m)
    simpa only [lineArgument,Bool.not_true,marginList,Bool.false_eq_true,ite_false,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hi,Option.getD_some,
      ←he] using hh

theorem validColumns_iff (B : Fin m → Fin n → ℕ) (z : SmallProfile small)
    (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) :
    validMargins false (((cellCatalog small e,complementValues (U,viewList small e z true)),
      (List.ofFn r,List.ofFn c)),U)=true ↔
      ∀ j,smallColumn small B (smallView small z true) j≤c j ∧
        (c j<U → smallColumn small B (smallView small z true) j=c j) := by
  rw [validMargins_iff]
  simp only [marginList,Bool.false_eq_true,ite_false,List.length_ofFn]
  constructor
  · intro h j
    have hj := h j.val j.isLt
    simpa only [lineArgument,Bool.not_false,marginList,ite_true,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some,
      Fin.eta,complementedColumnSum_eq small e B z U hU] using hj
  · intro h j hj
    have hh := h ⟨j,hj⟩
    have he := complementedColumnSum_eq small e B z U hU r (⟨j,hj⟩ : Fin n)
    simpa only [lineArgument,Bool.not_false,marginList,ite_true,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hj,Option.getD_some,
      ←he] using hh

end
end ContingencyTables.SmallGraphProfiles

end OAI
