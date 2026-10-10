import OAI.Combinatorics.ContingencyTables.Sampling.SmallRepairCodeProgram

namespace OAI

/-! # The labelled defect predicate on two binary-coded views -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def repairLabelTest (z : LabelledRepairData) : Bool :=
  defectTest ((z.1.1.2,z.1.2),z.2)

def repairLabelTestRealizer : Realizer repairLabelTest :=
  composition (pair (pair (composition (composition first first) second)
    (composition first second)) second) defectTestRealizer

theorem polynomial_repairLabelTest : PolynomialTime repairLabelTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second) polynomial_defectTest

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem repairLabelTest_iff (B : Fin m → Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (z : SmallProfile small)
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2) (s t : Cells small) :
    repairLabelTest (((cellCatalog small e,profileCode small e z),U),
      ((e.symm s).val,(e.symm t).val))=true ↔
      IsDefect (smallView small z false) (smallQ small B z) s.val t.val := by
  rw [defect_iff_cellSums small B z hb s t]
  simp only [repairLabelTest,profileCode,viewList,defectTest_ofFn]
  constructor
  · rintro ⟨hne,h⟩
    refine ⟨fun he => hne (congrArg e.symm he),?_⟩
    intro a
    have hs : e.symm a=e.symm s ↔ a=s := e.symm.injective.eq_iff
    have ht : e.symm a=e.symm t ↔ a=t := e.symm.injective.eq_iff
    simpa only [Equiv.apply_symm_apply,hs,ht,hU] using h (e.symm a)
  · rintro ⟨hne,h⟩
    refine ⟨fun he => hne (e.symm.injective he),?_⟩
    intro i
    have hs : e i=s ↔ i=e.symm s := (Equiv.eq_symm_apply e).symm
    have ht : e i=t ↔ i=e.symm t := (Equiv.eq_symm_apply e).symm
    simpa only [hs,ht,hU] using h (e i)

end
end ContingencyTables.SmallGraphProfiles

end OAI
