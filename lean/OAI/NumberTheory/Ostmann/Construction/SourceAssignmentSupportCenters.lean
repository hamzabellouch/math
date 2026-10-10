import OAI.NumberTheory.Ostmann.Construction.OffDiagonalFrequency
import OAI.NumberTheory.Ostmann.Construction.SelectedSourceSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
open Arithmetic.HistoryProductWindows InitialCoordinatesTemplate Conclusion
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem top_frequency_center_error (C : InitialSourceChoice d Bs BD Bz k L E) (b : ℕ) :
    |(∑h,∑i,topCenters b (C.cells.center b) h i)-
      (nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin-2*(C.bulkBin:ℝ))|≤2 := by
  have he : (∑h,∑i,topCenters b (C.cells.center b) h i)=2*∑i,(C.cells.top i:ℝ) := by
    simp only [topCenters,NominalCenterArray.center_top,Fintype.sum_bool]
    ring
  rw [he]
  exact C.cells.top_doubled_error.le

theorem type_frequency_center_error (C : InitialSourceChoice d Bs BD Bz k L E)
    (b j : ℕ) (hj : j<k) :
    |typeCenter b j (C.cells.center b)-
      nominalWeight k (nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin)
        (stepGap BD Bz k L) j|≤2 := by
  have he : typeCenter b j (C.cells.center b)=2*∑i,(C.cells.comp ⟨j,hj⟩ i:ℝ) := by
    unfold typeCenter
    calc
      _ = ∑h:Bool,∑i:Fin 2,(C.cells.comp ⟨j,hj⟩ i:ℝ) := by
        apply Finset.sum_congr rfl
        intro h hh
        apply Finset.sum_congr rfl
        intro i hi
        exact C.cells.center_comp b h ⟨j,hj⟩ i
      _ = _ := by simp only [Fintype.sum_bool]; ring
  rw [he]
  exact (C.cells.comp_doubled_error ⟨j,hj⟩).le

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
