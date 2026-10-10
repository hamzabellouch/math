import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateCells
import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice
import OAI.NumberTheory.Ostmann.Construction.NominalTotals

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic
open Construction Construction.InitialCoordinatesTemplate
open scoped BigOperators

@[simp] theorem selected_topCenters
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (b : ℕ) (h : Bool) (i : Fin 3) :
    topCenters b (C.cells.center b) h i = (C.cells.top i : ℝ) :=
  C.cells.center_top b h i

@[simp] theorem selected_compensationCenters
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (b : ℕ) (h : Bool) (j : Fin k) (i : Fin 2) :
    compensationCenters b (C.cells.center b) h j i = (C.cells.comp j i : ℝ) :=
  C.cells.center_comp b h j i

theorem selected_source_center_error
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (b : ℕ) :
    |(2*(C.giantCenter : ℝ)+2*C.bulkBin+2*C.spectatorBin+
      (∑ h, ∑ i, topCenters b (C.cells.center b) h i)+
      (∑ h, ∑ j : Fin k, ∑ i, compensationCenters b (C.cells.center b) h j i))-
      (Real.log (C.scale : ℝ)+Conclusion.initialGap Bs k L)| ≤ 2+2*(k : ℝ) := by
  simp only [selected_topCenters, selected_compensationCenters]
  have htop : |(∑ _h : Bool, ∑ i, (C.cells.top i : ℝ))-
      (nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin-2*C.bulkBin)| ≤ 2 := by
    simpa only [Fintype.sum_bool, ← two_mul] using C.cells.top_doubled_error.le
  have hcomp : |(∑ _h : Bool, ∑ j, ∑ i, (C.cells.comp j i : ℝ))-
      (∑ j : Fin k, nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j)| ≤
      2*(k : ℝ) := by
    have he : (∑ _h : Bool, ∑ j, ∑ i, (C.cells.comp j i : ℝ))-
        (∑ j : Fin k, nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j) =
        ∑ j : Fin k, (2*(∑ i, (C.cells.comp j i : ℝ))-
          nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j) := by
      simp only [Fintype.sum_bool, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [he]
    calc
      _ ≤ ∑ j : Fin k, |2*(∑ i, (C.cells.comp j i : ℝ))-
          nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k, (2 : ℝ) :=
        Finset.sum_le_sum (fun j _ => (C.cells.comp_doubled_error j).le)
      _ = _ := by simp [mul_comm]
  have hnom := nominalCompensation_total Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin
  rw [← Fin.sum_univ_eq_sum_range] at hnom
  change nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin+
      (∑ j : Fin k, nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j) =
      Real.log (C.scale : ℝ)-2*C.giantCenter-2*C.spectatorBin+Conclusion.initialGap Bs k L at hnom
  have he : (2*(C.giantCenter : ℝ)+2*C.bulkBin+2*C.spectatorBin+
      (∑ _h : Bool, ∑ i, (C.cells.top i : ℝ))+
      (∑ _h : Bool, ∑ j, ∑ i, (C.cells.comp j i : ℝ)))-
      (Real.log (C.scale : ℝ)+Conclusion.initialGap Bs k L) =
      ((∑ _h : Bool, ∑ i, (C.cells.top i : ℝ))-
        (nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin-2*C.bulkBin))+
      ((∑ _h : Bool, ∑ j, ∑ i, (C.cells.comp j i : ℝ))-
        (∑ j : Fin k, nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j)) := by
    linarith
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add htop hcomp)

theorem selected_Xi_source_center
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) :
    Real.log (C.scale : ℝ)+Conclusion.initialGap Bs k L-(2+2*(k : ℝ)) ≤
      2*(C.giantCenter : ℝ)+2*C.bulkBin+2*C.spectatorBin+
      (∑ h, ∑ i, topCenters (Conclusion.bulkSize k L/2)
        (C.cells.center (Conclusion.bulkSize k L/2)) h i)+
      (∑ h, ∑ j : Fin k, ∑ i, compensationCenters (Conclusion.bulkSize k L/2)
        (C.cells.center (Conclusion.bulkSize k L/2)) h j i) := by
  have h := (abs_le.mp (selected_source_center_error C (Conclusion.bulkSize k L/2))).1
  linarith

end Ostmann.Arithmetic

end

end OAI
