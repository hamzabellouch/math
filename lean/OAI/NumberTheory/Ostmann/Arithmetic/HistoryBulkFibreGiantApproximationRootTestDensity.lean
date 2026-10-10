import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCounterpartTransportExtracted
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestMixed

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion HistoryBulkReferenceSmallMultiplier
open HistoryDiagonalSmallOriginalMean HistoryBulkCounterpartTransport
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E}
namespace Frame

def slotDensity (xs : List SmallSlot) : ℂ :=
  ((∏i : Fin xs.length, ((((xs.get i).value-1:ℕ):ℝ)/(xs.get i).value):ℝ):ℂ)

theorem extractedDensity_eq_of_nonbulk_fixed
    (x x₀ : Source (C:=C) (l:=l))
    (hfixed : ∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
      ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
      (x i).val=(x₀ i).val) :
    extractedDensity (C:=C) x = extractedDensity (C:=C) x₀ := by
  have hu := restoringAssignment_first_eq_of_nonbulk_fixed C.sources _ (l+1) x x₀ hfixed
  have hs : currentOuterSlots C x = currentOuterSlots C x₀ :=
    congrArg (assignedSlots C.sources _) hu
  change slotDensity (currentOuterSlots C x)=slotDensity (currentOuterSlots C x₀)
  exact congrArg slotDensity hs

theorem norm_extractedDensity_le (x : Source (C:=C) (l:=l)) :
    ‖extractedDensity (C:=C) x‖≤1 := by
  unfold extractedDensity
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply Finset.prod_le_one₀ (fun _ _=>by positivity)
  intro i _
  let p := ((currentOuterSlots C x).get i).value
  change ((p-1:ℕ):ℝ)/(p:ℝ)≤1
  by_cases hp : p=0
  · simp [hp]
  · have hpos : (0:ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero hp
    apply (div_le_one hpos).mpr
    exact_mod_cast Nat.sub_le p 1

end Frame
end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
