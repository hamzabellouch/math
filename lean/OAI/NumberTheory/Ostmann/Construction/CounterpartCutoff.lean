import OAI.NumberTheory.Ostmann.Construction.CounterpartNormalization
import OAI.NumberTheory.Ostmann.Construction.DiagonalExternalMeasure
import OAI.NumberTheory.Ostmann.Construction.DiagonalRegroupingRootCorrection
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
local notation "b₀" => (Conclusion.bulkSize k L/2)

private theorem sourceCutoff_origin_eq (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin p : ℕ) (hi : origin<2*b₀+6+4*k) :
    C.sourceCutoff origin p=
      if origin<2*b₀ then 1 else Ostmann.smoothPartition (Real.log p-C.cells.center b₀ origin) := by
  by_cases hb : origin<2*b₀
  · simp only [sourceCutoff,initialSourceValue,hb,ite_true]
  · by_cases ht : origin<2*b₀+6
    · simp only [sourceCutoff,NominalCenterArray.center,initialSourceValue,hb,ht,ite_false,ite_true]
    · have hc : (origin-(2*b₀+6))/4<k := by omega
      simp only [sourceCutoff,NominalCenterArray.center,initialSourceValue,hb,ht,hc,ite_false,dite_true]

theorem sourceCutoff_slot_eq (C : InitialSourceChoice d Bs BD Bz k L E)
    (q : SourceSlot) (hq : q∈Template.initial (2*b₀) k) (p : ℕ) :
    C.sourceCutoff q.origin p=
      if q.role=.bulk then 1 else Ostmann.smoothPartition (Real.log p-C.cells.center b₀ q.origin) := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  have hi : i.val<2*b₀+6+4*k := by
    simpa only [InitialCoordinatesTemplate.initialRoles_length] using i.isLt
  rw [sourceCutoff_origin_eq C i.val p hi]
  have he := InitialCoordinatesTemplate.initialRoles_bulk_iff (2*b₀) k i
  change (Template.initialRoles (2*b₀) k)[i]=.bulk ↔ i.val<2*b₀ at he
  simp only [he]

private theorem nonbulk_cutoff_product (xs : List SmallSlot) (F : SmallSlot→ℝ) :
    (xs.map (fun q => if q.role=.bulk then 1 else F q)).prod=
      ((xs.filter (fun q => decide (q.role≠.bulk))).map F).prod := by
  induction xs with
  | nil => rfl
  | cons q xs ih =>
    by_cases hb : q.role=.bulk <;> simp [hb,ih]

theorem remainingCutoff_cells (C : InitialSourceChoice d Bs BD Bz k L E)
    (T : List SourceSlot) (hT : ∀q∈T,q∈Template.initial (2*b₀) k)
    (y : RemainingSample C.sources T C.giant) :
    C.remainingCutoff T y=
      Ostmann.smoothPartition (Real.log (y.1.val:ℝ)-C.giantCenter)*
      (((assignedSlots C.sources T y.2).filter (fun q => decide (q.role≠.bulk))).map
        (fun q => Ostmann.smoothPartition (Real.log (q.value:ℝ)-C.cells.center b₀ q.origin))).prod := by
  unfold remainingCutoff
  congr 1
  rw [←nonbulk_cutoff_product]
  simp only [assignedSlots,Template.sample,List.map_ofFn,List.prod_ofFn,Function.comp_def]
  apply Finset.prod_congr rfl
  intro i hi
  exact C.sourceCutoff_slot_eq T[i] (hT _ (List.getElem_mem i.isLt)) (y.2 i)

theorem remaining_mass_scalar_extraction (C : InitialSourceChoice d Bs BD Bz k L E)
    (seed : List SourceSlot) (hseed : ∀q∈seed,q∈Template.initial (2*b₀) k)
    (j l : ℕ) (B Δ : ℝ) (p : ℕ)
    (u : SourceAssignment C.sources (Template.extracted j (Template.current seed l)))
    (y : RemainingSample C.sources (Template.remainder j (Template.current seed l)) C.giant) :
    (((assignedSlots C.sources (Template.extracted j (Template.current seed l)) u).map SmallSlot.value).prod:ℝ)*
      Ostmann.smoothPartition (Real.log p-C.giantCenter)*
      (remainingPrior C.sources (Template.remainder j (Template.current seed l)) C.giant).mass y=
    C.remainingNormalization (Template.remainder j (Template.current seed l))*Real.exp (-Δ)*
      externalPivotWeight C.giantCenter p*
      remainingCounterpart C.sources (Template.current seed l) j C.giant
        ((C.giantCenter:ℝ)+B+Δ) B C.giantCenter (C.cells.center b₀) u y := by
  rw [remaining_mass_normalization,remainingCutoff_cells C _
    (fun q hq => hseed q (Template.mem_remainder_current_mem_seed hq)) y]
  exact counterpart_scalar_extraction C.giantCenter B Δ _ _ _ _ _

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
