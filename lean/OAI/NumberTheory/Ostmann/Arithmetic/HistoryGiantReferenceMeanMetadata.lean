import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanOriginal
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationMetadata
import OAI.NumberTheory.Ostmann.Construction.SelectedSourceSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantReferenceMean
open Construction HistorySignedXiTransport HistorySymbolicEncoding CanonicalOccurrenceTransport
open HistoryOccurrenceVariables HistoryRepresentativeSourceSeparation

@[simp] theorem drawHistory_root_small {α : Type*} (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (P Q : α→ℤ) (r : α) : (drawHistory sources seed V l a c P Q r).root.small=a.small := by
  simp only [drawHistory,decodeHistory_root,giantState]

@[simp] theorem drawHistory_root_frequency {α : Type*} (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (P Q : α→ℤ) (r : α) : (drawHistory sources seed V l a c P Q r).root.frequency=a.frequency := by
  simp only [drawHistory,decodeHistory_root,giantState]

theorem drawHistory_internalOccurrences {α : Type*} (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (P Q : α→ℤ) (r : α) :
    (drawHistory sources seed V l a c P Q r).internalOccurrences=
      (decodeHistory sources seed V l a c).internalOccurrences :=
  decoded_internalOccurrences_eq sources seed V l _ a c

theorem drawHistory_compensationProduct {α : Type*} (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (P Q : α→ℤ) (r : α) :
    (drawHistory sources seed V l a c P Q r).compensationProduct=
      (decodeHistory sources seed V l a c).compensationProduct :=
  decoded_compensationProduct_eq sources seed V l _ a c

theorem source_draw_root_mass {α : Type*} (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (x : SourceAssignment sources (Template.current seed l))
    (s : ℤ) (c : HistoryChoices sources seed V l) (P Q : α→ℤ) (r : α)
    (hx : (assignmentPrior sources (Template.current seed l)).mass x≠0) :
    ∀q∈(drawHistory sources seed V l (sourceState sources (Template.current seed l) x s) c P Q r).root.small,
      sourceMass sources q≠0 := by
  rw [drawHistory_root_small]
  exact assignedSlots_source_mass_ne_zero _ _ _ hx

theorem source_draw_internal_mass {α : Type*} (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (P Q : α→ℤ) (r : α) (hc : choicesMass sources seed V l c≠0) :
    ∀i : InternalKey (drawHistory sources seed V l a c P Q r),
      sourceMass sources (internalSlot (drawHistory sources seed V l a c P Q r) i)≠0 :=
  decoded_internalSlot_mass sources seed V l _ c hc

variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem prime_reference_cells (C : InitialSourceChoice d Bs BD Bz k L E)
    (r : PrimeDraw C.giant) (hr : 0 < primeWeight C.giant r) :
    |Real.log (r.1.val:ℝ)-(C.giantCenter:ℝ)|<1 ∧
    |Real.log (r.2.val:ℝ)-(C.giantCenter:ℝ)|<1 := by
  have hn : C.giant.law.mass r.1*C.giant.law.mass r.2≠0 := hr.ne'
  exact ⟨C.giant_log_support r.1 (mul_ne_zero_iff.mp hn).1,
    C.giant_log_support r.2 (mul_ne_zero_iff.mp hn).2⟩

theorem mixed_reference_cells (C : InitialSourceChoice d Bs BD Bz k L E)
    (r : MixedDraw C.giantCenter C.giant) (hr : 0 < mixedWeight C.giantCenter C.giant r) :
    |Real.log (r.1.val:ℝ)-(C.giantCenter:ℝ)|<1 ∧
    |Real.log (r.2.val:ℝ)-(C.giantCenter:ℝ)|<1 := by
  have hn : externalPivotWeight C.giantCenter r.1.val*C.giant.law.mass r.2≠0 := hr.ne'
  refine ⟨?_,C.giant_log_support r.2 (mul_ne_zero_iff.mp hn).2⟩
  have hweight := (mul_ne_zero_iff.mp hn).1
  have hphi : smoothPartition (Real.log (r.1.val:ℝ)-(C.giantCenter:ℝ))≠0 :=
    (mul_ne_zero_iff.mp hweight).2
  exact lt_of_not_ge (fun hh => hphi (smoothPartition_zero_of_one_le_abs hh))

end Ostmann.Arithmetic.HistoryGiantReferenceMean

end

end OAI
