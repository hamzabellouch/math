import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabelsBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open HistoryFrequencyLabels HistoryReconstruction
attribute [local instance] Classical.propDecidable

def stepHistoryRanges (S : List Bool → Finset ℤ) (T : Finset ℤ) (p : List Bool) : Finset ℤ :=
  if p=[] then T else S p.dropLast

@[simp] theorem stepHistoryRanges_nil (S : List Bool → Finset ℤ) (T : Finset ℤ) :
    stepHistoryRanges S T []=T := by simp [stepHistoryRanges]

@[simp] theorem stepHistoryRanges_append (S : List Bool → Finset ℤ) (T : Finset ℤ)
    (p : List Bool) (b : Bool) : stepHistoryRanges S T (p++[b])=S p := by
  simp [stepHistoryRanges]

theorem stepHistoryRangeSupported (S : List Bool → Finset ℤ) (T : Finset ℤ)
    (j : ℕ) (p : List Bool) (b : Bool) (s : ℤ) (t : Tree j) :
    RangeSupported (stepHistoryRanges S T) j (p++[b]) s t ↔ RangeSupported S j p s t := by
  induction j generalizing p s with
  | zero => exact congrArg (fun A:Finset ℤ => s∈A) (stepHistoryRanges_append S T p b) |>.to_iff
  | succ j ih =>
    change (s∈stepHistoryRanges S T (p++[b]) ∧
      RangeSupported (stepHistoryRanges S T) j ((false::p)++[b]) t.1.1 t.2.1 ∧
      RangeSupported (stepHistoryRanges S T) j ((true::p)++[b]) t.1.2 t.2.2) ↔ _
    rw [stepHistoryRanges_append,ih,ih]

def stepHistoryEquiv (S : List Bool → Finset ℤ) (T : Finset ℤ) (j : ℕ) :
    SupportedHistory (stepHistoryRanges S T) (j+1) [] ≃
      T × SupportedHistory S j [] × SupportedHistory S j [] where
  toFun z :=
    (⟨z.val.1,by simpa using z.property.1⟩,
      ⟨(z.val.2.1.1,z.val.2.2.1),(stepHistoryRangeSupported S T j [] false _ _).mp z.property.2.1⟩,
      ⟨(z.val.2.1.2,z.val.2.2.2),(stepHistoryRangeSupported S T j [] true _ _).mp z.property.2.2⟩)
  invFun z := ⟨(z.1.val,((z.2.1.val.1,z.2.2.val.1),z.2.1.val.2,z.2.2.val.2)),
    ⟨by simp,
      (stepHistoryRangeSupported S T j [] false _ _).mpr z.2.1.property,
      (stepHistoryRangeSupported S T j [] true _ _).mpr z.2.2.property⟩⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by rcases z with ⟨s,l,r⟩; rfl

theorem sum_stepHistory {A : Type*} [AddCommMonoid A]
    (S : List Bool → Finset ℤ) (T : Finset ℤ) (j : ℕ) (F : ℤ → HistoryReconstruction.Tree (j+1) → A) :
    (∑z:SupportedHistory (stepHistoryRanges S T) (j+1) [],F z.val.1 z.val.2) =
      ∑s∈T,∑l:SupportedHistory S j [],∑r:SupportedHistory S j [],
        F s ((l.val.1,r.val.1),l.val.2,r.val.2) := by
  rw [← (stepHistoryEquiv S T j).symm.sum_comp]
  simp only [Fintype.sum_prod_type,stepHistoryEquiv]
  exact (Finset.sum_subtype (p := fun s:ℤ => s∈T) (F := inferInstance) T
    (fun _ => Iff.rfl) (fun s => ∑l:SupportedHistory S j [],∑r:SupportedHistory S j [],
      F s ((l.val.1,r.val.1),l.val.2,r.val.2))).symm

end Ostmann.Characters.Template

end

end OAI
