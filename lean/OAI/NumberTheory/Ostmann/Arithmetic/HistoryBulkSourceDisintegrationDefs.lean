import OAI.NumberTheory.Ostmann.Conclusion.SelectedPermutation
import OAI.NumberTheory.Ostmann.Construction.AssignmentReinsert

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkSourceDisintegration
open Construction Conclusion

abbrev NonbulkPosition (T : List SourceSlot) :=
  {i : Fin T.length // (T.get i).role ≠ .bulk}

abbrev NonbulkSample (sources : SourceFamily) (T : List SourceSlot) :=
  (i : NonbulkPosition T) → (sources (T.get i.val).origin).Sample

def nonbulkPrior (sources : SourceFamily) (T : List SourceSlot) :
    FinitePrior (NonbulkSample sources T) :=
  dependentProductPrior (fun i : NonbulkPosition T => (sources (T.get i.val).origin).law)

def bulkPrior (bulk : PrimeSource) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    FinitePrior (ι → bulk.Sample) :=
  dependentProductPrior (fun _ : ι => bulk.law)

variable (sources : SourceFamily) (T : List SourceSlot) (bulk : PrimeSource)
variable (hbulk : ∀i : BulkPosition T, sources (T.get i.val).origin = bulk)
variable {ι : Type*} (e : BulkPosition T ≃ ι)

def bulkSampleEquiv :
    ((i : BulkPosition T) → (sources (T.get i.val).origin).Sample) ≃ (ι → bulk.Sample) :=
  (Equiv.piCongrRight (fun i : BulkPosition T => sourceSampleEquiv (hbulk i))).trans
    (Equiv.arrowCongr e (Equiv.refl bulk.Sample))

def coordinateEquiv : SourceAssignment sources T ≃ NonbulkSample sources T × (ι → bulk.Sample) where
  toFun x := (fun i => x i.val, fun u => sourceSampleEquiv (hbulk (e.symm u)) (x (e.symm u).val))
  invFun y i := if hi : (T.get i).role = .bulk then
    sourceSampleEquiv (hbulk ⟨i,hi⟩).symm (y.2 (e ⟨i,hi⟩)) else y.1 ⟨i,hi⟩
  left_inv x := by
    funext i
    apply Subtype.ext
    dsimp only
    split_ifs with hi
    · simp only [sourceSampleEquiv_val]
      exact congrArg (fun j : BulkPosition T => (x j.val).val) (e.symm_apply_apply ⟨i,hi⟩)
    · rfl
  right_inv y := by
    apply Prod.ext
    · funext i
      dsimp only
      simp only [i.property,dite_false]
    · funext u
      apply Subtype.ext
      have hu : (T.get (e.symm u).val).role = .bulk := (e.symm u).property
      simp only [sourceSampleEquiv_val,hu,dite_true]
      exact congrArg (fun z => (y.2 z).val) (e.apply_symm_apply u)

@[simp] theorem coordinateEquiv_nonbulk_apply (x : SourceAssignment sources T)
    (i : NonbulkPosition T) :
    (coordinateEquiv sources T bulk hbulk e x).1 i = x i.val := rfl

@[simp] theorem coordinateEquiv_bulk_apply (x : SourceAssignment sources T) (u : ι) :
    (coordinateEquiv sources T bulk hbulk e x).2 u =
      sourceSampleEquiv (hbulk (e.symm u)) (x (e.symm u).val) := rfl

@[simp] theorem coordinateEquiv_bulk_val (x : SourceAssignment sources T) (u : ι) :
    ((coordinateEquiv sources T bulk hbulk e x).2 u).val = (x (e.symm u).val).val := by
  rw [coordinateEquiv_bulk_apply,sourceSampleEquiv_val]

@[simp] theorem coordinateEquiv_bulk_mass (x : SourceAssignment sources T) (u : ι) :
    bulk.law.mass ((coordinateEquiv sources T bulk hbulk e x).2 u) =
      (sources (T.get (e.symm u).val).origin).law.mass (x (e.symm u).val) := by
  rw [coordinateEquiv_bulk_apply,sourceSampleEquiv_mass]

end Ostmann.Arithmetic.HistoryBulkSourceDisintegration

end

end OAI
