import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds
open Construction HistoryPairPattern HistoryActiveCoordinates
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates
attribute [local instance] Classical.propDecidable
variable {l : ℕ}

theorem giant_bulk_disjoint (h k : History l) :
    Disjoint (giantCoordinates h k) (bulkCoordinates h k) := by
  apply Finset.disjoint_left.mpr
  intro i hi hb
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hi
  exact left_giant_not_mem h k b hb

def jointInsert (h k : History l) {κ ι : Type*}
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k → ℝ) (u : κ → ℝ) (x : ι → ℝ) : PairKey h k → ℝ :=
  HistoryActiveCoordinates.insert (bulkCoordinates h k)
    (HistoryActiveCoordinates.insert (giantCoordinates h k) background (u ∘ eG.symm)) (x ∘ eB.symm)

theorem jointInsert_commute (h k : History l) {κ ι : Type*}
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k → ℝ) (u : κ → ℝ) (x : ι → ℝ) :
    jointInsert h k eG eB background u x=
      HistoryActiveCoordinates.insert (giantCoordinates h k)
        (HistoryActiveCoordinates.insert (bulkCoordinates h k) background (x ∘ eB.symm)) (u ∘ eG.symm) := by
  funext i
  by_cases hg : i∈giantCoordinates h k
  · have hb : i∉bulkCoordinates h k := fun hb => Finset.disjoint_left.mp (giant_bulk_disjoint h k) hg hb
    simp only [jointInsert,HistoryActiveCoordinates.insert,dite_eq_left hg,dite_eq_right hb]
  · by_cases hb : i∈bulkCoordinates h k <;>
      simp only [jointInsert,HistoryActiveCoordinates.insert,dite_eq_right hg,hb,↓reduceDIte]

@[simp] theorem jointInsert_giant (h k : History l) {κ ι : Type*}
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k → ℝ) (u : κ → ℝ) (x : ι → ℝ) (j : κ) :
    jointInsert h k eG eB background u x (eG j).val=u j := by
  rw [jointInsert_commute]
  simp only [HistoryActiveCoordinates.insert,dite_eq_left (eG j).property,Function.comp_apply]
  change u (eG.symm (eG j))=u j
  rw [Equiv.symm_apply_apply]

@[simp] theorem jointInsert_bulk (h k : History l) {κ ι : Type*}
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k → ℝ) (u : κ → ℝ) (x : ι → ℝ) (j : ι) :
    jointInsert h k eG eB background u x (eB j).val=x j := by
  simp only [jointInsert,HistoryActiveCoordinates.insert,dite_eq_left (eB j).property,Function.comp_apply]
  change x (eB.symm (eB j))=x j
  rw [Equiv.symm_apply_apply]

theorem jointInsert_frozen (h k : History l) {κ ι : Type*}
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k → ℝ) (u : κ → ℝ) (x : ι → ℝ) (j : PairKey h k)
    (hg : j∉giantCoordinates h k) (hb : j∉bulkCoordinates h k) :
    jointInsert h k eG eB background u x j=background j := by
  simp only [jointInsert,HistoryActiveCoordinates.insert,dite_eq_right hg,dite_eq_right hb]

theorem jointInsert_positive (h k : History l) {κ ι : Type*}
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k → ℝ) (u : κ → ℝ) (x : ι → ℝ)
    (hbackground : ∀i,0<background i) (hu : ∀i,0<u i) (hx : ∀i,0<x i) :
    ∀i,0<jointInsert h k eG eB background u x i :=
  insert_positive _ _ _ (insert_positive _ _ _ hbackground (fun i=>hu (eG.symm i)))
    (fun i=>hx (eB.symm i))

end Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds

end

end OAI
