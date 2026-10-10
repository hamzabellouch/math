import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Geometry

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev ProducedPositions {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :=
  Σ h : Produced K tick, Fin (population allocation dilation h.val)

abbrev SplitPositions {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :=
  Σ w : Active K tick, Σ b : w.val.1.Branch,
    Bool × Fin (branchPopulation allocation dilation w.val b)

def halfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (branchPopulation allocation dilation w b)) :
    Fin (population allocation dilation (w.1.child b right, w.2)) :=
  ⟨i.val, by rw [branchPopulation_half]; exact i.isLt⟩

def unhalfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (population allocation dilation (w.1.child b right, w.2))) :
    Fin (branchPopulation allocation dilation w b) :=
  ⟨i.val, by rw [← branchPopulation_half allocation dilation w b right]; exact i.isLt⟩

@[simp] theorem unhalf_halfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (branchPopulation allocation dilation w b)) :
    unhalfPosition allocation dilation w b right (halfPosition allocation dilation w b right i) = i := rfl

@[simp] theorem half_unhalfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (population allocation dilation (w.1.child b right, w.2))) :
    halfPosition allocation dilation w b right (unhalfPosition allocation dilation w b right i) = i := rfl

def splitToProduced {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    SplitPositions (K := K) (tick := tick) allocation dilation →
      ProducedPositions (K := K) (tick := tick) allocation dilation := by
  rintro ⟨⟨⟨w, phi⟩, hw⟩, b, right, i⟩
  cases w with
  | stageA h =>
      exact ⟨⟨(.afterA ⟨h, b, right⟩, phi), hw.symm⟩,
        halfPosition allocation dilation (.stageA h, phi) b right i⟩
  | stageB h =>
      let child : AfterB K := ⟨h, b, right⟩
      let j := halfPosition allocation dilation (.stageB h, phi) b right i
      by_cases hp : positive (bShape child) = true
      · let part := bSubdivisionPositionEquiv allocation dilation ⟨child, hp⟩ phi j
        exact ⟨⟨(.partC (⟨child, hp⟩, part.1), phi), hw.symm⟩, part.2⟩
      · exact ⟨⟨(.afterB child, phi), hw.symm, hp⟩, j⟩
  | stageC h =>
      exact ⟨⟨(.afterC (h, b, right), phi), hw.symm⟩,
        halfPosition allocation dilation (.stageC h, phi) b right i⟩

def producedToSplit {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    ProducedPositions (K := K) (tick := tick) allocation dilation →
      SplitPositions (K := K) (tick := tick) allocation dilation := by
  rintro ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h =>
      exact ⟨⟨(.stageA h.1, phi), hp.symm⟩, h.2.1, h.2.2,
        unhalfPosition allocation dilation (.stageA h.1, phi) h.2.1 h.2.2 i⟩
  | afterB h =>
      exact ⟨⟨(.stageB h.1, phi), hp.1.symm⟩, h.2.1, h.2.2,
        unhalfPosition allocation dilation (.stageB h.1, phi) h.2.1 h.2.2 i⟩
  | partC h =>
      let j := (bSubdivisionPositionEquiv allocation dilation h.1 phi).symm ⟨h.2, i⟩
      exact ⟨⟨(.stageB h.1.val.1, phi), hp.symm⟩, h.1.val.2.1, h.1.val.2.2,
        unhalfPosition allocation dilation (.stageB h.1.val.1, phi)
          h.1.val.2.1 h.1.val.2.2 j⟩
  | afterC h =>
      exact ⟨⟨(.stageC h.1, phi), hp.symm⟩, h.2.1, h.2.2,
        unhalfPosition allocation dilation (.stageC h.1, phi) h.2.1 h.2.2 i⟩

theorem producedToSplit_splitToProduced {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : SplitPositions (K := K) (tick := tick) allocation dilation) :
    producedToSplit allocation dilation (splitToProduced allocation dilation p) = p := by
  rcases p with ⟨⟨⟨w, phi⟩, hw⟩, b, right, i⟩
  cases w with
  | stageA h => rfl
  | stageB h =>
      by_cases hp : positive (bShape (⟨h, b, right⟩ : AfterB K)) = true
      · dsimp only [splitToProduced]
        rw [dite_eq_left hp]
        dsimp only [producedToSplit]
        simp only [Sigma.eta]
        let lift : Fin (population allocation dilation
            (.afterB ⟨h, b, right⟩, phi)) →
            SplitPositions (K := K) (tick := tick) allocation dilation :=
          fun j => ⟨⟨(.stageB h, phi), hw⟩, b, right,
            unhalfPosition allocation dilation (.stageB h, phi) b right j⟩
        exact congrArg lift ((bSubdivisionPositionEquiv allocation dilation
          ⟨⟨h, b, right⟩, hp⟩ phi).symm_apply_apply
            (halfPosition allocation dilation (.stageB h, phi) b right i))
      · dsimp only [splitToProduced]
        rw [dite_eq_right hp]
        rfl
  | stageC h => rfl

theorem splitToProduced_producedToSplit {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : ProducedPositions (K := K) (tick := tick) allocation dilation) :
    splitToProduced allocation dilation (producedToSplit allocation dilation p) = p := by
  rcases p with ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h => rfl
  | afterB h =>
      rcases h with ⟨a, b, right⟩
      dsimp only [producedToSplit, splitToProduced]
      rw [dite_eq_right hp.2]
      rfl
  | partC h =>
      rcases h with ⟨⟨⟨a, b, right⟩, hb⟩, part⟩
      dsimp only [producedToSplit, splitToProduced]
      rw [dite_eq_left hb]
      let lift : (Σ j : Fin 3,
          Fin (population allocation dilation
            (.partC (⟨⟨a, b, right⟩, hb⟩, j), phi))) →
          ProducedPositions (K := K) (tick := tick) allocation dilation :=
        fun q => ⟨⟨(.partC (⟨⟨a, b, right⟩, hb⟩, q.1), phi), hp⟩, q.2⟩
      exact congrArg lift ((bSubdivisionPositionEquiv allocation dilation
        ⟨⟨a, b, right⟩, hb⟩ phi).apply_symm_apply ⟨part, i⟩)
  | afterC h => rfl

def producedPositionEquiv {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    ProducedPositions (K := K) (tick := tick) allocation dilation ≃
      SplitPositions (K := K) (tick := tick) allocation dilation where
  toFun := producedToSplit allocation dilation
  invFun := splitToProduced allocation dilation
  left_inv := splitToProduced_producedToSplit allocation dilation
  right_inv := producedToSplit_splitToProduced allocation dilation

theorem producedPositionEquiv_parent {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : ProducedPositions (K := K) (tick := tick) allocation dilation) :
    (producedPositionEquiv allocation dilation p).1 = productionParent p.1 := by
  rcases p with ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h => rfl
  | afterB h => rfl
  | partC h => rfl
  | afterC h => rfl

theorem producedPositionEquiv_shape {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : ProducedPositions (K := K) (tick := tick) allocation dilation) :
    currentPhysicalShape p.1.val =
      physicalShape (producedPositionEquiv allocation dilation p).1.val.2
        (halfShape (producedPositionEquiv allocation dilation p).1.val.1.parentShape
          ((producedPositionEquiv allocation dilation p).1.val.1.splitShape
            (producedPositionEquiv allocation dilation p).2.1)
          (producedPositionEquiv allocation dilation p).2.2.1) := by
  rcases p with ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h => rfl
  | afterB h => rfl
  | partC h => rfl
  | afterC h => rfl

theorem producedPositionEquiv_length {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : ProducedPositions (K := K) (tick := tick) allocation dilation) :
    currentLength p.1.val.1 = (producedPositionEquiv allocation dilation p).1.val.1.halfLength := by
  rcases p with ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h => rfl
  | afterB h => rfl
  | partC h => rfl
  | afterC h => rfl

end MatrixMultiplication.AllFieldHistory

end

end OAI
