import OAI.Probability.SignedSweeps.MarkedCompression
import OAI.Probability.SignedSweeps.OccupiedGeometry

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma routeSize_sum {X Y Z J : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype J] (e : X ⊕ Y ≃ Z) (f : Z → J) (j : J) :
    routeSize (fun x => f (e (Sum.inl x))) j +
      routeSize (fun y => f (e (Sum.inr y))) j = routeSize f j := by
  let ee : {z : X ⊕ Y // f (e z) = j} ≃ {z : Z // f z = j} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  have h₁ := Fintype.card_congr ee
  have h₂ := Fintype.card_congr (Equiv.subtypeSum (p := fun z : X ⊕ Y => f (e z) = j))
  simpa only [routeSize, Fintype.card_sum] using h₂.symm.trans h₁

lemma routeSize_occupancy {l m : ℕ} (f : Fin l → Fin m) (j : Fin m) :
    routeSize f j = (occupancy f j).val := by
  simp only [routeSize, occupancy, Fintype.card_subtype]

lemma freeLineSize_add_marks {J : Type*} [Fintype J] {p l n : ℕ} {t : J → ℕ}
    (h : p+l=n) (z : MarkedAssignment l n) (E : (Σ j, Fin (t j)) ≃ Fin n) (j : J) :
    routeSize (freeRoute E (markedInjection h z)) j +
      routeSize (markedRoutes (fun x => (E.symm x).1) z) j = t j := by
  have hh := routeSize_sum (markedAllSites h z) (fun x => (E.symm x).1) j
  have hc := Fintype.card_congr (blockFiberEquiv E j)
  have hh' : routeSize (freeRoute E (markedInjection h z)) j +
      routeSize (markedRoutes (fun x => (E.symm x).1) z) j =
        routeSize (fun x => (E.symm x).1) j := hh
  apply hh'.trans
  unfold routeSize
  exact (Fintype.card_congr (blockFiberEquiv E j).symm).trans (Fintype.card_fin _)

def markedBoardPlacement {l n s m : ℕ} (e : Fin n ≃ Fin s × Fin m) :
    MarkedAssignment l n ≃ HolePlacement s m l where
  toFun z := ⟨fun i => e (z i), e.injective.comp z.injective⟩
  invFun z := ⟨fun i => e.symm (z.1 i), e.symm.injective.comp z.2⟩
  left_inv z := by ext i; simp
  right_inv z := by apply Subtype.ext; funext i; simp

@[simp] lemma markedBoardPlacement_apply {l n s m : ℕ}
    (e : Fin n ≃ Fin s × Fin m) (z : MarkedAssignment l n) (i : Fin l) :
    (markedBoardPlacement e z).1 i = e (z i) := rfl

lemma occupiedBoard_missing_bound {A B : Type*} [Fintype A] [Fintype B]
    {p l n : ℕ} (h : p+l=n) (e : Fin n ≃ A × B) (z : MarkedAssignment l n) :
    missingCellFactor (occupiedBoard e (markedInjection h z)) ≤ Real.exp (l : ℝ) := by
  have hc : n = Fintype.card A * Fintype.card B := by
    simpa only [Fintype.card_fin, Fintype.card_prod] using Fintype.card_congr e
  simpa only [occupiedBoard_card, ← hc, show n-p=l by omega] using
    missingCellFactor_le_exp_holes (occupiedBoard e (markedInjection h z))

end SignedSweeps
end

end OAI
