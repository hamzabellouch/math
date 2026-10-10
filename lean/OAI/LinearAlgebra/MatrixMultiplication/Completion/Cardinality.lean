import OAI.LinearAlgebra.MatrixMultiplication.Completion.Labels
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionCardinality

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
attribute [local instance] Classical.propDecidable Classical.decEq

universe uCoord
variable {X Y Z : Type uCoord}

def conditionalCount [Fintype X] [Fintype Y] [Fintype Z]
    (S : FlaggedTensor X Y Z) (c : Color) : ℕ :=
  Fintype.card {a : Leaf S // leafColor S a = c}

private abbrev AllowedLeaf (S : FlaggedTensor X Y Z) (center output : Color) :=
  {a : Leaf S // leafColor S a = center ∨ leafColor S a = output}

private def centerLeafEquiv (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    {a : Leaf (complete S center m) //
      leafColor (complete S center m) a = center} ≃
      (Fin m → {a : Leaf S // leafColor S a = center}) :=
  (conditionalLeafEquiv S center center m).trans
    ((Equiv.subtypeEquivRight (fun w => by simp [raisedFlag])).trans
      Equiv.subtypePiEquivPi)

private def noncenterLeafEquiv (S : FlaggedTensor X Y Z) (center output : Color)
    (m : ℕ) (h : center ≠ output) :
    {a : Leaf (complete S center m) //
      leafColor (complete S center m) a = output} ≃
      {w : Fin m → AllowedLeaf S center output //
        ¬ ∀ i, leafColor S (w i).val = center} :=
  (conditionalLeafEquiv S center output m).trans
    { toFun := fun w =>
        ⟨fun i => ⟨w.val i, w.property.2 i⟩, by
          intro hall
          have hex : ∃ i, leafColor S (w.val i) = output := by
            simpa only [raisedFlag, ite_eq_right h] using w.property.1
          obtain ⟨i, hi⟩ := hex
          exact h ((hall i).symm.trans hi)⟩
      invFun := fun w =>
        ⟨fun i => (w.val i).val, by
          constructor
          · simp only [raisedFlag, ite_eq_right h]
            by_contra hex
            apply w.property
            intro i
            rcases (w.val i).property with hc | ho
            · exact hc
            · exact False.elim (hex ⟨i, ho⟩)
          · exact fun i => (w.val i).property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

private def allCenterEquiv (S : FlaggedTensor X Y Z) (center output : Color)
    (m : ℕ) :
    {w : Fin m → AllowedLeaf S center output //
      ∀ i, leafColor S (w i).val = center} ≃
      (Fin m → {a : Leaf S // leafColor S a = center}) where
  toFun w i := ⟨(w.val i).val, w.property i⟩
  invFun w := ⟨fun i => ⟨(w i).val, Or.inl (w i).property⟩,
    fun i => (w i).property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

variable [Fintype X] [Fintype Y] [Fintype Z]

private theorem card_allowedLeaf (S : FlaggedTensor X Y Z) (center output : Color)
    (h : center ≠ output) :
    Fintype.card (AllowedLeaf S center output) =
      conditionalCount S center + conditionalCount S output := by
  apply Fintype.card_subtype_or_disjoint
  exact Pi.disjoint_iff.mpr fun a => Prop.disjoint_iff.mpr
    (fun ha => h (ha.1.symm.trans ha.2))

theorem count_complete_center (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    conditionalCount (complete S center m) center = conditionalCount S center ^ m := by
  calc
    conditionalCount (complete S center m) center =
        Fintype.card (Fin m → {a : Leaf S // leafColor S a = center}) :=
      Fintype.card_congr (centerLeafEquiv S center m)
    _ = conditionalCount S center ^ m := by simp [conditionalCount]

theorem count_complete_noncenter (S : FlaggedTensor X Y Z) (center output : Color)
    (m : ℕ) (h : center ≠ output) :
    conditionalCount (complete S center m) output =
      (conditionalCount S center + conditionalCount S output) ^ m -
        conditionalCount S center ^ m := by
  have hall : Fintype.card {w : Fin m → AllowedLeaf S center output //
      ∀ i, leafColor S (w i).val = center} = conditionalCount S center ^ m := by
    calc
      _ = Fintype.card (Fin m → {a : Leaf S // leafColor S a = center}) :=
        Fintype.card_congr (allCenterEquiv S center output m)
      _ = _ := by simp [conditionalCount]
  calc
    conditionalCount (complete S center m) output =
        Fintype.card {w : Fin m → AllowedLeaf S center output //
          ¬ ∀ i, leafColor S (w i).val = center} :=
      Fintype.card_congr (noncenterLeafEquiv S center output m h)
    _ = Fintype.card (Fin m → AllowedLeaf S center output) -
        Fintype.card {w : Fin m → AllowedLeaf S center output //
          ∀ i, leafColor S (w i).val = center} := Fintype.card_subtype_compl _
    _ = (conditionalCount S center + conditionalCount S output) ^ m -
        conditionalCount S center ^ m := by
      rw [hall, Fintype.card_fun, Fintype.card_fin, card_allowedLeaf S center output h]

theorem count_complete (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) (c : Color) :
    conditionalCount (complete S center m) c =
      if c = center then conditionalCount S center ^ m
      else (conditionalCount S center + conditionalCount S c) ^ m -
        conditionalCount S center ^ m := by
  by_cases h : c = center
  · subst c
    simpa using count_complete_center S center m
  · simpa [h] using count_complete_noncenter S center c m (Ne.symm h)

end MatrixMultiplication.CompletionCardinality

end

end OAI
