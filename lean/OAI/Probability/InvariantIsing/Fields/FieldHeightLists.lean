import OAI.Probability.InvariantIsing.Fields.FieldHeightCone

namespace OAI

/-! Exact transition-list laws for a literal height update. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldAllIncrements_withHeights (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    fieldAllIncrements (fieldWithHeights h r hr0 hrmono) =
      List.ofFn (fun j : Fin (h.depth + 1) =>
        (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement r j))) := by
  unfold fieldAllIncrements
  apply congrArg List.ofFn
  funext j
  apply Prod.ext
  · rfl
  · exact (Real.toNNReal_of_nonneg (fieldIncrement_nonneg (fieldWithHeights h r hr0 hrmono) j)).symm

lemma fieldAllIncrements_update_interior (h : FieldStep) (j : Fin h.depth) (t : ℝ)
    (ht : Function.update h.height j.castSucc (h.height j.castSucc + t) ∈
      fieldStrictHeightCone h.depth) :
    fieldAllIncrements (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t)) ht) =
      fieldAdjacentIncrements ((fieldAllIncrements h).take j.val)
        ((fieldAllIncrements h).drop (j.val + 2))
        (fieldIncrement h j.castSucc).2 (fieldIncrement h j.succ).2
        (fieldIncrement h j.castSucc).1 (fieldIncrement h j.succ).1 t := by
  rw [fieldStepOfStrictHeights, fieldAllIncrements_withHeights]
  exact updated_increments_interior h j t

lemma fieldAllIncrements_update_final (h : FieldStep) (t : ℝ)
    (ht : Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t) ∈
      fieldStrictHeightCone h.depth) :
    fieldAllIncrements (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) ht) =
      fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
        (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 t := by
  rw [fieldStepOfStrictHeights, fieldAllIncrements_withHeights]
  exact updated_increments_final h t

lemma fieldAdjacentIncrements_root (P S : List (ℝ × ℝ≥0))
    (root : ℝ≥0) (a b ζ η t : ℝ) :
    fieldAdjacentIncrements ((0, root) :: P) S a b ζ η t =
      (0, root) :: (P ++ (ζ, Real.toNNReal (a + t)) :: (η, Real.toNNReal (b - t)) :: S) := rfl

end InvariantIsing

end

end OAI
