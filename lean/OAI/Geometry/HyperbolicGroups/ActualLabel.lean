import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualPosition

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma squareSide_field (q : Square n w) (i : Fin 4) :
    (squareSide n w q i).1 = .inl ((q.2.val (squareField q.1 i)).1) := by
  fin_cases i <;>
    simp only [squareSide,letterDart,stepLetter,apply_ite,inverseLetter]
  all_goals simp [extendRow,squareField,rowSupport,squareSupport,MasterGraph.first,MasterGraph.second]
  all_goals split_ifs <;> rfl

lemma square_value_congr {q q' : Square n w} (h : q = q') (v : Field)
    (h1 : v ∈ rowSupport (.inr (.inr q.1))) (h2 : v ∈ rowSupport (.inr (.inr q'.1))) :
    q.2.val ⟨v,h1⟩ = q'.2.val ⟨v,h2⟩ := by
  cases h
  rfl

lemma representative_value (p : RawPosition n w d) :
    (walkLabel n w d (rawRepresentative n w d p)).1 =
      .inl ((occurrenceValues n w d (rawToPosition n w d p)).1) := by
  rcases p with a | (⟨b,e⟩ | (⟨q,i⟩ | ⟨q,i⟩))
  · change Sum.inl (a.val loose).1 = _
    simp only [rawToPosition,occurrenceValues,Equiv.symm_apply_apply]
  · change Sum.inl ((fanLetter n w ⟨b,e⟩).1) = _
    simp only [rawToPosition,occurrenceValues]
    apply congrArg Sum.inl
    apply congrArg Prod.fst
    exact fan_value_congr n w (Equiv.symm_apply_apply (enumFan n w) b).symm e.val _ _
  · change (squareSide n w q i).1 = _
    rw [squareSide_field]
    simp only [rawToPosition,occurrenceValues]
    apply congrArg Sum.inl
    apply congrArg Prod.fst
    exact square_value_congr n w ((enumSquare n w).symm_apply_apply q).symm _ _ _
  · change Sum.inl (q.val i).1 = _
    simp only [rawToPosition,occurrenceValues,Equiv.symm_apply_apply]

/-- Contact labels are compared only after forgetting orientation. Equal
unsigned labels are not used to identify distinct indexed positions. -/
lemma raw_label_value (s : WalkStep n w d) (hr : isLetter n w (walkLabel n w d s) = true) :
    (walkLabel n w d s).1 =
      .inl ((occurrenceValues n w d (rawToPosition n w d (rawPosition n w d s))).1) := by
  rcases raw_step_cases n w d s hr with h | h
  · conv_lhs => rw [h]
    exact representative_value n w d _
  · conv_lhs => rw [h,walkOpposite_label]
    exact representative_value n w d _

end HyperbolicObstruction.ConeSkeleton
end

end OAI
