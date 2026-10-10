import OAI.Probability.InvariantIsing.Fields.FieldScalarComposition

namespace OAI

/-! Composition of an earlier conditional spin square with an unchanged
later scalar recursion. This keeps the ordinary Gaussian root separate. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldPrefixIndex (P S : List (ℝ × ℝ≥0)) (i : Fin (P.length + 1)) :
    Fin ((P ++ S).length + 1) :=
  ⟨i.val, by simp only [List.length_append]; omega⟩

lemma fieldScalarSquares_append_prefix (P S : List (ℝ × ℝ≥0)) (F a : ℝ → ℝ)
    (i : Fin (P.length + 1)) :
    fieldScalarSquares (P ++ S) F a (fieldPrefixIndex P S i) =
      fieldScalarSquares P (fieldScalarValue S F) (fieldScalarMean S F a) i := by
  induction P with
  | nil =>
    have hi : i = 0 := by
      apply Fin.ext
      change i.val = 0
      have hi := i.isLt
      simp only [List.length_nil, zero_add] at hi
      omega
    subst i
    have he : fieldPrefixIndex [] S 0 = 0 := by apply Fin.ext; rfl
    rw [he]
    funext z
    simp only [List.nil_append, fieldScalarSquares_zero, fieldScalarSquares]
  | cons av P ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · have he : fieldPrefixIndex (av :: P) S 0 = 0 := by apply Fin.ext; rfl
      rw [he]
      funext z
      rw [fieldScalarSquares_zero, fieldScalarSquares_zero, fieldScalarMean_append]
    · have he : fieldPrefixIndex (av :: P) S j.succ = (fieldPrefixIndex P S j).succ := by
        apply Fin.ext
        rfl
      rw [he]
      change fieldSpinTransition av.1 av.2 (fieldScalarValue (P ++ S) F)
        (fieldScalarSquares (P ++ S) F a (fieldPrefixIndex P S j)) = _
      rw [fieldScalarValue_append, ih]
      rfl

end InvariantIsing

end

end OAI
