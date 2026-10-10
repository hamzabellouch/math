import OAI.Probability.InvariantIsing.Fields.FieldScalarComposition

namespace OAI

/-! Inserting a zero covariance increment preserves the scalar Ising
value and spin mean. Its adjacent overlap levels are the same. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarValue_insert_zero (P S : List (ℝ × ℝ≥0)) (a : ℝ) (F : ℝ → ℝ) :
    fieldScalarValue (P ++ (a, 0) :: S) F = fieldScalarValue (P ++ S) F := by
  rw [fieldScalarValue_append, fieldScalarValue_append]
  change fieldScalarValue P (gaussianOperator a 0 (fieldScalarValue S F)) = _
  rw [gaussianOperator_zero_variance]

lemma fieldScalarMean_insert_zero (P S : List (ℝ × ℝ≥0)) (a : ℝ) (F b : ℝ → ℝ) :
    fieldScalarMean (P ++ (a, 0) :: S) F b = fieldScalarMean (P ++ S) F b := by
  rw [fieldScalarMean_append, fieldScalarMean_append]
  change fieldScalarMean P (gaussianOperator a 0 (fieldScalarValue S F))
    (fieldSpinTransition a 0 (fieldScalarValue S F) (fieldScalarMean S F b)) = _
  rw [gaussianOperator_zero_variance]
  have hs : fieldSpinTransition a 0 (fieldScalarValue S F) (fieldScalarMean S F b) =
      fieldScalarMean S F b := funext (fieldSpinTransition_zero_variance _ _ _)
  rw [hs]

/-- The natural-index form of a scalar square. All indices used by the
finite field are at most the length; the terminal extension avoids casts
in zero-increment insertion. -/
def fieldScalarSquareAt : List (ℝ × ℝ≥0) → (ℝ → ℝ) → (ℝ → ℝ) → ℕ → ℝ → ℝ
  | [], _, b, _ => fun z => (b z) ^ 2
  | av :: L, F, b, 0 => fun z => (fieldScalarMean (av :: L) F b z) ^ 2
  | av :: L, F, b, i + 1 =>
      fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarSquareAt L F b i)

lemma fieldScalarSquareAt_eq (L : List (ℝ × ℝ≥0)) (F b : ℝ → ℝ)
    (i : Fin (L.length + 1)) :
    fieldScalarSquareAt L F b i.val = fieldScalarSquares L F b i := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change fieldSpinTransition av.1 av.2 (fieldScalarValue L F)
        (fieldScalarSquareAt L F b j.val) = _
      rw [ih]
      rfl

lemma fieldScalarSquareAt_insert_zero (P S : List (ℝ × ℝ≥0))
    (a : ℝ) (F b : ℝ → ℝ) (i : ℕ) :
    fieldScalarSquareAt (P ++ (a, 0) :: S) F b i =
      fieldScalarSquareAt (P ++ S) F b (if i ≤ P.length then i else i - 1) := by
  induction P generalizing i with
  | nil =>
    cases i with
    | zero =>
      simp only [List.nil_append, List.length_nil, le_refl, ite_true,
        fieldScalarSquareAt, fieldScalarMean]
      have hs : fieldSpinTransition a 0 (fieldScalarValue S F) (fieldScalarMean S F b) =
          fieldScalarMean S F b := funext (fieldSpinTransition_zero_variance _ _ _)
      rw [hs]
      cases S <;> rfl
    | succ i =>
      simp only [List.nil_append, List.length_nil,
        Nat.add_sub_cancel, fieldScalarSquareAt]
      exact funext (fieldSpinTransition_zero_variance _ _ _)
  | cons av P ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_le, ite_true, List.cons_append, fieldScalarSquareAt]
      have he := fieldScalarMean_insert_zero (av :: P) S a F b
      simpa only [List.cons_append] using congrArg (fun f : ℝ → ℝ => fun z => f z ^ 2) he
    | succ i =>
      have hv := fieldScalarValue_insert_zero P S a F
      simp only [List.cons_append, List.length_cons, Nat.succ_le_succ_iff]
      by_cases hi : i ≤ P.length
      · simp only [hi, ite_true, fieldScalarSquareAt]
        rw [hv, ih, ite_eq_left hi]
      · have hp : 0 < i := by omega
        simp only [hi, ite_false, fieldScalarSquareAt]
        have he : i + 1 - 1 = (i - 1) + 1 := by omega
        rw [he]
        change fieldSpinTransition av.1 av.2 (fieldScalarValue (P ++ (a, 0) :: S) F)
          (fieldScalarSquareAt (P ++ (a, 0) :: S) F b i) =
          fieldSpinTransition av.1 av.2 (fieldScalarValue (P ++ S) F)
            (fieldScalarSquareAt (P ++ S) F b (i - 1))
        rw [hv, ih, ite_eq_right hi]

end InvariantIsing

end

end OAI
