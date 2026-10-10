import OAI.Probability.InvariantIsing.Fields.FieldConstantPrefix
import OAI.Probability.InvariantIsing.Fields.FieldSpinLinear

namespace OAI

/-! Exact concatenation and linear propagation identities for the finite
scalar field recursion. The exponents may include the zero root level. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarValue_append (P S : List (ℝ × ℝ≥0)) (F : ℝ → ℝ) :
    fieldScalarValue (P ++ S) F = fieldScalarValue P (fieldScalarValue S F) := by
  exact List.foldr_append

lemma fieldScalarMean_append (P S : List (ℝ × ℝ≥0)) (F a : ℝ → ℝ) :
    fieldScalarMean (P ++ S) F a =
      fieldScalarMean P (fieldScalarValue S F) (fieldScalarMean S F a) := by
  induction P with
  | nil => rfl
  | cons av P ih =>
    simp only [List.cons_append, fieldScalarMean, fieldScalarValue_append, ih]

lemma fieldScalarMean_const_mul (P : List (ℝ × ℝ≥0)) (F a : ℝ → ℝ) (c : ℝ) :
    fieldScalarMean P F (fun z => c * a z) = fun z => c * fieldScalarMean P F a z := by
  induction P with
  | nil => rfl
  | cons av P ih =>
    simp only [fieldScalarMean, ih]
    funext z
    exact fieldSpinTransition_const_mul av.1 av.2 _ _ c z

/-- Index of a level in the suffix, after an unchanged prefix. -/
def fieldAppendIndex (P S : List (ℝ × ℝ≥0)) (i : Fin (S.length + 1)) :
    Fin ((P ++ S).length + 1) :=
  ⟨P.length + i.val, by simp only [List.length_append]; omega⟩

lemma fieldScalarSquares_append (P S : List (ℝ × ℝ≥0)) (F a : ℝ → ℝ)
    (i : Fin (S.length + 1)) :
    fieldScalarSquares (P ++ S) F a (fieldAppendIndex P S i) =
      fieldScalarMean P (fieldScalarValue S F) (fieldScalarSquares S F a i) := by
  induction P with
  | nil =>
    have hi : fieldAppendIndex [] S i = i := by apply Fin.ext; simp [fieldAppendIndex]
    rw [hi]
    rfl
  | cons av P ih =>
    have hi : fieldAppendIndex (av :: P) S i = (fieldAppendIndex P S i).succ := by
      apply Fin.ext
      simp only [fieldAppendIndex, List.length_cons, Fin.val_succ]
      omega
    rw [hi]
    change fieldSpinTransition av.1 av.2 (fieldScalarValue (P ++ S) F)
      (fieldScalarSquares (P ++ S) F a (fieldAppendIndex P S i)) = _
    rw [fieldScalarValue_append, ih]
    rfl

lemma fieldConstantPrefix_test_regular {I : Set ℝ} (hI : IsOpen I)
    (F : FieldSmoothFamily I) (P : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < (av.2 : ℝ)) (t : ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) {B : ℝ} (haB : ∀ z, |a z| ≤ B) :
    Measurable (fieldScalarMean P (fun z => F.U (t, z)) a) ∧
      ∀ z, |fieldScalarMean P (fun z => F.U (t, z)) a z| ≤ B := by
  induction P with
  | nil => exact ⟨ha, haB⟩
  | cons av P ih =>
    let hp := fun bv hb => hP bv (List.mem_cons_of_mem av hb)
    let G := fieldConstantPrefix hI F P hp
    have hv := fieldConstantPrefix_value hI F P hp t
    have hm : Measurable (fieldScalarValue P (fun z => F.U (t, z))) := by
      rw [← hv]
      exact G.mU.comp (by fun_prop)
    have hg : HasLinearGrowth (fieldScalarValue P (fun z => F.U (t, z))) := by
      rw [← hv]
      exact G.growth t
    have ht := ih hp
    exact ⟨measurable_fieldSpinTransition av.1 av.2 hm ht.1,
      fieldSpinTransition_bound av.1 av.2 hm hg ht.2⟩

lemma fieldConstantPrefix_test_affine {I : Set ℝ} (hI : IsOpen I)
    (F : FieldSmoothFamily I) (P : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < (av.2 : ℝ)) (t : ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) {B : ℝ} (haB : ∀ z, |a z| ≤ B) (c k : ℝ) :
    fieldScalarMean P (fun z => F.U (t, z)) (fun z => c + k * a z) =
      fun z => c + k * fieldScalarMean P (fun z => F.U (t, z)) a z := by
  induction P with
  | nil => rfl
  | cons av P ih =>
    let hp := fun bv hb => hP bv (List.mem_cons_of_mem av hb)
    let G := fieldConstantPrefix hI F P hp
    have hv := fieldConstantPrefix_value hI F P hp t
    have hm : Measurable (fieldScalarValue P (fun z => F.U (t, z))) := by
      rw [← hv]
      exact G.mU.comp (by fun_prop)
    have hg : HasLinearGrowth (fieldScalarValue P (fun z => F.U (t, z))) := by
      rw [← hv]
      exact G.growth t
    have hr := fieldConstantPrefix_test_regular hI F P hp t ha haB
    change fieldSpinTransition av.1 av.2 _
      (fieldScalarMean P (fun z => F.U (t, z)) (fun z => c + k * a z)) = _
    rw [ih hp]
    funext z
    rw [fieldSpinTransition_add av.1 av.2 hm hg measurable_const (hr.1.const_mul k)
      (fun _ => le_rfl) (fun u => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hr.2 u) (abs_nonneg k)),
      fieldSpinTransition_const av.1 av.2 hm hg,
      fieldSpinTransition_const_mul]
    rfl

lemma fieldScalarSquares_congr_list {P Q : List (ℝ × ℝ≥0)} (he : P = Q)
    (F a : ℝ → ℝ) (i : Fin (P.length + 1)) (j : Fin (Q.length + 1))
    (hij : i.val = j.val) : fieldScalarSquares P F a i = fieldScalarSquares Q F a j := by
  subst Q
  have hi : i = j := Fin.ext hij
  rw [hi]

end InvariantIsing

end

end OAI
