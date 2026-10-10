import OAI.Probability.InvariantIsing.Fields.FieldHeightChart

namespace OAI

/-! Identification of the finite covariance charts with literal updates
of a field height. The formula is defined without choosing proofs of the
order constraints; whenever the updated heights are admissible it is the
original `fieldValue` of that field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldHeightIncrement {n : ℕ} (r : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  r j - if hj : j.val = 0 then 0 else r ⟨j.val - 1, by omega⟩

lemma fieldHeightIncrement_eq (h : FieldStep) (j : Fin (h.depth + 1)) :
    fieldHeightIncrement h.height j = (fieldIncrement h j).2 := rfl

lemma fieldHeightIncrement_update {n : ℕ} (r : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (t : ℝ) :
    fieldHeightIncrement (Function.update r i (r i + t)) j =
      fieldHeightIncrement r j + if j = i then t else if j.val = i.val + 1 then -t else 0 := by
  classical
  by_cases hj : j.val = 0
  · have hn : j.val ≠ i.val + 1 := by omega
    simp only [fieldHeightIncrement, hj, dite_true, sub_zero]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  · have hp : (⟨j.val - 1, by omega⟩ : Fin (n + 1)) = i ↔ j.val = i.val + 1 := by
      constructor
      · intro he
        have hv := congrArg Fin.val he
        simp only at hv
        omega
      · intro he
        apply Fin.ext
        simp only
        omega
    simp only [fieldHeightIncrement, hj, dite_false, Function.update_apply, hp]
    by_cases he : j = i
    · subst j
      have hn : i.val ≠ i.val + 1 := by omega
      simp only [ite_true, hn, ite_false]
      ring
    · by_cases hn : j.val = i.val + 1
      · have hpi : (⟨j.val - 1, by omega⟩ : Fin (n + 1)) = i := hp.mpr hn
        rw [hpi]
        simp only [he, hn, ite_false, ite_true]
        ring
      · simp [he, hn]

private lemma list_set_two {α : Type*} (L : List α) (i : ℕ)
    (A B : α) (hi : i + 1 < L.length) :
    (L.set i A).set (i + 1) B = L.take i ++ A :: B :: L.drop (i + 2) := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    cases i with
    | zero =>
      cases L with
      | nil => simp at hi
      | cons y L => rfl
    | succ i =>
      have hh : i + 1 < L.length := by simp only [List.length_cons] at hi; omega
      simpa only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons,
        List.cons_append, Nat.succ_eq_add_one, Nat.add_assoc] using
        congrArg (List.cons x) (ih i hh)

/-- The literal single-coordinate value, using exactly the Gaussian
recursion of `fieldValue` with the updated height vector. -/
def fieldHeightCoordinateValue (h : FieldStep) (i : Fin (h.depth + 1))
    (t z : ℝ) : ℝ :=
  let r := Function.update h.height i (h.height i + t)
  fieldScalarValue (List.ofFn fun j : Fin (h.depth + 1) =>
    (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement r j)))
    (fun y => Real.log (Real.cosh y)) z - r (Fin.last h.depth) / 2

lemma gaussianOperator_toNNReal (ζ v : ℝ) (F : ℝ → ℝ) :
    gaussianOperator ζ (Real.toNNReal v) F = gaussianOperator ζ v F := by
  rw [gaussianOperator_eq_transform ζ v F]
  exact (field_gaussianTransform_eq_operator v ζ F).symm

/-- The original partition with an admissible updated height vector. -/
def fieldWithHeights (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) : FieldStep :=
  { h with height := r, nonneg := hr0, ordered_height := hrmono }

lemma fieldHeightCoordinateValue_eq_fieldValue (h : FieldStep)
    (i : Fin (h.depth + 1)) (t z : ℝ)
    (hr0 : ∀ j, 0 ≤ Function.update h.height i (h.height i + t) j)
    (hrmono : Monotone (Function.update h.height i (h.height i + t))) :
    fieldHeightCoordinateValue h i t z =
      fieldValue (fieldWithHeights h (Function.update h.height i (h.height i + t))
        hr0 hrmono) z := by
  let k := fieldWithHeights h (Function.update h.height i (h.height i + t)) hr0 hrmono
  have hl : (List.ofFn fun j : Fin (h.depth + 1) =>
      (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement k.height j))) =
      fieldAllIncrements k := by
    unfold fieldAllIncrements
    apply congrArg List.ofFn
    funext j
    apply Prod.ext
    · rfl
    · exact Real.toNNReal_of_nonneg (fieldIncrement_nonneg k j)
  change fieldScalarValue (List.ofFn fun j : Fin (h.depth + 1) =>
      (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement k.height j)))
      (fun y => Real.log (Real.cosh y)) z - k.height (Fin.last k.depth) / 2 = _
  rw [hl]
  exact fieldAllIncrements_value k z

lemma updated_increments_interior (h : FieldStep) (i : Fin h.depth) (t : ℝ) :
    (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height i.castSucc (h.height i.castSucc + t)) j))) =
    fieldAdjacentIncrements ((fieldAllIncrements h).take i.val)
      ((fieldAllIncrements h).drop (i.val + 2))
      (fieldIncrement h i.castSucc).2 (fieldIncrement h i.succ).2
      (fieldIncrement h i.castSucc).1 (fieldIncrement h i.succ).1 t := by
  classical
  let L := fieldAllIncrements h
  let A : ℝ × ℝ≥0 := ((fieldIncrement h i.castSucc).1,
    Real.toNNReal ((fieldIncrement h i.castSucc).2 + t))
  let B : ℝ × ℝ≥0 := ((fieldIncrement h i.succ).1,
    Real.toNNReal ((fieldIncrement h i.succ).2 - t))
  have he : (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height i.castSucc (h.height i.castSucc + t)) j))) =
      (L.set i.val A).set (i.val + 1) B := by
    apply List.ext_getElem
    · simp [L]
    · intro j hj hj'
      have hjn : j < h.depth + 1 := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_set, fieldHeightIncrement_update,
        Fin.ext_iff, Fin.val_castSucc, fieldHeightIncrement_eq]
      by_cases he : j = i.val
      · subst j
        simp [A, fieldIncrement]
        constructor <;> rfl
      · by_cases hs : j = i.val + 1
        · subst j
          simp [B, fieldIncrement, sub_eq_add_neg]
          constructor <;> rfl
        · have he' : i.val ≠ j := Ne.symm he
          have hs' : i.val + 1 ≠ j := Ne.symm hs
          simp only [he, hs, he', hs', ite_false, add_zero]
          change (h.cut (⟨j, hjn⟩ : Fin (h.depth + 1)).castSucc,
            Real.toNNReal (fieldHeightIncrement h.height ⟨j, hjn⟩)) = L[j]'(by simpa [L] using hjn)
          rw [show L[j]'(by simpa [L] using hjn) = ((fieldIncrement h ⟨j, hjn⟩).1,
            NNReal.mk (fieldIncrement h ⟨j, hjn⟩).2 (fieldIncrement_nonneg h ⟨j, hjn⟩)) from
              List.getElem_ofFn _]
          apply Prod.ext
          · rfl
          · exact Real.toNNReal_of_nonneg (fieldIncrement_nonneg h ⟨j, hjn⟩)
  rw [he, list_set_two L i.val A B (by simp only [L, fieldAllIncrements_length]; omega)]
  rfl

lemma fieldHeightCoordinateValue_interior (h : FieldStep) (i : Fin h.depth) (t z : ℝ) :
    fieldHeightCoordinateValue h i.castSucc t z = fieldInteriorChart h i t z := by
  dsimp only [fieldHeightCoordinateValue, fieldInteriorChart]
  rw [updated_increments_interior]
  have hn : Fin.last h.depth ≠ i.castSucc := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  rw [Function.update_of_ne hn]

lemma hasDerivAt_fieldHeightCoordinate_interior (h : FieldStep) (i : Fin h.depth)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) :
    HasDerivAt (fun t => fieldHeightCoordinateValue h i.castSucc t 0)
      (-(h.cut i.castSucc.succ - h.cut i.castSucc.castSucc) / 2 *
        fieldMagnetizationLevel h i.castSucc) 0 := by
  have he : (fun t => fieldHeightCoordinateValue h i.castSucc t 0) =
      fun t => fieldInteriorChart h i t 0 := by
    funext t
    exact fieldHeightCoordinateValue_interior h i t 0
  rw [he]
  exact hasDerivAt_fieldInteriorChart_magnetization h i hstrict

lemma updated_increments_final (h : FieldStep) (t : ℝ) :
    (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) j))) =
    fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
      (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 t := by
  classical
  let L := fieldAllIncrements h
  let A : ℝ × ℝ≥0 := ((fieldIncrement h (Fin.last h.depth)).1,
    Real.toNNReal ((fieldIncrement h (Fin.last h.depth)).2 + t))
  have he : (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) j))) =
      L.set h.depth A := by
    apply List.ext_getElem
    · simp [L]
    · intro j hj hj'
      have hjn : j < h.depth + 1 := by simpa using hj
      have hn : j ≠ h.depth + 1 := by omega
      simp only [List.getElem_ofFn, List.getElem_set, fieldHeightIncrement_update,
        Fin.ext_iff, Fin.val_last, hn, ite_false, fieldHeightIncrement_eq]
      by_cases he : j = h.depth
      · subst j
        simp [A, fieldIncrement]
        constructor <;> rfl
      · have he' : h.depth ≠ j := Ne.symm he
        simp only [he, he', ite_false, add_zero]
        change (h.cut (⟨j, hjn⟩ : Fin (h.depth + 1)).castSucc,
          Real.toNNReal (fieldHeightIncrement h.height ⟨j, hjn⟩)) = L[j]'(by simpa [L] using hjn)
        rw [show L[j]'(by simpa [L] using hjn) = ((fieldIncrement h ⟨j, hjn⟩).1,
          NNReal.mk (fieldIncrement h ⟨j, hjn⟩).2 (fieldIncrement_nonneg h ⟨j, hjn⟩)) from
            List.getElem_ofFn _]
        apply Prod.ext
        · rfl
        · exact Real.toNNReal_of_nonneg (fieldIncrement_nonneg h ⟨j, hjn⟩)
  rw [he, List.set_eq_take_append_cons_drop]
  simp only [L, fieldAllIncrements_length, Nat.lt_succ_self, ite_true]
  rw [List.drop_eq_nil_of_le (by simp)]
  rfl

lemma fieldHeightCoordinateValue_final (h : FieldStep) (t z : ℝ) :
    fieldHeightCoordinateValue h (Fin.last h.depth) t z = fieldFinalChart h t z := by
  dsimp only [fieldHeightCoordinateValue, fieldFinalChart]
  rw [updated_increments_final, Function.update_self]

/-- Exact finite-coordinate gradient of the actual field functional,
including the zero root exponent and the final diagonal subtraction. -/
lemma hasDerivAt_fieldHeightCoordinate (h : FieldStep) (i : Fin (h.depth + 1))
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) :
    HasDerivAt (fun t => fieldHeightCoordinateValue h i t 0)
      (-(h.cut i.succ - h.cut i.castSucc) / 2 * fieldMagnetizationLevel h i) 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : (fun t => fieldHeightCoordinateValue h (Fin.last h.depth) t 0) =
        fun t => fieldFinalChart h t 0 := by
      funext t
      exact fieldHeightCoordinateValue_final h t 0
    rw [he]
    simpa only [Fin.succ_last, h.last] using hasDerivAt_fieldFinalChart h hstrict
  · exact hasDerivAt_fieldHeightCoordinate_interior h j hstrict

end InvariantIsing

end

end OAI
