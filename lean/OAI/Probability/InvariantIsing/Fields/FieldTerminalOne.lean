import OAI.Probability.InvariantIsing.Fields.FieldGaussianTerminal

namespace OAI

/-! Appending an exponent-one terminal increment changes the scalar
value by its Gaussian constant and preserves every earlier spin moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

private lemma squares_cons_succ (av : ℝ × ℝ≥0) (L : List (ℝ × ℝ≥0))
    (F a : ℝ → ℝ) (i : Fin (L.length + 1)) :
    fieldScalarSquares (av :: L) F a i.succ =
      fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarSquares L F a i) := rfl

lemma fieldScalarValue_const_add (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (c : ℝ) :
    fieldScalarValue L (fun z => c + F z) = fun z => c + fieldScalarValue L F z := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    change gaussianOperator av.1 av.2 (fieldScalarValue L (fun z => c + F z)) = _
    rw [ih ht]
    funext z
    exact gaussianOperator_const_add hv.1 hv.2 c av.1 av.2 z

lemma fieldScalarMean_const_add (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (c : ℝ) :
    fieldScalarMean L (fun z => c + F z) a = fieldScalarMean L F a := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    change fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun z => c + F z))
      (fieldScalarMean L (fun z => c + F z) a) = _
    rw [fieldScalarValue_const_add L ht hF hG c, ih ht]
    funext z
    exact fieldSpinTransition_const_add av.1 av.2 (fieldScalarValue L F) _ c z

lemma fieldScalarValue_terminal_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v : ℝ≥0) :
    fieldScalarValue (L ++ [(1, v)]) (fun z => Real.log (Real.cosh z)) =
      fun z => v / 2 + fieldScalarValue L (fun z => Real.log (Real.cosh z)) z := by
  have he : fieldScalarValue (L ++ [(1, v)]) (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue L (fun z => v / 2 + Real.log (Real.cosh z)) := by
    simp only [fieldScalarValue, List.foldr_append, List.foldr_cons, List.foldr_nil]
    congr 1
    funext z
    exact gaussianOperator_one_logCosh v z
  rw [he]
  exact fieldScalarValue_const_add L hL measurable_logCosh logCosh_linearGrowth _

lemma fieldScalarMean_terminal_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v : ℝ≥0) :
    fieldScalarMean (L ++ [(1, v)]) (fun z => Real.log (Real.cosh z)) Real.tanh =
      fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh := by
  induction L with
  | nil =>
    funext z
    exact fieldSpinTransition_one_tanh v z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    simp only [List.cons_append, fieldScalarMean]
    rw [fieldScalarValue_terminal_one L ht v, ih ht]
    funext z
    exact fieldSpinTransition_const_add av.1 av.2 _ _ (v / 2) z

lemma fieldScalarSquares_terminal_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v : ℝ≥0) (i : ℕ) (hi : i ≤ L.length) :
    fieldScalarSquares (L ++ [(1, v)]) (fun z => Real.log (Real.cosh z)) Real.tanh
      ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩ =
    fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh
      ⟨i, by omega⟩ := by
  induction L generalizing i with
  | nil =>
    have hi0 : i = 0 := by simpa using hi
    subst i
    funext z
    change (fieldSpinTransition 1 v (fun z => Real.log (Real.cosh z)) Real.tanh z) ^ 2 =
      (Real.tanh z) ^ 2
    rw [fieldSpinTransition_one_tanh]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    cases i with
    | zero =>
      funext z
      change (fieldScalarMean ((av :: L) ++ [(1, v)]) (fun z => Real.log (Real.cosh z))
        Real.tanh z) ^ 2 = (fieldScalarMean (av :: L) (fun z => Real.log (Real.cosh z))
        Real.tanh z) ^ 2
      rw [fieldScalarMean_terminal_one (av :: L) hL v]
    | succ i =>
      have hiL : i ≤ L.length := Nat.le_of_succ_le_succ hi
      simp only [List.cons_append]
      have hleft : (⟨i + 1, by simp only [List.length_cons, List.length_append]; omega⟩ :
          Fin ((av :: (L ++ [(1, v)])).length + 1)) =
          (⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩ :
            Fin ((L ++ [(1, v)]).length + 1)).succ := rfl
      have hright : (⟨i + 1, by simp only [List.length_cons]; omega⟩ : Fin ((av :: L).length + 1)) =
          (⟨i, by omega⟩ : Fin (L.length + 1)).succ := rfl
      rw [hleft, hright, squares_cons_succ, squares_cons_succ]
      rw [fieldScalarValue_terminal_one L ht v, ih ht i hiL]
      funext z
      exact fieldSpinTransition_const_add av.1 av.2 _ _ (v / 2) z

end InvariantIsing

end

end OAI
