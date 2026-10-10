import OAI.NumberTheory.Ostmann.Construction.HistoryFormulaFourier

namespace OAI

/-! # Products queried at the actual intermediate reconstruction stages -/

namespace Ostmann

open scoped Classical

theorem ValidIntegerReconstruction.take {σ : Type*} {steps : List (HistoryPivotStep σ)}
    {x : σ → ℤ} (h : ValidIntegerReconstruction steps x) (n : ℕ) :
    ValidIntegerReconstruction (steps.take n) x := by
  induction n generalizing steps x with
  | zero => trivial
  | succ n ih =>
    cases steps with
    | nil => trivial
    | cons step rest => exact ⟨h.1, ih h.2⟩

noncomputable def reconstructedWordFormula {σ : Type*} (steps : List (HistoryPivotStep σ))
    (stage : ℕ) (word : List σ) : HistoryFormula σ :=
  .listProduct (word.map (integerReconstructionFormulas (steps.take stage)))

theorem reconstructedWordFormula_value {σ : Type*} (steps : List (HistoryPivotStep σ))
    (stage : ℕ) (word : List σ) (x : σ → ℤ) (hx : ValidIntegerReconstruction steps x) :
    (reconstructedWordFormula steps stage word).value (fun i => (x i : ℚ)) =
      ((word.map (reconstructIntegers (steps.take stage) x)).prod : ℤ) := by
  simp only [reconstructedWordFormula, HistoryFormula.value_listProduct, List.map_map,
    Function.comp_def, integerReconstructionFormulas_value _ _ (hx.take stage)]
  induction word with
  | nil => simp
  | cons i word ih => simp only [List.map_cons, List.prod_cons, Int.cast_mul, ih]

theorem reconstructedWordFormula_cost {σ : Type*} (steps : List (HistoryPivotStep σ))
    (stage : ℕ) (word : List σ) (C : ℕ) (hC : 1 ≤ C)
    (hsize : ∀ step ∈ steps, step.left.length + step.right.length + 4 ≤ C) :
    (reconstructedWordFormula steps stage word).cost ≤ word.length * C ^ steps.length + 1 := by
  have hc (i : σ) : (integerReconstructionFormulas (steps.take stage) i).cost ≤ C ^ steps.length := by
    have h := HistoryFormula.reconstructedFormulas_cost
      ((steps.take stage).map fun step => (step.target, step.formula)) C hC
      (by
        intro a ha
        obtain ⟨step, hstep, rfl⟩ := List.mem_map.mp ha
        simpa only [step.formula_cost] using hsize step (List.mem_of_mem_take hstep)) i
    simp only [List.length_map] at h
    exact h.trans (pow_le_pow_right₀ hC (by
      simp only [List.length_take]
      exact Nat.min_le_right _ _))
  induction word with
  | nil => simp [reconstructedWordFormula, HistoryFormula.listProduct, HistoryFormula.cost]
  | cons i word ih =>
    change (integerReconstructionFormulas (steps.take stage) i).cost +
      (reconstructedWordFormula steps stage word).cost ≤ _
    simp only [List.length_cons]
    nlinarith [hc i]

theorem HistoryFormula.inputsBounded_listProduct {σ : Type*} (fs : List (HistoryFormula σ))
    (R : ℝ) (hR : 1 ≤ R) (h : ∀ F ∈ fs, F.InputsBounded R) :
    (HistoryFormula.listProduct fs).InputsBounded R := by
  induction fs with
  | nil => simpa only [listProduct, InputsBounded, Int.cast_one, abs_one] using hR
  | cons F fs ih => exact ⟨h F (by simp), ih (fun G hG => h G (by simp [hG]))⟩

theorem HistoryPivotStep.formula_inputsBounded {σ : Type*} (step : HistoryPivotStep σ)
    (R : ℝ) (hR : 1 ≤ R) (hv : |(step.v : ℝ)| ≤ R)
    (hw : |(step.w : ℝ)| ≤ R) (hs : |(step.s : ℝ)| ≤ R) : step.formula.InputsBounded R := by
  have hp (l : List σ) : (HistoryFormula.listProduct (l.map .prime)).InputsBounded R := by
    apply HistoryFormula.inputsBounded_listProduct _ R hR
    intro F hF
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
    trivial
  exact ⟨hp _, hp _, hv, hw, hs⟩

theorem reconstructedWordFormula_inputsBounded {σ : Type*} (steps : List (HistoryPivotStep σ))
    (stage : ℕ) (word : List σ) (R : ℝ) (hR : 1 ≤ R)
    (hsize : ∀ step ∈ steps,
      |(step.v : ℝ)| ≤ R ∧ |(step.w : ℝ)| ≤ R ∧ |(step.s : ℝ)| ≤ R) :
    (reconstructedWordFormula steps stage word).InputsBounded R := by
  apply HistoryFormula.inputsBounded_listProduct _ R hR
  intro F hF
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
  apply HistoryFormula.replayFormulas_inputs
  · intro j; trivial
  · intro a ha
    obtain ⟨step, hstep, rfl⟩ := List.mem_map.mp ha
    obtain ⟨hv, hw, hs⟩ := hsize step (List.mem_of_mem_take hstep)
    exact step.formula_inputsBounded R hR hv hw hs

end Ostmann

end OAI
