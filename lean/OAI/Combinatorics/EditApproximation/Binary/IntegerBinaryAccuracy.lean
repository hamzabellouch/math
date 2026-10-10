import OAI.Combinatorics.EditApproximation.Binary.IntegerBinaryOutput

namespace OAI

namespace EditApproximation
open MeasureTheory

/-- The uniform implementation uses exact dynamic programming below the
proved cutoff and the evaluated binary memo above it. -/
noncomputable def integerBinaryAnswer (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) : ℕ :=
  if physicalLargeInput N epsilon then
    match outcome with
    | .inl _ => exactSuffixAnswer (source.map integerSymbolCode) (target.map integerSymbolCode)
    | .inr execution => bitWordValue (integerBinaryOutput source target N
        (computedExecutionAccepted _ _ N execution)).1
  else exactSuffixAnswer (source.map integerSymbolCode) (target.map integerSymbolCode)

theorem integerBinaryAnswer_large (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (hlarge : physicalLargeInput N epsilon) (hsize : source.length + target.length ≤ N)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerBinaryAnswer source target N epsilon outcome =
      computedFullAnswer (source.map integerSymbolCode) (target.map integerSymbolCode) N outcome := by
  cases outcome with
  | inl unitValue => simp only [integerBinaryAnswer, hlarge, ite_true]; rfl
  | inr execution =>
    simp only [integerBinaryAnswer, hlarge, ite_true]
    exact integerBinaryOutput_execution source target N epsilon hlarge hsize execution

theorem integerBinaryAnswer_equal (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (heq : source = target)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerBinaryAnswer source target N epsilon outcome = 0 := by
  have hm : source.map integerSymbolCode = target.map integerSymbolCode := congrArg _ heq
  unfold integerBinaryAnswer
  split_ifs
  · cases outcome with
    | inl unitValue => exact exactSuffixAnswer_equal _ _ hm
    | inr execution =>
      simp only [integerBinaryOutput, computedQueryAnswerWithWork, hm, ite_true]
      rfl
  · exact exactSuffixAnswer_equal _ _ hm

/-- Accuracy of the concrete binary answer under the finite Bernstein
hypothesis for the reference algorithm. -/
theorem integerBinaryAnswer_conditional_accuracy (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value)
    (hsize : source.length + target.length ≤ N) (bernstein : ComputedBernsteinInputs N) :
    (2 / 3 : ℝ) ≤ (computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon).real
      {outcome | EditDistortion.edit source target ≤ integerBinaryAnswer source target N epsilon outcome ∧
        (integerBinaryAnswer source target N epsilon outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} := by
  by_cases hlarge : physicalLargeInput N epsilon
  · have heq : integerBinaryAnswer source target N epsilon =
        computedFullAnswer (source.map integerSymbolCode) (target.map integerSymbolCode) N :=
      funext (integerBinaryAnswer_large source target N epsilon hlarge hsize)
    rw [heq]
    have h := computed_full_conditional_accuracy (source.map integerSymbolCode) (target.map integerSymbolCode)
      N epsilon hepsilon (by simpa only [List.length_map] using hsize) bernstein.1 bernstein.2
    simpa only [integerSymbols_edit] using h
  · have heq (outcome) : integerBinaryAnswer source target N epsilon outcome = EditDistortion.edit source target := by
      simp only [integerBinaryAnswer, hlarge, ite_false, exactSuffixAnswer_eq_edit, integerSymbols_edit]
    have hupper : (EditDistortion.edit source target : ℝ) ≤
        (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target := by
      have hp : (0 : ℝ) < epsilon.value := by exact_mod_cast hepsilon
      nlinarith only [hp, Nat.cast_nonneg (α := ℝ) (EditDistortion.edit source target)]
    have hevent : {outcome | EditDistortion.edit source target ≤ integerBinaryAnswer source target N epsilon outcome ∧
        (integerBinaryAnswer source target N epsilon outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} = Set.univ := by
      ext outcome
      simp only [Set.mem_ofPred_eq, heq, le_refl, true_and, Set.mem_univ, iff_true]
      exact hupper
    rw [hevent, probReal_univ]
    norm_num

end EditApproximation

end OAI
