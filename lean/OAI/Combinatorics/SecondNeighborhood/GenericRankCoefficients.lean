import OAI.Combinatorics.SecondNeighborhood.GenericRankFamily
import OAI.Combinatorics.SecondNeighborhood.KernelConflict

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {X τ : Type*} [Fintype X] [DecidableEq X] [Fintype τ]

abbrev CoefficientVariables (X : Type*) := Sum (X × X) (X × X)

noncomputable def selectedA (r : X → X → Prop)
    (v : CoefficientVariables X → ℝ) (x y : X) : ℝ := by
  classical
  exact if r x y then v (Sum.inl (x, y)) else 0

noncomputable def selectedB (r : X → X → Prop)
    (v : CoefficientVariables X → ℝ) (x y : X) : ℝ := by
  classical
  exact if r x y then v (Sum.inr (x, y)) else 0

omit [Fintype X] [DecidableEq X] in
theorem selectedA_supported (r : X → X → Prop) (v : CoefficientVariables X → ℝ) :
    SupportedCoefficients r (selectedA r v) := by
  classical
  intro x y h
  simp [selectedA, h]

omit [Fintype X] [DecidableEq X] in
theorem selectedB_supported (r : X → X → Prop) (v : CoefficientVariables X → ℝ) :
    SupportedCoefficients r (selectedB r v) := by
  classical
  intro x y h
  simp [selectedB, h]

omit [Fintype X] [DecidableEq X] in
theorem matrixD_eq_eval_supported (r : X → X → Prop) (R C : Finset (X × X))
    (v : CoefficientVariables X → ℝ) (p i : X) :
    matrixD R C (selectedB r v) p i = evalPolynomialMatrix v
      (supportedVariableMatrix (R := ℝ)
        (fun s : PairFiber C i => fun j : PairFiber R p => r s.1 j.1)
        (fun s j => Sum.inr (s.1, j.1))) := by
  classical
  ext s j
  by_cases h : r s.1 j.1 <;>
    simp [matrixD, selectedB, evalPolynomialMatrix, supportedVariableMatrix, h]

theorem exists_coefficients_localMaximalRanks
    (r : X → X → Prop) (R C : Finset (X × X))
    (extra : τ → MvPolynomial (CoefficientVariables X) ℝ)
    (hextra : ∀ t, extra t ≠ 0) :
    ∃ v : CoefficientVariables X → ℝ,
      (∀ t, MvPolynomial.eval v (extra t) ≠ 0) ∧
      SupportedCoefficients r (selectedA r v) ∧
      SupportedCoefficients r (selectedB r v) ∧
      LocalMaximalRanks r R C (selectedB r v) := by
  classical
  let support (q : X × X) (s : PairFiber C q.2) (j : PairFiber R q.1) := r s.1 j.1
  let label (q : X × X) (s : PairFiber C q.2) (j : PairFiber R q.1) :
      CoefficientVariables X := Sum.inr (s.1, j.1)
  have hlabel : ∀ q s j s' j', support q s j → support q s' j' →
      label q s j = label q s' j' → s = s' ∧ j = j' := by
    intro q s j s' j' _ _ h
    have hp : (s.1, j.1) = (s'.1, j'.1) := Sum.inr.inj h
    exact ⟨Subtype.ext (congrArg Prod.fst hp), Subtype.ext (congrArg Prod.snd hp)⟩
  obtain ⟨v, hv, hmax⟩ :=
    exists_eval_maximal_support_rank support label hlabel extra hextra
  refine ⟨v, hv, selectedA_supported r v, selectedB_supported r v, ?_⟩
  intro p i _ D hD
  rw [matrixD_eq_eval_supported]
  apply hmax (p, i) D
  intro s j h
  exact hD s j h

end SeymourSecondNeighborhood.Pruning

end OAI
