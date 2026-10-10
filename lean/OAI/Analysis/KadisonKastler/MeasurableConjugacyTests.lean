import OAI.Analysis.KadisonKastler.SequentialConjugacyTests

namespace OAI

/-! # Measurable conjugacy relations from vector evaluations

The two countable strong-test families recognize actual algebra
conjugacy. Their measurability and the countable operator norm tests
give the bounded implementer relation used for measurable selection.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]
  (M N : X → VonNeumannAlgebra H)

theorem measurableSet_conjugates_of_vector_tests
    (A : ∀ p, StrongUnitBallTestSequence (M p)) (B : ∀ p, StrongUnitBallTestSequence (N p))
    (ξ : ℕ → H) (hξ : DenseRange ξ) (U : X → unitary (H →L[ℂ] H))
    (hAB : ∀ j q l, Measurable (fun p =>
      (unitaryConj (U p) ((A p).op j) - (B p).op q) (ξ l)))
    (hBA : ∀ j q l, Measurable (fun p =>
      (unitaryConj (star (U p)) ((B p).op j) - (A p).op q) (ξ l))) :
    MeasurableSet {p | Conjugates (U p) (M p) (N p)} := by
  have hL : MeasurableSet {p | ∀ j,
      CountableStrongTests ξ (Set.range (B p).op) (unitaryConj (U p) ((A p).op j))} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_countableStrongTests_range ξ
      (fun p => unitaryConj (U p) ((A p).op j)) (fun p => (B p).op) (hAB j)
  have hR : MeasurableSet {p | ∀ j,
      CountableStrongTests ξ (Set.range (A p).op) (unitaryConj (star (U p)) ((B p).op j))} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_countableStrongTests_range ξ
      (fun p => unitaryConj (star (U p)) ((B p).op j)) (fun p => (A p).op) (hBA j)
  have heq : {p | Conjugates (U p) (M p) (N p)} =
      {p | ∀ j, CountableStrongTests ξ (Set.range (B p).op) (unitaryConj (U p) ((A p).op j))} ∩
      {p | ∀ j, CountableStrongTests ξ (Set.range (A p).op) (unitaryConj (star (U p)) ((B p).op j))} := by
    ext p
    exact conjugates_iff_countable_strong_tests (A p) (B p) ξ hξ (U p)
  rw [heq]
  exact hL.inter hR

theorem measurableSet_bounded_conjugates_of_vector_tests
    (A : ∀ p, StrongUnitBallTestSequence (M p)) (B : ∀ p, StrongUnitBallTestSequence (N p))
    (ξ : ℕ → H) (hξ : DenseRange ξ) (U : X → unitary (H →L[ℂ] H))
    (hAB : ∀ j q l, Measurable (fun p =>
      (unitaryConj (U p) ((A p).op j) - (B p).op q) (ξ l)))
    (hBA : ∀ j q l, Measurable (fun p =>
      (unitaryConj (star (U p)) ((B p).op j) - (A p).op q) (ξ l)))
    (hU : ∀ l, Measurable (fun p => ((U p : H →L[ℂ] H) - 1) (ξ l)))
    {a : ℝ} (ha : 0 ≤ a) :
    MeasurableSet {p | Conjugates (U p) (M p) (N p) ∧ ‖(U p : H →L[ℂ] H) - 1‖ ≤ a} :=
  (measurableSet_conjugates_of_vector_tests M N A B ξ hξ U hAB hBA).inter
    (measurableSet_operator_norm_le ξ hξ (fun p => (U p : H →L[ℂ] H) - 1) ha hU)

end

end KadisonKastler

end OAI
