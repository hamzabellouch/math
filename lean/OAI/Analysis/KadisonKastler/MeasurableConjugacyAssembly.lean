import OAI.Analysis.KadisonKastler.DirectIntegralConjugacy

namespace OAI

/-! # From fiber implementers to a bounded global conjugacy

This completes selection and assembly for a constant-fiber stratum of a
given central decomposition. The decomposition data and the factor
implementers are the explicit premises; neither is silently assumed to
exist for an arbitrary pair of algebras.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u v

variable {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

theorem exists_bounded_conjugacy_of_fiber_implementers
    (hpub : PublishedUnitaryBorelSelection.{u, v}) (μ : Measure X) [IsFiniteMeasure μ]
    (M N : X → VonNeumannAlgebra H)
    (A B : VonNeumannAlgebra (Lp H 2 μ))
    (hMA : OperatorFieldDecomposition μ M A) (hNB : OperatorFieldDecomposition μ N B)
    (sM : ∀ p, StrongUnitBallTestSequence (M p))
    (sN : ∀ p, StrongUnitBallTestSequence (N p))
    (hmM : ∀ j x, Measurable (fun p => (sM p).op j x))
    (hmN : ∀ j x, Measurable (fun p => (sN p).op j x))
    {a : ℝ} (ha : 0 ≤ a)
    (hex : ∀ᵐ p ∂μ, ∃ u : unitary (H →L[ℂ] H),
      Conjugates u (M p) (N p) ∧ ‖(u : H →L[ℂ] H) - 1‖ ≤ a) :
    ∃ u : unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ),
      Conjugates u A B ∧ ‖(u : Lp H 2 μ →L[ℂ] Lp H 2 μ) - 1‖ ≤ a := by
  obtain ⟨U, hU, hUs, hrel⟩ := exists_measurable_implementer_field hpub μ M N sM sN hmM hmN ha hex
  refine ⟨regularUnitaryField μ U hU hUs, ?_, ?_⟩
  · exact conjugates_regularUnitaryField μ hMA hNB U hU hUs (hrel.mono fun _ h => h.1)
  · exact norm_regularUnitaryField_sub_one_le μ U hU hUs ha (hrel.mono fun _ h => h.2)

end

end KadisonKastler

end OAI
