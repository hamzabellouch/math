import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConditionalGroupRecognition

namespace OAI

/-! # The finite-covolume lattice formulation

Mostow's uniformity theorem is used only for a lattice in the original
connected solvable Lie group: Mostow (1962), Theorem 6.2, as stated in
Geng, *When are radicals of Lie groups lattice-hereditary?*, NYJM 21
(2015), Theorem 2.9(i), p.325. No recognition conclusion is part of this input.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

/-- A discrete subgroup with finite covolume, expressed by the normalized
invariant measure on the coset space. -/
def IsFiniteCovolumeLattice {G : Type} [Group G] [TopologicalSpace G]
    (Λ : Subgroup G) : Prop :=
  letI : MeasurableSpace (G ⧸ Λ) := borel _
  DiscreteTopology Λ ∧ ∃ μ : Measure (G ⧸ Λ),
    IsProbabilityMeasure μ ∧ SMulInvariantMeasure G (G ⧸ Λ) μ

/-- The connected-solvable specialization of Mostow's uniformity theorem. -/
def MostowSolvableLatticeUniformInput : Prop :=
  ∀ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
    IsFiniteCovolumeLattice Λ → IsUniformLattice Λ

/-- Corollary `lattice-recognition`, including finite-covolume lattices in
the hypothesis and allowing the ambient Lie group to change. -/
theorem lattice_recognition_of_published_inputs
    (inputs : PublishedRecognitionInputs) (mostow : MostowSolvableLatticeUniformInput)
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsFiniteCovolumeLattice Λ)
    {J : Type} [Group J] [Group.FG J] (e : GroupCoarseEquivalence Λ J) :
    ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
      ∃ (R : SimplyConnectedSolvableLieModel) (Δ : Subgroup R.carrier),
        IsUniformLattice Δ ∧ Nonempty (Γ ≃* Δ) :=
  uniform_lattice_recognition_of_published_inputs inputs S Λ (mostow S Λ hΛ) e

end PolycyclicRecognition

end

end OAI
