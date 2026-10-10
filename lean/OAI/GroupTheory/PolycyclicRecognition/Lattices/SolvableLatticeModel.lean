import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeQuotient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Polycyclic
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.GroupTheory.Solvable

namespace OAI

/-!
# Solvable-lattice realization

K. Dekimpe, *Solvable Lie Algebras, Lie Groups and Polynomial Structures*,
Compositio Mathematica 121 (2000), 183–204, Theorem 4.1, p.199,
DOI 10.1023/A:1001738932743, gives a finite-index subgroup of a
polycyclic-by-finite group as a uniform lattice in a connected simply
connected solvable Lie group. We use only this consequence, omitting the
additional equality with the Fitting subgroup and omitting normality.

The realization predicate specifies a finite-dimensional smooth Lie structure
and a discrete lattice with compact coset quotient.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

/-- A connected simply connected finite-dimensional real solvable Lie group.
No metric or lattice is part of this record. -/
structure SimplyConnectedSolvableLieModel where
  modelSpace : Type
  [normedAddCommGroup : NormedAddCommGroup modelSpace]
  [normedSpace : NormedSpace ℝ modelSpace]
  [finiteDimensional : FiniteDimensional ℝ modelSpace]
  carrier : Type
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace modelSpace carrier]
  [group : Group carrier]
  [lieGroup : LieGroup (𝓘(ℝ, modelSpace)) ⊤ carrier]
  [t2Space : T2Space carrier]
  [secondCountableTopology : SecondCountableTopology carrier]
  [simplyConnectedSpace : SimplyConnectedSpace carrier]
  [solvable : Group.IsSolvable carrier]

attribute [instance] SimplyConnectedSolvableLieModel.normedAddCommGroup
  SimplyConnectedSolvableLieModel.normedSpace SimplyConnectedSolvableLieModel.finiteDimensional
  SimplyConnectedSolvableLieModel.topologicalSpace SimplyConnectedSolvableLieModel.chartedSpace
  SimplyConnectedSolvableLieModel.group SimplyConnectedSolvableLieModel.lieGroup
  SimplyConnectedSolvableLieModel.t2Space SimplyConnectedSolvableLieModel.simplyConnectedSpace
  SimplyConnectedSolvableLieModel.secondCountableTopology
  SimplyConnectedSolvableLieModel.solvable

/-- The exact lattice-realization consequence of Dekimpe's Theorem 4.1
needed for the paper's lattice formulation. -/
def DekimpeLatticeRealizationInput : Prop :=
  ∀ (P : Type) [Group P], IsVirtuallyPolycyclic P →
    ∃ Γ : Subgroup P, Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        DiscreteTopology Λ ∧ CompactSpace (S.carrier ⧸ Λ) ∧ Nonempty (Γ ≃* Λ)

/-- Restate the published realization using the equivalent compact-cover
definition used by the metric lattice lemmas. -/
theorem exists_uniform_solvable_lattice_of_virtuallyPolycyclic
    (dekimpe : DekimpeLatticeRealizationInput)
    (P : Type) [Group P] (hP : IsVirtuallyPolycyclic P) :
    ∃ Γ : Subgroup P, Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨Γ, hΓ, S, Λ, hdisc, hcompact, e⟩ := dekimpe P hP
  let := hdisc
  let := hcompact
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, S.modelSpace))
  exact ⟨Γ, hΓ, S, Λ, isUniformLattice_of_compact_quotient Λ, e⟩

end PolycyclicRecognition

end

end OAI
