import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete

namespace OAI

/-! Amenability, unitarizability, and bounded nonunitarizable representations.
Representations into the endomorphism monoid have bounded inverses because
their domain is a group. Norm-preserving invertible complex linear maps on
Hilbert spaces are unitary. No bound on similarities is imposed. -/
noncomputable section
universe u v
namespace Dixmier
open scoped BoundedContinuousFunction

def leftTranslate {G : Type u} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (g : G) (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  f.compContinuous ⟨fun x => g⁻¹ * x, continuous_of_discreteTopology⟩

/-- A positive normalized left-invariant complex mean. -/
def Amenable (G : Type u) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] : Prop :=
  ∃ m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ,
    m (BoundedContinuousFunction.const G 1) = 1 ∧
    (∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) ∧
    ∀ (g : G) (f : G →ᵇ ℂ), m (leftTranslate g f) = m f

def SimilarToUnitary {G : Type u} [Group G]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)) : Prop :=
  ∃ S : H ≃L[ℂ] H, ∀ (g : G) (x : H), ‖S (π g (S.symm x))‖ = ‖x‖

/-- A uniformly 101-bounded nonunitarizable representation on a separable
complete complex Hilbert space, with its universe explicit. -/
def NonamenableWitness (G : Type u) [Group G] : Prop :=
  ∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
    (π : G →* (H →L[ℂ] H)),
    (∀ g : G, ‖π g‖ ≤ 101) ∧ ¬ SimilarToUnitary π

/-- Unitarizability at an explicitly quantified Hilbert-space universe. -/
def Unitarizable (G : Type u) [Group G] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
    (∃ C : ℝ, ∀ g, ‖π g‖ ≤ C) → SimilarToUnitary π

/-- Every countable discrete nonamenable group has a bounded nonunitarizable witness. -/
def MainTheorem : Prop :=
  ∀ (G : Type u) [Group G] [Countable G] [TopologicalSpace G]
    [DiscreteTopology G], ¬ Amenable G → NonamenableWitness.{u, v} G

/-- A nonunitarizable witness contradicts unitarizability. -/
theorem witness_not_unitarizable {G : Type u} [Group G]
    (h : NonamenableWitness.{u, v} G) : ¬ Unitarizable.{u, v} G := by
  rcases h with ⟨H, hnorm, hinner, hcomplete, hsep, π, hbound, hnot⟩
  intro hunit
  exact hnot (hunit H π ⟨101, hbound⟩)

end Dixmier

end

end OAI
