import OAI.GroupTheory.PolycyclicRecognition.Geometry.MinimizingLieMetric
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularRealizationInput
import Mathlib.Geometry.Manifold.ContMDiff.Defs

namespace OAI

/-! # The published regularity inputs needed for Lipschitz replacement

These retain regularity that the earlier topological/metric inputs deliberately
discarded. Dixmier, *Bull. Soc. Math. France* 85 (1957), Theorem 3, p.120,
gives a global exponential diffeomorphism for a simply connected solvable group
with real adjoint roots. Lee, *Introduction to Riemannian Manifolds*, second
edition (2018), Lemma 3.10(b), Problem 6-12(c) and Corollary 6.21 give the
complete left-invariant metric and minimizing paths. Lemmas 2.53–2.54,
especially the length comparison (2.22), give local Lipschitz compatibility
of smooth coordinates and their inverses with that Riemannian distance.

Only smooth (`∞`) regularity is retained; analyticity is not needed by the
application. The second input is precisely this coordinate consequence of the published
length comparison, for the chosen tangent-space coordinates. It assumes no
contraction, interpolation, quasi-isometry or height conclusion.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
open Module

def DixmierExponentialDiffeomorphismInput
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G] : Prop :=
  ∀ (a : ℕ) (_T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    let V := Fin (finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) → ℝ
    let b := finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
    ∃ φ : V ≃ₜ G,
      (∀ x, φ x = Exp (b.equivFun.symm x)) ∧
      ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ φ ∧
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ φ.symm

/-- Only the tangent-space global coordinates used by the application are
retained from the general Riemannian local length comparison. -/
def LieRiemannianMetricInput : Prop :=
  ∀ S : SimplyConnectedSolvableLieModel,
    ∃ d : ProperMinimizingMetric S.carrier,
      letI := d.toProperChainMetric.compatibleMetric
      ∀ (n : ℕ) (φ : (Fin n → ℝ) ≃ₜ S.carrier),
        ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, S.modelSpace)) ∞ φ →
        ContMDiff (𝓘(ℝ, S.modelSpace)) (𝓘(ℝ, Fin n → ℝ)) ∞ φ.symm →
        LocallyLipschitz φ ∧ LocallyLipschitz φ.symm

end PolycyclicRecognition

end

end OAI
