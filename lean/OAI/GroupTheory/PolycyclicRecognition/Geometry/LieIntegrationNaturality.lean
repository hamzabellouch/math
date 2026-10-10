import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialNaturality
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieIntegrationInput

namespace OAI

/-! # Removing exponential compatibility from the integration input

Only existence of a smooth homomorphism with the prescribed differential
remains from Lee's integration theorem. The exponential maps and their
compatibility are supplied by the proved integral-curve construction.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EN N EG G : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace G] [ChartedSpace EG G] [Group G] [LieGroup (𝓘(ℝ, EG)) ⊤ G]

/-- The still-undischarged existence assertion of Lee (2013), Theorem 20.19,
in precisely the nilpotent-source specialization used in the application. -/
def NilpotentSmoothIntegrationInput : Prop :=
  SimplyConnectedSpace N → LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, EN)) N) →
    ∀ j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EG)) G,
      ∃ ι : N →* G, ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι ∧
        ∀ x, mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 x = j x

theorem nilpotentLieIntegrationInput_of_smooth [T2Space G]
    (h : NilpotentSmoothIntegrationInput (EN := EN) (N := N) (EG := EG) (G := G)) :
    NilpotentLieIntegrationInput (EN := EN) (N := N) (EG := EG) (G := G) := by
  intro hN hnil j ExpN ExpG hExpN hExpG
  obtain ⟨ι, hsmooth, hderiv⟩ := h hN hnil j
  refine ⟨ι, hsmooth, hderiv, fun x => ?_⟩
  have heq := hExpN.map_of_mdifferentiable hExpG ι (hsmooth.mdifferentiable (by simp)) x
  rw [hderiv] at heq
  exact heq

/-- Smooth integration is equivalent to integration compatible with the
intrinsic exponential maps. -/
theorem nilpotentLieIntegrationInput_iff_smooth [T2Space N] [T2Space G] :
    NilpotentLieIntegrationInput (EN := EN) (N := N) (EG := EG) (G := G) ↔
      NilpotentSmoothIntegrationInput (EN := EN) (N := N) (EG := EG) (G := G) := by
  constructor
  · intro h hN hnil j
    obtain ⟨ι, hsmooth, hderiv, _⟩ := h hN hnil j groupExponential groupExponential
      groupExponential_isGroupExponential groupExponential_isGroupExponential
    exact ⟨ι, hsmooth, hderiv⟩
  · exact nilpotentLieIntegrationInput_of_smooth

end PolycyclicRecognition

end

end OAI
