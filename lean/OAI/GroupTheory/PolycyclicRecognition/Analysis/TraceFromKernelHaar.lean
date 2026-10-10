import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightKernelCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightKernelDeterminant
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AdjointDeterminant
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput

namespace OAI

/-! # Zero adjoint trace from unimodularity and nilpotent kernel coordinates

This proves the needed conclusion directly from Haar invariance. No formula
identifying the modular character with an adjoint determinant is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G] [SimplyConnectedSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem trace_ad_eq_zero_of_kernel_haar
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))
    (dixmier : DixmierExponentialInput (E := E) (G := G))
    (realize : ExponentialLinearRealizationInput (EG := E) (G := G))
    (existN : NilpotentLieExistenceInput T.kernelIdeal)
    (haarN : ∀ N : NilpotentLieModel T.kernelIdeal,
      NilpotentExponentialHaarInput N.modelSpace N.carrier)
    (integrate : ∀ N : NilpotentLieModel T.kernelIdeal,
      NilpotentLieIntegrationInput (EN := N.modelSpace) (N := N.carrier) (EG := E) (G := G))
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : LinearMap.trace ℝ _ (ad ℝ _ x) = 0 := by
  obtain ⟨cG, hcG⟩ := (dixmier ⟨a, ⟨T⟩⟩).2 Exp hExp
  obtain ⟨s, hs⟩ := exists_continuous_height_section T q Exp π hπExp cG hcG
  obtain ⟨N, ExpN, hExpN, ι, hι, hιExp, hrange⟩ :=
    exists_closed_height_kernel T q Exp hExp π hπExp cG hcG existN haarN integrate
  let b := finBasis ℝ T.kernelIdeal
  obtain ⟨c, hc, hhaar, hright⟩ :=
    exists_height_kernel_coordinates T Exp hExp π N (haarN N) ExpN hExpN ι hι hιExp hrange b
  have hdet := abs_det_conjugationDifferential_eq_one_of_height_coordinates
    T q Exp hExp π hπ hπExp s hs b c hc hhaar hright μ (Exp x)
  obtain ⟨m, _hm, ρ, j, hind, hρExp⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  have hρ : Function.Injective ρ := by
    intro g k h
    exact hind.injective (congrArg Units.val h)
  rw [det_conjugationDifferential_exp T hExp j ρ hρ hρExp,
    abs_of_pos (Real.exp_pos _)] at hdet
  exact (Real.exp_eq_one_iff _).mp hdet

end PolycyclicRecognition

end

end OAI
