import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularAdjointSolvable
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularRepresentationKernel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntrinsicIdealNormality

namespace OAI

/-! # Faithful triangular group representations from the retained exponential input

All representation and nilpotent integration data are constructed. The
only remaining premise here is Dixmier's global exponential chart.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G] [LocallyCompactSpace G]

theorem exists_faithful_triangular_group_representation
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (dixmier : DixmierExponentialInput (E := E) (G := G))
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
    ∃ m : ℕ, 0 < m ∧
      ∃ j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
      ∃ ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ,
        Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
        (∀ x ∈ T.kernelIdeal, IsNilpotent (j x)) ∧
        Continuous ρ ∧ Function.Injective ρ ∧
        ∀ x, ρ (Exp x) = algebraExpUnit (j x) := by
  let := T.lieAlgebra_isSolvable
  obtain ⟨m, hm, j, hj, hu, hn⟩ := exists_positive_faithful_triangular_representation T
  obtain ⟨H, hH, hnil, _, hspan, _⟩ := exists_cartan_model T
  let := hH
  obtain ⟨chart, hchart⟩ := (dixmier ⟨a, ⟨T⟩⟩).2 Exp hExp
  have hinj : Function.Injective Exp := by
    intro x y h
    apply chart.injective
    simpa only [hchart] using h
  have hsurj : Function.Surjective Exp := by
    intro g
    obtain ⟨x, hx⟩ := chart.surjective g
    exact ⟨x, (hchart x).symm.trans hx⟩
  obtain ⟨F⟩ := nonempty_cartanFactorModel_of_published_inputs (H := H) T hExp dixmier
    (nilpotentPublishedInputs.existsModel _) (nilpotentPublishedInputs.existsModel _)
    (nilpotentPublishedInputs.haar _) (nilpotentPublishedInputs.haar _)
    (fun N => nilpotentLieIntegrationInput_of_smooth
      (nilpotentSmoothIntegrationInput (E := E) (G := G) _ N))
    (fun D => nilpotentLieIntegrationInput_of_smooth
      (nilpotentSmoothIntegrationInput (E := E) (G := G) _ D))
    (fun N => nilpotentIdealNormalityInput_of_intrinsic_exponential
      (nilpotentPublishedInputs.haar _ N) Exp hExp hsurj)
  have hsN : Function.Surjective F.ExpN := by
    obtain ⟨c, hc⟩ := ((nilpotentPublishedInputs.haar _ F.N).2 F.ExpN F.isExpN
      (F.N.tangent_nilpotent hnil)).1
    intro g
    obtain ⟨x, hx⟩ := c.surjective g
    exact ⟨x, (hc x).symm.trans hx⟩
  have hsD : Function.Surjective F.ExpD := by
    obtain ⟨c, hc⟩ := ((nilpotentPublishedInputs.haar _ F.D).2 F.ExpD F.isExpD
      (F.D.tangent_nilpotent inferInstance)).1
    intro g
    obtain ⟨x, hx⟩ := c.surjective g
    exact ⟨x, (hc x).symm.trans hx⟩
  obtain ⟨ρ, hρ, he⟩ := F.exists_integrated_representation hExp hinj hnil hspan hsN hsD j
  exact ⟨m, hm, j, ρ, hj, hu, hn, hρ,
    triangular_representation_injective j hj hu Exp hExp.map_zero hsurj ρ he, he⟩

end PolycyclicRecognition

end

end OAI
