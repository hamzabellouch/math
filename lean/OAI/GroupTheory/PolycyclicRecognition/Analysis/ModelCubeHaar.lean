import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput

namespace OAI

/-! # Haar normalization in a Lie-algebra model basis -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

/-- Normalize the published nilpotent exponential Haar measure in a basis
of an isomorphic Lie algebra, as used for the actual Cartan factor. -/
theorem exists_model_haar_cube_volume
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent L) {n : ℕ} (b : Basis (Fin n) ℝ L) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ R : ℝ, 0 ≤ R →
      μ (exponentialCoordinateBox (Exp ∘ e) b R) = ENNReal.ofReal (2 * R) ^ n := by
  obtain ⟨_, μ, _, hμ, hvol⟩ := exists_haar_exponential_cube_volume haar Exp hExp
    (e.nilpotent_iff_equiv_nilpotent.mp hnil) (b.map e.toLinearEquiv)
  refine ⟨μ, hμ, ?_⟩
  intro R hR
  have he : exponentialCoordinateBox (Exp ∘ e) b R =
      exponentialCoordinateBox Exp (b.map e.toLinearEquiv) R := by
    rw [exponentialCoordinateBox_eq_cube_image _ _ R hR,
      exponentialCoordinateBox_eq_cube_image _ _ R hR]
    congr 1
  rw [he]
  exact hvol R hR

end PolycyclicRecognition

end

end OAI
