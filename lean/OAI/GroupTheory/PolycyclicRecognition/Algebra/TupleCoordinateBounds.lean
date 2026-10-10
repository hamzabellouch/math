import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialTupleCoordinates

namespace OAI

/-! # Bounds in the actual inverse exponential charts -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Metric
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace G] [BorelSpace G] in
theorem exponentialBasisHomeomorph_symm_exp {n : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b : Basis (Fin n) ℝ L) (v : L) :
    (exponentialBasisHomeomorph lie chart b).symm (Exp (lie v)) = b.equivFun v := by
  apply (exponentialBasisHomeomorph lie chart b).injective
  rw [Homeomorph.apply_symm_apply, exponentialBasisHomeomorph_apply lie Exp chart hchart,
    LinearEquiv.symm_apply_apply]

omit [MeasurableSpace G] [BorelSpace G] in
theorem exponentialTupleCoordinates_image_subset_ball {n h : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b : Fin h → Basis (Fin n) ℝ L) {R : ℝ} (hR : 0 ≤ R)
    (S : Set (Fin h → G))
    (hS : ∀ u ∈ S, ∀ i, u i ∈ exponentialCoordinateBox (Exp ∘ lie) (b i) R) :
    exponentialTupleCoordinates lie chart b '' S ⊆ closedBall 0 R := by
  rintro z ⟨u, hu, rfl⟩
  apply mem_closedBall_zero_iff.mpr
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  obtain ⟨v, hv, hb⟩ := hS u hu i
  change ‖(exponentialBasisHomeomorph lie chart (b i)).symm (u i)‖ ≤ R
  rw [← hv]
  simpa only [Function.comp_apply, exponentialBasisHomeomorph_symm_exp lie Exp chart hchart] using hb

end PolycyclicRecognition

end

end OAI
