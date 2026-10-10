import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledTupleVolume
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TupleCoordinateBounds
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearHaarCoordinates

namespace OAI

/-! # A correlated tuple set in a growing flat coordinate cube -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter Metric
open scoped Manifold Topology

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

def flatExponentialTupleCoordinates {h m n : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (b : Fin h → Basis (Fin n) ℝ L)
    (flat : (Fin m → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ)) :
    (Fin h → G) ≃ₜ (Fin m → ℝ) :=
  (exponentialTupleCoordinates lie chart b).trans flat.symm.toHomeomorph

theorem normalized_tuple_domain {h m : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : Fin h → WordBasisSelections X words) (cost : Fin h → words → ℝ)
    (flat : (Fin m → ℝ) ≃L[ℝ] (Fin h → Fin (finrank ℝ L) → ℝ))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (R : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (S : ℕ → Set (Fin h → G)) (hS : ∀ r, IsCompact (S r))
    (hbox : ∀ r u, u ∈ S r → ∀ i, u i ∈ exponentialCoordinateBox (Exp ∘ lie)
      (rescaledTupleBases X words β cost (scale r) i) (R r))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun r =>
      ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume))
        (S r)).toReal / Real.exp (scale r * ∑ i, columnBasisWeight (cost i) (β i).val))) :
    let f := fun r => flatExponentialTupleCoordinates lie chart
      (rescaledTupleBases X words β cost (scale r)) flat
    (∀ r, IsCompact (f r '' S r)) ∧
    (∀ r, f r '' S r ⊆ closedBall 0 (‖flat.symm.toContinuousLinearMap‖ * R r)) ∧
    HasSubexponentialUpperBoundSeq scale (fun r => ‖flat.symm.toContinuousLinearMap‖ * R r) ∧
    HasSubexponentialLowerBoundSeq scale (fun r => (volume (f r '' S r)).toReal) := by
  dsimp only
  refine ⟨fun r => (hS r).image (Homeomorph.continuous _), ?_, ?_, ?_⟩
  · intro r z hz
    obtain ⟨u, hu, rfl⟩ := hz
    apply mem_closedBall_zero_iff.mpr
    have hb := exponentialTupleCoordinates_image_subset_ball lie Exp chart hchart
      (rescaledTupleBases X words β cost (scale r)) (hR r) (S r) (hbox r)
    exact (flat.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp (hb ⟨u, hu, rfl⟩)) (norm_nonneg _))
  · exact (sequence_subexponential_upper_const hscale ‖flat.symm.toContinuousLinearMap‖).mul hRupper
      (Eventually.of_forall (fun _ => norm_nonneg _))
  · have h := (rescaled_tuple_volume_lower_sequence scale hscale lie Exp chart hchart
      X words b₀ β cost S hlower).linear_image hscale flat.symm
    have he (r : ℕ) :
        flatExponentialTupleCoordinates lie chart (rescaledTupleBases X words β cost (scale r)) flat '' S r =
        flat.symm '' (exponentialTupleCoordinates lie chart
          (rescaledTupleBases X words β cost (scale r)) '' S r) := by
      rw [← Set.image_comp]
      rfl
    simpa only [he] using h

end PolycyclicRecognition

end

end OAI
