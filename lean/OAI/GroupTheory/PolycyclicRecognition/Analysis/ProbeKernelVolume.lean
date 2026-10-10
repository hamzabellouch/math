import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeSectionRestrictions
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedHaarVolume

namespace OAI

/-! # The ideal restriction has its intrinsic weighted Haar volume -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold Topology ENNReal BigOperators

variable {V I N Q : Type*} [LieRing V] [LieAlgebra ℝ V]
  [Group I] [Group N] [Group Q] [TopologicalSpace I] [TopologicalSpace N]
  [IsTopologicalGroup I] [IsTopologicalGroup N]
  (U : LieIdeal ℝ V) (π : N →* Q) (ι : I →* N)
  (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (π.ker : Set N))
  (ExpI : U → I) (ExpN : V → N) (hcompat : ∀ u : U, ι (ExpI u) = ExpN u)

include hcompat

omit [IsTopologicalGroup I] [IsTopologicalGroup N] in
/-- The ideal region used for the target-cell restriction is the image of
the actual intrinsic ideal set, not a possibly larger preimage region. -/
theorem exponentialIdealKernelRegion_eq_image (A : Set U) :
    exponentialIdealKernelRegion U π ExpN A =
      kernelRealization π ι hι hrange '' (ExpI '' A) := by
  ext n
  constructor
  · rintro ⟨u, hu, hn⟩
    refine ⟨ExpI u, ⟨u, hu, rfl⟩, ?_⟩
    apply Subtype.ext
    change ι (ExpI u) = (n : N)
    exact (hcompat u).trans hn.symm
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, (hcompat u)⟩

variable [MeasurableSpace I] [MeasurableSpace N] [BorelSpace I] [BorelSpace N]

omit [IsTopologicalGroup I] [IsTopologicalGroup N] in
/-- Transport through the kernel homeomorphism preserves the exact ideal
volume, for the same kernel measure used by quotient integration. -/
theorem exponentialIdealKernelRegion_measure (μ : Measure I) (A : Set U) :
    (Measure.map (kernelRealization π ι hι hrange) μ)
      (exponentialIdealKernelRegion U π ExpN A) = μ (ExpI '' A) := by
  rw [exponentialIdealKernelRegion_eq_image U π ι hι hrange ExpI ExpN hcompat]
  have he : MeasurableEmbedding (kernelRealization π ι hι hrange : I → π.ker) :=
    (kernelRealization π ι hι hrange).toHomeomorph.measurableEmbedding
  rw [he.map_apply,
    preimage_image_eq _ (kernelRealization π ι hι hrange).injective]

section Weighted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E I] [LieGroup (𝓘(ℝ, E)) ⊤ I]
  [T2Space I] [SimplyConnectedSpace I]

omit hcompat [IsTopologicalGroup I] [IsTopologicalGroup N] in
/-- The actual kernel region in the target packing has the expected ideal
exponent and a subexponential radius loss, in its transported Haar measure. -/
theorem exists_exponential_kernel_box_volumes
    (haar : NilpotentExponentialHaarInput E I)
    (groupExp : GroupLieAlgebra (𝓘(ℝ, E)) I → I) (hExp : IsGroupExponential groupExp)
    (e : U ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) I) (hnil : LieRing.IsNilpotent U)
    (hc : ∀ u : U, ι (groupExp (e u)) = ExpN u)
    {m : ℕ} (b : Basis (Fin m) ℝ U) (cost : Fin m → ℝ)
    (μ : Measure I) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    let μK := Measure.map (kernelRealization π ι hι hrange) μ
    let regions := fun n => exponentialIdealKernelRegion U π ExpN
      {u : U | ‖(exponentialRescaleBasis b cost (scale n)).equivFun u‖ ≤ R n}
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n, μK (regions n) ≠ ⊤ ∧
        (μK (regions n)).toReal = V n * Real.exp ((∑ j, cost j) * scale n) := by
  dsimp only
  obtain ⟨V, hV0, hV, hvol⟩ := haar_model_sequence_weighted_boxes haar groupExp hExp e hnil
    b cost μ scale R hs hR0 hR
  refine ⟨V, hV0, hV, ?_⟩
  intro n
  have heq : (Measure.map (kernelRealization π ι hι hrange) μ)
      (exponentialIdealKernelRegion U π ExpN
        {u : U | ‖(exponentialRescaleBasis b cost (scale n)).equivFun u‖ ≤ R n}) =
      μ (exponentialCoordinateBox (groupExp ∘ e) (exponentialRescaleBasis b cost (scale n)) (R n)) := by
    rw [exponentialIdealKernelRegion_measure U π ι hι hrange (groupExp ∘ e) ExpN hc]
    congr 1
    ext z
    simp only [mem_image, mem_ofPred_eq, exponentialCoordinateBox]
    exact exists_congr (fun u => and_comm)
  rw [heq]
  exact hvol n

omit hcompat [IsTopologicalGroup I] [IsTopologicalGroup N] in
/-- The source ideal unit boxes have a positive fixed coefficient, in the
same transported kernel measure used in the section coordinates. -/
theorem exists_exponential_kernel_unit_volumes
    (haar : NilpotentExponentialHaarInput E I)
    (groupExp : GroupLieAlgebra (𝓘(ℝ, E)) I → I) (hExp : IsGroupExponential groupExp)
    (e : U ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) I) (hnil : LieRing.IsNilpotent U)
    (hc : ∀ u : U, ι (groupExp (e u)) = ExpN u)
    {m : ℕ} (b : Basis (Fin m) ℝ U) (cost : Fin m → ℝ)
    (μ : Measure I) [μ.IsHaarMeasure] :
    let μK := Measure.map (kernelRealization π ι hι hrange) μ
    ∃ v : ℝ, 0 < v ∧ ∀ r : ℝ,
      let region := exponentialIdealKernelRegion U π ExpN
        {u : U | ‖(exponentialRescaleBasis b cost r).equivFun u‖ ≤ 1}
      μK region ≠ 0 ∧ μK region ≠ ⊤ ∧
        (μK region).toReal = v * Real.exp (r * ∑ j, cost j) := by
  obtain ⟨v, hv, hvol⟩ := haar_model_weighted_unit_volume haar groupExp hExp e hnil b cost μ
  refine ⟨v, hv, ?_⟩
  intro r
  dsimp only
  have heq : (Measure.map (kernelRealization π ι hι hrange) μ)
      (exponentialIdealKernelRegion U π ExpN
        {u : U | ‖(exponentialRescaleBasis b cost r).equivFun u‖ ≤ 1}) =
      μ (exponentialCoordinateBox (groupExp ∘ e) (exponentialRescaleBasis b cost r) 1) := by
    rw [exponentialIdealKernelRegion_measure U π ι hι hrange (groupExp ∘ e) ExpN hc]
    congr 1
    ext z
    simp only [mem_image, mem_ofPred_eq, exponentialCoordinateBox]
    exact exists_congr (fun u => and_comm)
  rw [heq]
  exact hvol r

end Weighted

end PolycyclicRecognition

end

end OAI
