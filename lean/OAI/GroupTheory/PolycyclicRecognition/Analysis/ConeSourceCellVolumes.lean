import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeIdealBoxCalculus
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedHaarVolume
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxCompact
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactProbeLift

namespace OAI

/-! # The source probability cell and its exact exponential volume -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set Metric
open scoped Manifold BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {EI I N Q : Type*} [NormedAddCommGroup EI] [NormedSpace ℝ EI]
  [FiniteDimensional ℝ EI] [TopologicalSpace I] [ChartedSpace EI I] [Group I]
  [LieGroup (𝓘(ℝ, EI)) ⊤ I] [T2Space I] [SimplyConnectedSpace I]
  [MeasurableSpace I] [BorelSpace I] [IsTopologicalGroup I]
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [MeasurableSpace N] [BorelSpace N] [Group Q] [TopologicalSpace Q]
  [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]

omit [IsTopologicalGroup I] [IsTopologicalGroup N] [T2Space Q] [BorelSpace Q] in
/-- In the actual kernel Haar measure, the source box has one fixed positive
coefficient and the exact sum-of-word-widths exponent. The quotient factor
is fixed and has finite positive measure. -/
theorem cone_source_cell_volumes
    (eI : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EI)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, EI)) I → I) (hExpI : IsGroupExponential ExpI)
    (haarI : NilpotentExponentialHaarInput EI I)
    (chartI : GroupLieAlgebra (𝓘(ℝ, EI)) I ≃ₜ I) (hchartI : ∀ v, chartI v = ExpI v)
    (π : N →* Q) (ι : I →* N) (hι : Topology.IsClosedEmbedding ι)
    (hrange : range ι = (π.ker : Set N))
    (μI : Measure I) [μI.IsHaarMeasure]
    (μQ : Measure Q) [μQ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μQ]
    {d : ℕ} (eQ : (Fin d → ℝ) ≃ₜ Q)
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C) (scale : ℕ → ℝ) :
    let ZQ := eQ '' closedBall (0 : Fin d → ℝ) 1
    let J := fun n => kernelRealization π ι hι hrange ''
      M.coneIdealBox C (ExpI ∘ eI) s β (scale n) 1
    let μK := Measure.map (kernelRealization π ι hι hrange) μI
    IsCompact ZQ ∧ μQ ZQ ≠ 0 ∧ μQ ZQ ≠ ⊤ ∧
      ∃ v : ℝ, 0 < v ∧ ∀ n,
        IsCompact (J n) ∧ μK (J n) ≠ 0 ∧ μK (J n) ≠ ⊤ ∧
        (μK (J n)).toReal = v * Real.exp (scale n * ∑ j,
          M.coneIdealWordCost C s (β.val j)) ∧
        IsCompact (ZQ ×ˢ J n) := by
  dsimp only
  let ZQ := eQ '' closedBall (0 : Fin d → ℝ) 1
  let J := fun n => kernelRealization π ι hι hrange ''
    M.coneIdealBox C (ExpI ∘ eI) s β (scale n) 1
  let μK := Measure.map (kernelRealization π ι hι hrange) μI
  have hZ : IsCompact ZQ := (isCompact_closedBall (0 : Fin d → ℝ) 1).image eQ.continuous
  have hZ0 : μQ ZQ ≠ 0 := by
    have hopen : IsOpen (eQ '' ball (0 : Fin d → ℝ) 1) := eQ.isOpenMap _ isOpen_ball
    have hne : (eQ '' ball (0 : Fin d → ℝ) 1).Nonempty :=
      ⟨eQ 0, ⟨0, mem_ball_self zero_lt_one, rfl⟩⟩
    exact ne_of_gt ((hopen.measure_pos μQ hne).trans_le
      (measure_mono (image_mono ball_subset_closedBall)))
  obtain ⟨v, hv, hvol⟩ := haar_model_weighted_unit_volume haarI ExpI hExpI eI
    (M.coneIdeal_nilpotent C)
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    (fun j => M.coneIdealWordCost C s (β.val j)) μI
  refine ⟨hZ, hZ0, hZ.measure_ne_top, v, hv, ?_⟩
  intro n
  have hbox : IsCompact (M.coneIdealBox C (ExpI ∘ eI) s β (scale n) 1) :=
    isCompact_exponentialCoordinateBox eI.toLinearEquiv ExpI chartI hchartI
      (M.coneIdealBoxBasis C s β (scale n)) 1 zero_le_one
  have hJ : IsCompact (J n) := hbox.image (kernelRealization π ι hι hrange).continuous
  have hμ : μK (J n) = μI (M.coneIdealBox C (ExpI ∘ eI) s β (scale n) 1) := by
    change (Measure.map (kernelRealization π ι hι hrange) μI)
      (kernelRealization π ι hι hrange ''
        M.coneIdealBox C (ExpI ∘ eI) s β (scale n) 1) = _
    have he : MeasurableEmbedding (kernelRealization π ι hι hrange : I → π.ker) :=
      (kernelRealization π ι hι hrange).toHomeomorph.measurableEmbedding
    rw [he.map_apply]
    exact congrArg μI (preimage_image_eq _ (kernelRealization π ι hι hrange).injective)
  obtain ⟨hzero, hfinite, heq⟩ := hvol (scale n)
  change μI (M.coneIdealBox C (ExpI ∘ eI) s β (scale n) 1) ≠ 0 at hzero
  change μI (M.coneIdealBox C (ExpI ∘ eI) s β (scale n) 1) ≠ ⊤ at hfinite
  change (μI (M.coneIdealBox C (ExpI ∘ eI) s β (scale n) 1)).toReal = _ at heq
  exact ⟨hJ, hμ.trans_ne hzero, hμ.trans_ne hfinite, hμ ▸ heq, hZ.prod hJ⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
