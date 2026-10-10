import OAI.Analysis.FiniteFactor.CrossedProduct.ResamplingLaw

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter ProbabilityTheory CouplingParameters
open scoped ENNReal
noncomputable section

/-- The independent Haar pair has no equality boundary at any coordinate. -/
theorem sourceSamplingPairHaar_coordinate_ne :
    ∀ᵐ z ∂sourceSamplingPairHaar, ∀ i, (z i).1 ≠ (z i).2 := by
  let : NullSingletonClass unitIntervalMeasure := by unfold unitIntervalMeasure; infer_instance
  apply ae_all_iff.mpr
  intro i
  have hp : ∀ᵐ z ∂unitIntervalMeasure.prod unitIntervalMeasure, z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    apply Eventually.of_forall
    intro x
    have hh : ∀ᵐ y ∂unitIntervalMeasure, y ≠ x := by
      rw [ae_iff]
      simp
    exact hh.mono fun y hy => hy.symm
  exact (measurePreserving_eval_infinitePi
    (fun _ : SourceCoordinate => unitIntervalMeasure.prod unitIntervalMeasure) i).quasiMeasurePreserving.ae hp

/-- Strict and non-strict order coincide for the replacement coordinates. -/
theorem sourceSamplingLimit_order_event (I : Finset SourceCoordinate) :
    (sourceSamplingLimitMap I ⁻¹' sourceSamplingOrdered) =ᵐ[sourceSamplingPairHaar]
      sourceSamplingTriangleSet I := by
  filter_upwards [sourceSamplingPairHaar_coordinate_ne] with z hz
  apply propext
  change (∀ i, (z i).1 ≤ if i ∈ I then (z i).2 else (z i).1) ↔
    (∀ i ∈ I, (z i).1 < (z i).2)
  constructor
  · intro h i hi
    exact lt_of_le_of_ne (by simpa [hi] using h i) (hz i)
  · intro h i
    by_cases hi : i ∈ I
    · simpa [hi] using (h i hi).le
    · simp [hi]

theorem sourceResampling_ordered_restriction (I : Finset SourceCoordinate) :
    (sourceSamplingHaar ⊗ₘ sourceResamplingKernel I).restrict sourceSamplingOrdered =
      sourceSamplingLambda I := by
  rw [sourceResampling_compProd_eq_map,
    Measure.restrict_map (sourceSamplingLimitMap_measurable I) sourceSamplingOrdered_measurable,
    Measure.restrict_congr_set (sourceSamplingLimit_order_event I)]
  rfl

/-- Exact finite-prefix reference mixture after imposing global order. -/
theorem sourceFiniteReference_ordered_mixture (F : Finset SourceCoordinate) :
    (sourceSamplingHaar ⊗ₘ sourceFiniteReferenceKernel F).restrict sourceSamplingOrdered =
      ((2 : ℝ≥0∞)⁻¹)^F.card • ∑ I ∈ F.powerset, sourceSamplingLambda I := by
  have hs : (∑ I ∈ F.powerset, sourceSamplingHaar ⊗ₘ sourceResamplingKernel I).restrict sourceSamplingOrdered =
      ∑ I ∈ F.powerset, (sourceSamplingHaar ⊗ₘ sourceResamplingKernel I).restrict sourceSamplingOrdered :=
    map_sum (Measure.restrictₗ sourceSamplingOrdered) _ _
  rw [sourceFiniteReference_compProd_mixture,Measure.restrict_smul,hs]
  simp_rw [sourceResampling_ordered_restriction]

end
end FiniteFactor

end OAI
