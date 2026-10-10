import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafMaximalIntrinsic

namespace OAI

/-!
# Intrinsic leaf maximal inequality inside root boxes

A measurable set of points witnessing a bad intrinsic leaf interval has
small ambient measure, provided the witnessing interval stays in the
root box. The constant is independent of the box and ambient measure.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_intrinsic_rootBox_maximal_constant :
    ∃ N : ℕ, ∀ {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
      (A : RootBox hij k) (R : ℝ), A.time ⊆ rootLeafWindow R 0 →
      ∀ (μ : Measure (X n)) [IsFiniteMeasure μ],
      (∀ᵐ x ∂μ, ∀ v : ℝ,
        rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) →
      ∀ (B E : Set (X n)), MeasurableSet B → MeasurableSet E → ∀ c : ℝ≥0∞,
      (∀ᵐ z ∂A.coordinateMeasure μ,
        rootQuotientParametrization hij z ∈ B → ∃ r : ℝ, 0 < r ∧
        closedBall z.2 r ⊆ A.time ∧
        c * intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) (closedBall 0 r) ≤
          intrinsicRootLeaf hij μ (rootQuotientParametrization hij z)
            ({u | rightAction (rootQuotientParametrization hij z)
              (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩ closedBall 0 r)) →
      c * (μ.restrict A.range) B ≤ (N : ℝ≥0∞) * (μ.restrict A.range) E := by
  obtain ⟨N, hN⟩ := exists_rootBox_relative_maximal_constant
  refine ⟨N, ?_⟩
  intro n i j k hij A R hAR μ _ hfree B E hB hE c hbad
  apply hN hij A μ B E hB hE c
  have hspec : ∀ᵐ z ∂A.coordinateMeasure μ,
      A.IsNormalizedRootLeaf R μ z.1 (A.leafMeasure R μ z.1) :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_spec R hAR μ hfree)
  have hall : ∀ᵐ z ∂A.coordinateMeasure μ,
      rootQuotientParametrization hij z ∈ B → ∃ r : ℝ, 0 < r ∧
      c * A.conditionalKernel μ z.1 (closedBall z.2 r) ≤
        A.conditionalKernel μ z.1
          ({u | rootQuotientParametrization hij (z.1, u) ∈ E} ∩ closedBall z.2 r) := by
    filter_upwards [hbad, hspec, A.ae_leafMeasure_ball_pos R hAR μ hfree,
      A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree] with z hz hs hp he
    intro hx
    obtain ⟨r, hr, hinside, hmass⟩ := hz hx
    exact ⟨r, hr, intrinsic_bad_interval_to_conditional hij A R μ z.1 z.2 r E hE
      hs (hp 1 zero_lt_one) he hinside c hmass⟩
  have hh : (A.coordinateMeasure μ).fst ⊗ₘ A.conditionalKernel μ = A.coordinateMeasure μ := by
    change (A.coordinateMeasure μ).fst ⊗ₘ (A.coordinateMeasure μ).condKernel = _
    exact Measure.disintegrate _ _
  rw [← hh] at hall
  exact Measure.ae_ae_of_ae_compProd hall

end DukePrimeDegree

end

end OAI
