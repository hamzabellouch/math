import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafMaximal

namespace OAI

/-!
# Disintegrating the relative leaf maximal estimate

The real-line estimate is integrated against the transverse measure.
This gives the relative maximal bound in an actual root box, using its
conditional kernel and the original ambient measure.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem relative_maximal_compProd_bound
    {Y : Type*} [MeasurableSpace Y] (N : ℕ)
    (hN : ∀ (ν : Measure ℝ) (E : Set ℝ), MeasurableSet E → ∀ c : ℝ≥0∞,
      c * ν {x | ∃ r : ℝ, 0 < r ∧
        c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)} ≤ (N : ℝ≥0∞) * ν E)
    (μ : Measure Y) [SFinite μ] (κ : Kernel Y ℝ) [IsSFiniteKernel κ]
    (B E : Set (Y × ℝ)) (hB : MeasurableSet B) (hE : MeasurableSet E)
    (c : ℝ≥0∞)
    (hbad : ∀ᵐ y ∂μ, ∀ᵐ t ∂κ y, (y, t) ∈ B → ∃ r : ℝ, 0 < r ∧
      c * κ y (closedBall t r) ≤ κ y ((Prod.mk y ⁻¹' E) ∩ closedBall t r)) :
    c * (μ ⊗ₘ κ) B ≤ (N : ℝ≥0∞) * (μ ⊗ₘ κ) E := by
  rw [Measure.compProd_apply hB, Measure.compProd_apply hE,
    ← lintegral_const_mul c (Kernel.measurable_kernel_prodMk_left hB),
    ← lintegral_const_mul (N : ℝ≥0∞) (Kernel.measurable_kernel_prodMk_left hE)]
  apply lintegral_mono_ae
  filter_upwards [hbad] with y hy
  exact (mul_le_mul' le_rfl (measure_mono_ae hy)).trans
    (hN (κ y) (Prod.mk y ⁻¹' E) (hE.preimage (measurable_const.prodMk measurable_id)) c)

/-- The Besicovitch constant remains uniform after integrating along
the actual conditional distributions in any root box. -/
theorem exists_rootBox_relative_maximal_constant :
    ∃ N : ℕ, ∀ {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
      (A : RootBox hij k) (μ : Measure (X n)) [IsFiniteMeasure μ]
      (B E : Set (X n)), MeasurableSet B → MeasurableSet E → ∀ c : ℝ≥0∞,
      (∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.conditionalKernel μ s,
        rootQuotientParametrization hij (s, t) ∈ B → ∃ r : ℝ, 0 < r ∧
        c * A.conditionalKernel μ s (closedBall t r) ≤
          A.conditionalKernel μ s
            ({u | rootQuotientParametrization hij (s, u) ∈ E} ∩ closedBall t r)) →
      c * (μ.restrict A.range) B ≤ (N : ℝ≥0∞) * (μ.restrict A.range) E := by
  obtain ⟨N, hN⟩ := exists_real_relative_maximal_constant_all_radii
  refine ⟨N, ?_⟩
  intro n i j k hij A μ _ B E hB hE c hbad
  have hparam : Measurable (rootQuotientParametrization (k := k) hij) :=
    (rootQuotientParametrization_localHomeomorph hij).continuous.measurable
  have hbound := relative_maximal_compProd_bound N hN (A.coordinateMeasure μ).fst
    (A.conditionalKernel μ)
    (rootQuotientParametrization hij ⁻¹' B) (rootQuotientParametrization hij ⁻¹' E)
    (hB.preimage hparam) (hE.preimage hparam) c hbad
  rw [← Measure.map_apply hparam hB, ← Measure.map_apply hparam hE,
    A.disintegrate μ] at hbound
  exact hbound

end DukePrimeDegree

end

end OAI
