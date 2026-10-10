import OAI.NumberTheory.DukePrimeDegree.Geometry.RootBoxMargins

namespace OAI

/-!
# Uniform short-interval maximal estimates on compact sets

The root-box estimate and a finite cover of a compact set give one
positive radius and one finite constant, uniformly over all finite
ambient measures with essentially free root action.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem compact_intrinsic_maximal_bound
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (K : Set (X n)) (hK : IsCompact K) :
    ∃ (M : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ (μ : Measure (X n)) [IsFiniteMeasure μ],
      (∀ᵐ x ∂μ, ∀ v : ℝ,
        rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) →
      ∀ (B E : Set (X n)), MeasurableSet B → MeasurableSet E → B ⊆ K →
      ∀ c : ℝ≥0∞,
      (∀ᵐ x ∂μ, x ∈ B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
        c * intrinsicRootLeaf hij μ x (closedBall 0 r) ≤
          intrinsicRootLeaf hij μ x
            ({u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩
              closedBall 0 r)) →
      c * μ B ≤ (M : ℝ≥0∞) * μ E := by
  obtain ⟨N, hN⟩ := exists_intrinsic_rootBox_maximal_constant
  obtain ⟨F, δ, hδ, hcover, hmargin⟩ := compact_bufferedRootBox_cover hij K hK
  refine ⟨F.card * N, δ, hδ, ?_⟩
  intro μ _ hfree B E hB hE hBK c hbad
  have hlocal (A : BufferedRootBox hij) (hAF : A ∈ F) :
      c * μ (B ∩ A.core) ≤ (N : ℝ≥0∞) * μ E := by
    have hBC := hB.inter A.core_open.measurableSet
    have hparam : Measurable (rootQuotientParametrization (k := A.pivot) hij) :=
      (rootQuotientParametrization_localHomeomorph hij).continuous.measurable
    have hbadcoord : ∀ᵐ z ∂A.box.coordinateMeasure μ,
        rootQuotientParametrization hij z ∈ B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
        c * intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) (closedBall 0 r) ≤
          intrinsicRootLeaf hij μ (rootQuotientParametrization hij z)
            ({u | rightAction (rootQuotientParametrization hij z)
              (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩ closedBall 0 r) := by
      have hmap := ae_restrict_of_ae (s := A.box.range) hbad
      rw [← A.box.map_coordinateMeasure μ] at hmap
      exact ae_of_ae_map hparam.aemeasurable hmap
    have hbound := hN hij A.box A.radius A.time_bound μ hfree (B ∩ A.core) E hBC hE c (by
      filter_upwards [hbadcoord, A.box.coordinateMeasure_ae_domain μ] with z hz hzd
      intro hx
      obtain ⟨r, hr, hrδ, hmass⟩ := hz hx.1
      exact ⟨r, hr, (closedBall_subset_closedBall (hrδ.trans (hmargin A hAF))).trans
        (A.time_margin z hzd hx.2), hmass⟩)
    rw [Measure.restrict_apply hBC,
      inter_eq_left.mpr (inter_subset_right.trans A.core_subset), Measure.restrict_apply hE] at hbound
    exact hbound.trans (mul_le_mul' le_rfl (measure_mono inter_subset_left))
  have hBcover : B ⊆ ⋃ A ∈ F, B ∩ A.core := by
    intro x hx
    obtain ⟨A, hA⟩ := mem_iUnion.mp (hcover (hBK hx))
    obtain ⟨hAF, hxA⟩ := mem_iUnion.mp hA
    exact mem_iUnion.mpr ⟨A, mem_iUnion.mpr ⟨hAF, hx, hxA⟩⟩
  calc
    c * μ B ≤ c * μ (⋃ A ∈ F, B ∩ A.core) := mul_le_mul' le_rfl (measure_mono hBcover)
    _ ≤ c * ∑ A ∈ F, μ (B ∩ A.core) :=
      mul_le_mul' le_rfl (measure_biUnion_finset_le F _)
    _ = ∑ A ∈ F, c * μ (B ∩ A.core) := Finset.mul_sum ..
    _ ≤ ∑ _A ∈ F, (N : ℝ≥0∞) * μ E := Finset.sum_le_sum fun A hAF => hlocal A hAF
    _ = (↑(F.card * N) : ℝ≥0∞) * μ E := by simp [nsmul_eq_mul, mul_assoc]

end DukePrimeDegree

end

end OAI
