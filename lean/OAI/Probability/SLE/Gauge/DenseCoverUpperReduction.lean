import OAI.Probability.SLE.Gauge.FiniteCoverAssembly
import OAI.Probability.SLE.Gauge.CoverNumerics

namespace OAI

/-! Candidate and missed-cell tests imply the dense-cover upper bound. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- Spatial selection, missed-cell probability bounds, and one-mesh charging
produce the upper Hausdorff expectation. No measurable choice of disks is needed. -/
theorem expected_hausdorff_le_of_candidate_disks
    {Ω ι η : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (h : ℝ → ℝ) (E : Ω → Set ℂ)
    (I : ℕ → Ω → Finset ι) (M : ℕ → Finset η)
    (x : ℕ → ι → ℂ) (r : ℕ → ι → ℝ) (Q : ℕ → η → Set ℂ)
    (missed : ℕ → η → Set Ω)
    (hmissmeas : ∀ n k, k ∈ M n → MeasurableSet (missed n k))
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (R : ℝ) (C : ℝ≥0)
    (δ : ℕ → ℝ≥0∞) (hδ : Tendsto δ atTop (𝓝 0))
    (probBound : ℕ → η → ℝ≥0∞)
    (hprob : ∀ n k, k ∈ M n → P (missed n k) ≤ probBound n k)
    (hcleanup : Tendsto (fun n => ∑ k ∈ M n,
      extendedGauge h (ediam (Q n k)) * probBound n k) atTop (𝓝 0))
    (hgeometry : ∀ᵐ ω ∂P, ∀ n,
      (∀ i ∈ I n ω, r n i ≤ R) ∧
      (∀ i ∈ I n ω, closedBall (x n i) (r n i) ⊆ closedBall 0 R) ∧
      (∀ i ∈ I n ω,
        extendedGauge h (ediam (closedBall (x n i) (4 * r n i))) ≤
          (C : ℝ≥0∞) * wholeSausageCharge κ (γ ω) (v n)
            (closedBall (x n i) (r n i))) ∧
      (∀ i ∈ I n ω, ediam (closedBall (x n i) (4 * r n i)) ≤ δ n) ∧
      (∀ k ∈ M n, ediam (Q n k) ≤ δ n) ∧
      (∀ z ∈ E ω, (∃ i ∈ I n ω, z ∈ closedBall (x n i) (r n i)) ∨
        ∃ k ∈ M n, ω ∈ missed n k ∧ z ∈ Q n k)) :
    (∫⁻ ω, hausdorffGauge h (E ω) ∂P) ≤
      (C : ℝ≥0∞) * wholeSausageChargeBound κ R := by
  classical
  let error (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∑ k ∈ M n, (missed n k).indicator
      (fun _ => extendedGauge h (ediam (Q n k))) ω
  have herr (n : ℕ) : AEMeasurable (error n) P := by
    apply Measurable.aemeasurable
    exact Finset.measurable_sum (M n) (fun k hk =>
      measurable_const.indicator (hmissmeas n k hk))
  have herrlim : Tendsto (fun n => ∫⁻ ω, error n ω ∂P) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hcleanup (fun _ => bot_le) (fun n => ?_)
    exact expected_missed_cell_cost P (M n) (missed n)
      (hmissmeas n) (fun k => extendedGauge h (ediam (Q n k)))
      (probBound n) (hprob n)
  apply expected_hausdorff_le_of_finite_sausage_covers P κ hκ hκ8 γ hSLE
    h E δ hδ v hv R C error herr herrlim
  filter_upwards [hgeometry] with ω hω
  intro n
  obtain ⟨hr, hA, hcost, hdisk, hmiss, hcell⟩ := hω n
  let missedIndices := (M n).filter (fun k => ω ∈ missed n k)
  have he : (∑ k ∈ missedIndices, extendedGauge h (ediam (Q n k))) = error n ω := by
    simp [missedIndices, error, Finset.sum_filter, Set.indicator]
  have hc : ∀ z ∈ E ω,
      (∃ i ∈ I n ω, z ∈ closedBall (x n i) (r n i)) ∨
        ∃ k ∈ missedIndices, z ∈ Q n k := by
    intro z hz
    rcases hcell z hz with hz | ⟨k, hk, hkm, hkz⟩
    · exact Or.inl hz
    · exact Or.inr ⟨k, Finset.mem_filter.mpr ⟨hk, hkm⟩, hkz⟩
  obtain ⟨N, U, hU, hUd, hUc⟩ := exists_finite_selected_missed_cover
    (I n ω) missedIndices (x n) (r n) (Q n) (E ω) (closedBall 0 R)
    (wholeSausageMeasure κ (γ ω) (v n)) h R hr (δ n) C hA
    (by simpa only [wholeSausageMeasure_apply _ _ _ isClosed_closedBall.measurableSet]
      using hcost)
    hdisk (fun k hk => hmiss k (Finset.mem_filter.mp hk).1) hc
  refine ⟨N, U, hU, hUd, ?_⟩
  simpa only [wholeSausageMeasure_apply _ _ _ isClosed_closedBall.measurableSet, he]
    using hUc

end SLEExactGauge

end

end OAI
