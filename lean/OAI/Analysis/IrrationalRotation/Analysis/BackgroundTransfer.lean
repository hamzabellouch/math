import OAI.Analysis.IrrationalRotation.Model.BackgroundData
import OAI.Analysis.IrrationalRotation.Analysis.ContinuityCoboundary
import OAI.Analysis.IrrationalRotation.Analysis.TransferSupport

namespace OAI

open MeasureTheory Set Filter Function
open scoped ENNReal

namespace InvariantProjection.Continuity

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem measurable_backgroundTransfer (σ : X ≃ᵐ X) (v : X → ℝ)
    (W : ℕ) (hv : Measurable v) :
    Measurable (backgroundTransfer σ.toEquiv v W) := by
  unfold backgroundTransfer backwardSum
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_sum
  intro r hr
  exact hv.comp (σ.symm.measurable.iterate (r + 1))

omit [MeasurableSpace X] in

theorem support_backgroundTransfer_subset (σ : X ≃ X) (v : X → ℝ) (W : ℕ) :
    support (backgroundTransfer σ v W) ⊆
      ⋃ r ∈ Finset.range W, ((σ.symm : X → X)^[r + 1]) ⁻¹' support v := by
  intro x hx
  have hsum : (∑ n ∈ Finset.range W, backwardSum σ v (n + 1) x) ≠ 0 :=
    (mul_ne_zero_iff.mp hx).2
  obtain ⟨n, hn, hnx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  obtain ⟨r, hr, hrx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnx
  refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨?_, hrx⟩⟩
  apply Finset.mem_range.mpr
  have hn' := Finset.mem_range.mp hn
  have hr' := Finset.mem_range.mp hr
  omega

theorem measure_support_backgroundTransfer_le (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) (v : X → ℝ) (W : ℕ) :
    μ (support (backgroundTransfer σ.toEquiv v W)) ≤
      (W : ℝ≥0∞) * μ (support v) := by
  calc
    _ ≤ μ (⋃ r ∈ Finset.range W,
        ((σ.symm : X → X)^[r + 1]) ⁻¹' support v) :=
      measure_mono (support_backgroundTransfer_subset σ.toEquiv v W)
    _ ≤ ∑ r ∈ Finset.range W,
        μ (((σ.symm : X → X)^[r + 1]) ⁻¹' support v) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ Finset.range W, μ (support v) := by
      exact Finset.sum_le_sum fun r _ => ((hσ.symm σ).iterate (r + 1)).measure_preimage_le _
    _ = _ := by simp

end InvariantProjection.Continuity

namespace Invariant233.BackgroundCost

open InvariantProjection.Continuity Invariant233.TransferSupport

variable {θ : ℝ} (d : BackgroundBumpData θ)

theorem tsum_measure_backgroundTransfer_support_ne_top :
    (∑' n, circleMeasure (support (backgroundTransfer
      (Equiv.addRight (θ : Circle)) (d.bump n) (2 ^ (n + 2))))) ≠ ∞ := by
  apply ne_top_of_le_ne_top (show (1 / 2 : ℝ≥0∞) ≠ ∞ by norm_num)
  apply le_trans _ d.weighted_support_bound
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    _ ≤ ((2 ^ (n + 2) : ℕ) : ℝ≥0∞) * circleMeasure (support (d.bump n)) :=
      measure_support_backgroundTransfer_le (MeasurableEquiv.addRight (θ : Circle))
        (measurePreserving_add_right volume _) _ _
    _ ≤ (2 : ℝ≥0∞) ^ (n + 2) * circleMeasure (Metric.closedBall 0 (d.radius n)) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        mul_le_mul_right (measure_mono (d.bump_support n))
          (((2 ^ (n + 2) : ℕ) : ℝ≥0∞))

theorem tsum_measure_backgroundBump_support_ne_top :
    (∑' n, circleMeasure (support (d.bump n))) ≠ ∞ := by
  apply ne_top_of_le_ne_top (show (1 / 2 : ℝ≥0∞) ≠ ∞ by norm_num)
  apply le_trans _ d.weighted_support_bound
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    _ ≤ circleMeasure (Metric.closedBall 0 (d.radius n)) := measure_mono (d.bump_support n)
    _ ≤ (2 : ℝ≥0∞) ^ (n + 2) * circleMeasure (Metric.closedBall 0 (d.radius n)) := by
      exact le_mul_of_one_le_left' (one_le_pow₀ (by norm_num))

theorem ae_finite_backgroundTransfer_support :
    ∀ᵐ x ∂circleMeasure, (support (fun n => backgroundTransfer
      (Equiv.addRight (θ : Circle)) (d.bump n) (2 ^ (n + 2)) x)).Finite :=
  ae_finite_transfer_support _ (tsum_measure_backgroundTransfer_support_ne_top d)

theorem measurable_backgroundTransferSum : Measurable (backgroundTransferSum d) := by
  apply Measurable.tsum
  intro n
  exact measurable_backgroundTransfer (MeasurableEquiv.addRight (θ : Circle))
    _ _ (d.continuous_bump n).measurable

theorem backgroundCost_ae_coboundary :
    backgroundCost d =ᵐ[circleMeasure] fun x =>
      1 + backgroundTransferSum d (x + (θ : Circle)) - backgroundTransferSum d x := by
  have hsum : ∀ᵐ x ∂circleMeasure, Summable (fun n => d.bump n x) :=
    (ae_finite_transfer_support _ (tsum_measure_backgroundBump_support_ne_top d)).mono
      (fun _ hx => summable_of_hasFiniteSupport hx)
  have hneg := ae_tsum_coboundary d.bump (backgroundNegative d)
    (fun n => backgroundTransfer (Equiv.addRight (θ : Circle)) (d.bump n) (2 ^ (n + 2)))
    (fun x : Circle => x + (θ : Circle))
    (measurePreserving_add_right volume _).quasiMeasurePreserving
    (tsum_measure_backgroundTransfer_support_ne_top d) hsum (fun n => by
      apply Eventually.of_forall
      intro x
      have h := background_coboundary (Equiv.addRight (θ : Circle)) (d.bump n)
        (2 ^ (n + 2)) (pow_ne_zero _ (by norm_num)) x
      change backgroundNegative d n x = _
      change d.bump n x - backgroundNegative d n x = _ at h
      change d.bump n x - backgroundNegative d n x =
        backgroundTransfer (Equiv.addRight (θ : Circle)) (d.bump n) (2 ^ (n + 2))
          (x + (θ : Circle)) -
        backgroundTransfer (Equiv.addRight (θ : Circle)) (d.bump n) (2 ^ (n + 2)) x at h
      linarith)
  filter_upwards [hneg] with x hx
  unfold backgroundCost backgroundTransferSum
  rw [hx.2]
  ring

end Invariant233.BackgroundCost

end OAI
