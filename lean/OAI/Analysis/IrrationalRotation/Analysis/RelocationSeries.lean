import OAI.Analysis.IrrationalRotation.Analysis.ContinuityCoboundary
import OAI.Analysis.IrrationalRotation.Analysis.TransferSupport

namespace OAI

open scoped ENNReal BigOperators
open MeasureTheory Function

namespace InvariantProjection.Continuity

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem measurable_relocationTransfer (σ : X ≃ᵐ X) (h : X → ℝ)
    (φ : ℕ → X → ℝ) (H : ℕ) (hh : Measurable h)
    (hφ : ∀ n, Measurable (φ n)) :
    Measurable (relocationTransfer σ.toEquiv h φ H) := by
  unfold relocationTransfer backwardSum
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_sum
  intro r hr
  exact (hh.comp (σ.symm.measurable.iterate (r + 1))).mul
    ((hφ n).comp (σ.symm.measurable.iterate (r + 1)))

theorem exists_measurable_relocation_series_transfer {ι : Type*} [Countable ι]
    (σ : X ≃ᵐ X) (hσ : MeasurePreserving σ μ μ)
    (h : ι → X → ℝ) (φ : ι → ℕ → X → ℝ) (H : ι → ℕ)
    (hm : ∀ i, Measurable (h i)) (hφm : ∀ i n, Measurable (φ i n))
    (hpartition : ∀ i x, ∑ n ∈ Finset.range (H i + 1), φ i n x = 1)
    (hcost : ∑' i, (H i : ℝ≥0∞) * μ (support (h i)) ≠ ∞)
    (hsum : ∀ᵐ x ∂μ, Summable (fun i => h i x)) :
    ∃ b : X → ℝ, Measurable b ∧
      (∀ᵐ x ∂μ, (support (fun i => relocationTransfer σ.toEquiv (h i) (φ i) (H i) x)).Finite) ∧
      ∀ᵐ x ∂μ,
        Summable (fun i => relocated σ.toEquiv (h i) (φ i) (H i) x) ∧
        (∑' i, relocated σ.toEquiv (h i) (φ i) (H i) x) =
          (∑' i, h i x) + b x - b (σ x) := by
  let d : ι → X → ℝ := fun i => relocationTransfer σ.toEquiv (h i) (φ i) (H i)
  have hdmeas (i : ι) : Measurable (d i) :=
    measurable_relocationTransfer σ (h i) (φ i) (H i) (hm i) (hφm i)
  have hdcost : ∑' i, μ (support (d i)) ≠ ∞ := by
    apply ne_top_of_le_ne_top hcost
    exact ENNReal.tsum_le_tsum fun i =>
      measure_support_relocationTransfer_le σ hσ (h i) (hm i) (φ i) (H i)
  refine ⟨fun x => ∑' i, d i x, Measurable.tsum hdmeas, ?_, ?_⟩
  · exact Invariant233.TransferSupport.ae_finite_transfer_support d hdcost
  · apply Invariant233.TransferSupport.ae_tsum_coboundary h
      (fun i => relocated σ.toEquiv (h i) (φ i) (H i)) d σ
      hσ.quasiMeasurePreserving hdcost hsum
    intro i
    exact Filter.Eventually.of_forall fun x =>
      relocated_eq_add_coboundary σ.toEquiv (h i) (φ i) (H i) x (hpartition i x)

end InvariantProjection.Continuity

end OAI
