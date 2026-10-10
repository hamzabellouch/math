import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeSourcePacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuotientSectionHaar

namespace OAI

/-! # Source counts in the actual dilated ideal-section coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped NNReal Pointwise

variable {N D G Q : Type*} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology N] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]

omit [IsTopologicalGroup Q] [SecondCountableTopology N] in
/-- The original product probe measure, the moving scalar dilation, and
fixed-pivot metric packing give one source exponent with a uniform positive
constant. The retained mass is measured before choosing its base sample. -/
theorem exists_dilated_section_probe_counts
    (π : N →* Q) (hπ : Continuous π) (σ : C(Q, N)) (hs : ∀ q, π (σ q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
    (μ : Measure N) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ σ hs).symm (μQ.prod μI))
    (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (hι : Topology.IsClosedEmbedding ι)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (S : ℕ → N ≃ₜ N) (hS : ∀ n, MeasurePreserving (S n) μ μ)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (x a : ℕ → G) (d : ℕ → D)
    (Z : Set Q) (J : ℕ → Set π.ker)
    (hZ0 : μQ Z ≠ 0) (hZt : μQ Z ≠ ⊤)
    (hJ0 : ∀ n, μI (J n) ≠ 0) (hJt : ∀ n, μI (J n) ≠ ⊤)
    (K : ℕ → Set (Q × π.ker))
    (hK : ∀ n, IsCompact (K n)) (hKm : ∀ n, MeasurableSet (K n))
    (hKsub : ∀ n, K n ⊆ Z ×ˢ J n)
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellProbabilityMeasure (μQ.prod μI) (Z ×ˢ J n)
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (Q × π.ker)) (K n))
    (scale : ℕ → ℝ) (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μI (J n)).toReal) :
    ∃ (c : ℝ) (source : ℕ → Finset G), 0 < c ∧
      (∀ n, (↑(source n) : Set G) ⊆
        (fun y : Q × π.ker => basedImage (p n).val.1 (a n)
          (x n * ι (S n ((y.2 : N) * σ y.1)) * κ (d n))) '' K n) ∧
      (∀ n, ∀ u ∈ source n, ∀ w ∈ source n, u ≠ w → 1 ≤ dist u w) ∧
      ∀ n, c * Real.exp (scale n * P₁) ≤ ((source n).card : ℝ) := by
  let chart := quotientSectionHomeomorph π hπ σ hs
  let e := fun n => chart.symm.trans (S n)
  have he (n : ℕ) : MeasurableEmbedding (e n) := (e n).measurableEmbedding
  have heμ (n : ℕ) : μ = Measure.map (e n) (μQ.prod μI) := by
    change μ = Measure.map ((S n) ∘ chart.symm) (μQ.prod μI)
    rw [← Measure.map_map (S n).measurable chart.symm.measurable, ← hμ]
    exact (hS n).map_eq.symm
  have hA0 (n : ℕ) : (μQ.prod μI) (Z ×ˢ J n) ≠ 0 := by
    rw [Measure.prod_prod]
    exact mul_ne_zero hZ0 (hJ0 n)
  have hAt (n : ℕ) : (μQ.prod μI) (Z ×ˢ J n) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hZt (hJt n)
  have hq : 0 < (μQ Z).toReal := ENNReal.toReal_pos hZ0 hZt
  have hv' : 0 < (μQ Z).toReal * v := mul_pos hq hv
  have hvol' (n : ℕ) : ((μQ Z).toReal * v) * Real.exp (scale n * P₁) ≤
      ((μQ.prod μI) (Z ×ˢ J n)).toReal := by
    rw [Measure.prod_prod, ENNReal.toReal_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hvol n) hq.le
  obtain ⟨c, source, hc, hsub, hsep, hcount⟩ := exists_probe_source_count_sequence
    ι κ φ μ hι hφ hconj (μQ.prod μI) (fun n => e n) he (fun n => (e n).continuous) heμ
    hΛ p x a d (fun n => Z ×ˢ J n) K hA0 hAt hK hKm hKsub hmass scale P₁ hv' hvol'
  exact ⟨c, source, hc, hsub, hsep, hcount⟩

end PolycyclicRecognition

end

end OAI
