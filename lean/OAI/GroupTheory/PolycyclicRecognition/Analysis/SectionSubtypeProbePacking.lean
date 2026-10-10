import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionProbePacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactProbeLift

namespace OAI

/-! # Source counts for the compact subtype probes -/

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


variable [T2Space N] [T2Space Q]

omit [IsTopologicalGroup Q] [SecondCountableTopology N] in
/-- Compact good probes selected on the original product cell give the
actual separated image count. Their subtype probability is transported
exactly; the choice of starting sample causes no loss of source volume. -/
theorem exists_dilated_section_subtype_probe_counts
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
    (hZm : MeasurableSet Z) (hJm : ∀ n, MeasurableSet (J n))
    (hZ0 : μQ Z ≠ 0) (hZt : μQ Z ≠ ⊤)
    (hJ0 : ∀ n, μI (J n) ≠ 0) (hJt : ∀ n, μI (J n) ≠ ⊤)
    (K : ∀ n, Set (Z ×ˢ J n)) (hK : ∀ n, IsCompact (K n))
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellSubtypeProbability (μQ.prod μI) (Z ×ˢ J n) (hZm.prod (hJm n))
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (Z ×ˢ J n)) (K n))
    (scale : ℕ → ℝ) (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μI (J n)).toReal) :
    ∃ (c : ℝ) (source : ℕ → Finset G), 0 < c ∧
      (∀ n, (↑(source n) : Set G) ⊆
        (fun y : Z ×ˢ J n => basedImage (p n).val.1 (a n)
          (x n * ι (S n ((y.val.2 : N) * σ y.val.1)) * κ (d n))) '' K n) ∧
      (∀ n, ∀ u ∈ source n, ∀ w ∈ source n, u ≠ w → 1 ≤ dist u w) ∧
      ∀ n, c * Real.exp (scale n * P₁) ≤ ((source n).card : ℝ) := by
  let ambientK := fun n => Subtype.val '' K n
  have hproperties (n) := cellSubtypeProbability_compact_image (μQ.prod μI)
    (Z ×ˢ J n) (hZm.prod (hJm n))
    (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
    (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) (K n) (hK n)
  have hmass' (n) : ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellProbabilityMeasure (μQ.prod μI) (Z ×ˢ J n)
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (Q × π.ker)) (ambientK n) := by
    rw [(hproperties n).2.2.2]
    exact hmass n
  obtain ⟨c, source, hc, hsource, hsep, hcount⟩ := exists_dilated_section_probe_counts
    π hπ σ hs μQ μI μ hμ ι κ φ hι hφ hconj S hS hΛ p x a d Z J hZ0 hZt hJ0 hJt
    ambientK (fun n => (hproperties n).1) (fun n => (hproperties n).2.1)
    (fun n => (hproperties n).2.2.1) hmass' scale P₁ hv hvol
  refine ⟨c, source, hc, ?_, hsep, hcount⟩
  intro n
  simpa only [ambientK, image_image] using hsource n

omit [IsTopologicalGroup Q] [SecondCountableTopology N] in
/-- For normalized quasi-isometries the source net consists of the actual
image points. The count and separation are unchanged, and the image
witnesses now match the two-path offset theorem directly. -/
theorem exists_absolute_section_subtype_probe_counts
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
    (x : ℕ → G) (d : ℕ → D)
    (Z : Set Q) (J : ℕ → Set π.ker)
    (hZm : MeasurableSet Z) (hJm : ∀ n, MeasurableSet (J n))
    (hZ0 : μQ Z ≠ 0) (hZt : μQ Z ≠ ⊤)
    (hJ0 : ∀ n, μI (J n) ≠ 0) (hJt : ∀ n, μI (J n) ≠ ⊤)
    (K : ∀ n, Set (Z ×ˢ J n)) (hK : ∀ n, IsCompact (K n))
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellSubtypeProbability (μQ.prod μI) (Z ×ˢ J n) (hZm.prod (hJm n))
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (Z ×ˢ J n)) (K n))
    (scale : ℕ → ℝ) (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μI (J n)).toReal) :
    ∃ (c : ℝ) (source : ℕ → Finset G), 0 < c ∧
      (∀ n, (↑(source n) : Set G) ⊆
        (fun y : Z ×ˢ J n => (p n).val.1
          (x n * ι (S n ((y.val.2 : N) * σ y.val.1)) * κ (d n))) '' K n) ∧
      (∀ n, ∀ u ∈ source n, ∀ w ∈ source n, u ≠ w → 1 ≤ dist u w) ∧
      ∀ n, c * Real.exp (scale n * P₁) ≤ ((source n).card : ℝ) := by
  obtain ⟨c, source, hc, hsource, hsep, hcount⟩ := exists_dilated_section_subtype_probe_counts
    π hπ σ hs μQ μI μ hμ ι κ φ hι hφ hconj S hS hΛ p x (fun _ => 1) d
    Z J hZm hJm hZ0 hZt hJ0 hJt K hK hmass scale P₁ hv hvol
  refine ⟨c, source, hc, ?_, hsep, hcount⟩
  intro n
  simpa only [basedImage, (p n).property.2, inv_one, one_mul] using hsource n

end PolycyclicRecognition

end

end OAI
