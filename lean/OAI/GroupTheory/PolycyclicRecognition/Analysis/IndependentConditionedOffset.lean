import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConditionedGoodProbeOffset
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasuredGoodProbeOffset
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasuredRegionOffset
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeImageGeometry
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RetainedProbeAnchors
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionSubtypeProbePacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeImageTileCover
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Offset comparison with different source and target cone quotients -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators NNReal

variable {N D G Q : Type*} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]
  [IsTopologicalGroup G] [ProperSpace G]
  [T2Space N] [T2Space Q]


variable {W V Z : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

omit [T2Space Q] in
/-- Source counting uses the original polar-cone quotient; target restrictions
use its transformed cone. Their Haar products need not have the same quotient
or normalization. The source translation retains the original profile center. -/
theorem MeasuredProbeRegions.offset_nonpos_of_independent_conditioned_probes
    (π : N →* Q) (hπ : Continuous π)
    (μQ : Measure Q) (μI : Measure π.ker) (μ : Measure N) (ν : Measure D)
    [SFinite μQ] [SFinite μI] [SFinite μ] [SFinite ν]
    [μQ.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (actionQ : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * actionQ d q)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (P₂ : ℝ) (R : MeasuredProbeRegions π μQ μI ν scale P₂)
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ
      R.sectionMap R.section_rightInverse).symm (μQ.prod μI))
    {QS : Type*} [Group QS] [TopologicalSpace QS] [IsTopologicalGroup QS]
    [T2Space QS] [SecondCountableTopology QS] [MeasurableSpace QS] [BorelSpace QS]
    (πS : N →* QS) (hπS : Continuous πS)
    (μQS : Measure QS) (μIS : Measure πS.ker) (μS : Measure N)
    [SFinite μQS] [SFinite μIS] [μS.IsMulLeftInvariant]
    [μIS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
    (hφS : ∀ d, MeasurePreserving (φ d) μS μS)
    (σ : C(QS, N)) (hσ : ∀ q, πS (σ q) = q)
    (hμS : μS = Measure.map (quotientSectionHomeomorph πS hπS σ hσ).symm
      (μQS.prod μIS))
    (S : ℕ → N ≃ₜ N) (hS : ∀ n, MeasurePreserving (S n) μS μS)
    (hι : Topology.IsClosedEmbedding ι)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (d : ℕ → D) (ZQ : Set QS) (J : ℕ → Set πS.ker)
    (hZm : MeasurableSet ZQ) (hJm : ∀ n, MeasurableSet (J n))
    (hZ0 : μQS ZQ ≠ 0) (hZt : μQS ZQ ≠ ⊤)
    (hJ0 : ∀ n, μIS (J n) ≠ 0) (hJt : ∀ n, μIS (J n) ≠ ⊤)
    (good : ∀ n, Set (ZQ ×ˢ J n)) (hgood : ∀ n, IsCompact (good n))
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellSubtypeProbability (μQS.prod μIS) (ZQ ×ˢ J n) (hZm.prod (hJm n))
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (ZQ ×ˢ J n)) (good n))
    (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μIS (J n)).toReal)
    (tiles : ℕ → ℕ)
    (tile : ∀ n, (ZQ ×ˢ J n) → Fin (tiles n))
    (height : G →* Multiplicative W)
    (center base : ℕ → G) (anchorSuffix : ∀ n, Fin (tiles n) → G)
    (fallback : ℕ → G) (first second : ∀ n, (ZQ ×ˢ J n) → G)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b₁ b₂ : W)
    (translation : ℕ → N)
    (hfirst : ∀ n y, first n y = ι (translation n) * ι (S n
      ((y.val.2 : N) * σ y.val.1)))
    (hchart : ∀ n, chart n (z₀ n) = κ (d n))
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < 1 / 2)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (η : ℕ → ℝ) (δ Apath Bpath : ℝ) (E₁ E₂ : Set W)
    (Dbridge : ℝ) (hδ : 0 < δ)
    (hLip : ∀ n, LipschitzWith Λ (p n).val.1) (hD : (Λ : ℝ) * Dbridge ≤ δ)
    (hpaths : ∀ᶠ n in atTop, R.ControlsTwoPaths
      (fun u d => ι u * κ d) φ (fun g q => act g q) height cell E₁ E₂ η Apath Bpath δ n)
    (hprofiles : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (anchorSuffix n (tile n y)) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b₂)‖ ≤ η n ∧
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (second n y) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hbridge : ∀ᶠ n in atTop, ∀ y ∈ good n,
      dist (center n * second n y * chart n (z₀ n))
        (center n * first n y * chart n (z₀ n)) ≤ Dbridge * scale n)
    (hprobePaths : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ∃ (path₁ : Path (1 : G) (basedImage (p n).val.1
          (center n * base n * chart n (z₀ n))
          (center n * first n y * chart n (z₀ n))))
        (path₂ : Path (1 : G) (basedImage (p n).val.1
          (center n * anchorSuffix n (tile n y) * chart n (z₀ n))
          (center n * second n y * chart n (z₀ n)))),
        PathMetricBound path₁ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))))
    (ell : W →L[ℝ] ℝ) (tileLoss : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hbase : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n) (base n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖ ≤ η n)
    (hfallback : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n) (fallback n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hHaar : ∀ (g : G) (E : Set Q), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μQ E)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  classical
  obtain ⟨lower, source, hlower, hsource, hsep, hcount⟩ :=
    exists_absolute_section_subtype_probe_counts πS hπS σ hσ
      μQS μIS μS hμS ι κ φ hι hφS hc S hS hΛ p
      (fun n => center n * ι (translation n)) d ZQ J
      hZm hJm hZ0 hZt hJ0 hJt good hgood hmass scale P₁ hv hvol
  let image := fun n (y : ZQ ×ˢ J n) =>
    (p n).val.1 (center n * first n y * chart n (z₀ n))
  have hsource' : ∀ n, (source n : Set G) ⊆ image n '' good n := by
    intro n
    simpa only [image, hfirst, hchart, mul_assoc] using hsource n
  obtain ⟨points, hsub, hcover, hpoint⟩ :=
    exists_probe_image_tile_cover_sequence good image tiles tile source hsource'
  apply R.offset_nonpos_of_good_probes π hπ μQ μI μ ν φ ι κ hc hφ actionQ act hact
    scale hscale hscale0 P₂ hμ source tiles points good tile height (fun n => (p n).val.1)
    center base anchorSuffix fallback first second chart q z₀ A b₁ b₂
    cell hcell hcell0 hcelltop hsmall
    (fun n j x hx y hy hxy => hsep n x (hsub n j hx) y (hsub n j hy) hxy)
    hsurj η δ Apath Bpath E₁ E₂ Dbridge Λ hδ hLip hD hpaths
    (fun n j x hx => ((hpoint n j x).mp hx).2) hprofiles hbridge hprobePaths
    hcover P₁ ell (fun _ => lower) tileLoss hη hbase hfallback
    (sequence_subexponential_lower_const hscale hlower) htileLoss htile0 hHaar
    (Eventually.of_forall hcount) htiles

end PolycyclicRecognition

end

end OAI
