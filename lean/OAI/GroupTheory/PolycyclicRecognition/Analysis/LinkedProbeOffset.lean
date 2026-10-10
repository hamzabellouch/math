import OAI.GroupTheory.PolycyclicRecognition.Analysis.IndependentConditionedOffset
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasuredGoodProbeOffset
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasuredRegionOffset
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeImageGeometry
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RetainedProbeAnchors
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionSubtypeProbePacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeImageTileCover
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # The offset inequality from the actual three linked probe chains -/

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
/-- Insert the three actual linked chains into the independent-quotient
volume comparison. The first and third chains supply the image paths; the
second supplies the retained anchor profile. All profiles retain their
original center, and their common error is derived from the chain bounds. -/
theorem MeasuredProbeRegions.offset_nonpos_of_linked_probe_bounds
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
    (center : ℕ → G) (sample origin neighbor : ℕ → N)
    (anchorRoot : ∀ n, Fin (tiles n) → N) (secondRoot : ∀ n, (ZQ ×ˢ J n) → N)
    (length : Fin 3 → ℕ)
    (vertex : ∀ k n, (ZQ ×ˢ J n) → Fin (length k + 1) → N)
    (hstart : ∀ n y, vertex 0 n y 0 = origin n)
    (hthird : ∀ n y, vertex 2 n y 0 = vertex 1 n y (Fin.last (length 1)))
    (hfirst : ∀ n y, vertex 0 n y (Fin.last (length 0)) =
      origin n * S n ((y.val.2 : N) * σ y.val.1))
    (hanchor : ∀ n y, vertex 1 n y (Fin.last (length 1)) = anchorRoot n (tile n y))
    (hsecond : ∀ n y, vertex 2 n y (Fin.last (length 2)) = secondRoot n y)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b : Bool → W)
    (hchart : ∀ n, chart n (z₀ n) = κ (d n))
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < 1 / 2)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
    (δ C Dbridge : ℝ) (E : Fin 3 → Set W) (hδ : 0 < δ)
    (hLip : ∀ n, LipschitzWith Λ (p n).val.1) (hD : (Λ : ℝ) * Dbridge ≤ δ)
    (hpaths : ∀ᶠ n in atTop, R.ControlsTwoPaths
      (fun u d => ι u * κ d) φ (fun g q => act g q) height cell (E 0) (E 2)
      (fun n => 2 * η n) C C δ n)
    (hbaseProfiles : ∀ᶠ n in atTop, ∀ s : Bool,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (ι (sample n * if s then neighbor n else origin n)) (Real.log (scale n))
        (chart n) (z₀ n) - (A (q (z₀ n)) + b s)‖ ≤ η n)
    (hprefixProfiles : ∀ᶠ n in atTop, ∀ y ∈ good n, ∀ k j,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (ι (sample n * vertex k n y j)) (Real.log (scale n))
        (chart n) (z₀ n) - (A (q (z₀ n)) + b (k != 0))‖ ≤ 2 * η n)
    (hbridge : ∀ᶠ n in atTop, ∀ y ∈ good n,
      dist (center n * ι (sample n * secondRoot n y) * chart n (z₀ n))
        (center n * ι (sample n * vertex 0 n y (Fin.last (length 0))) *
          chart n (z₀ n)) ≤ Dbridge * scale n)
    (hprobePaths : ∀ᶠ n in atTop, ∀ y ∈ good n, ∀ k,
      ∃ path : Path (1 : G) (basedImage (p n).val.1
        (center n * ι (sample n * vertex k n y 0) * chart n (z₀ n))
        (center n * ι (sample n * vertex k n y (Fin.last (length k))) * chart n (z₀ n))),
        PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ w ∈ E k, ‖(height (path t)).toAdd - scale n • w‖ ≤
          4 * scale n * η n + C * (1 + Real.log (2 + scale n)))
    (ell : W →L[ℝ] ℝ) (tileLoss : ℕ → ℝ)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hHaar : ∀ (g : G) (E : Set Q), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μQ E)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) :
    ell (b true - b false) ≤ 0 := by
  let base := fun n => ι (sample n * origin n)
  let fallback := fun n => ι (sample n * neighbor n)
  let anchors := fun n j => ι (sample n * anchorRoot n j)
  let first := fun n y => ι (sample n * vertex 0 n y (Fin.last (length 0)))
  let second := fun n y => ι (sample n * secondRoot n y)
  have herr : Tendsto (fun n => 2 * η n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hη.const_mul 2
  have hfirst' : ∀ n y, first n y = ι (sample n * origin n) *
      ι (S n ((y.val.2 : N) * σ y.val.1)) := by
    intro n y
    dsimp only [first]
    rw [hfirst]
    simp only [map_mul, mul_assoc]
  have hprofiles' : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (anchors n (tile n y)) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b true)‖ ≤ 2 * η n ∧
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (second n y) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b true)‖ ≤ 2 * η n := by
    filter_upwards [hprefixProfiles] with n hn y hy
    have ha := hn y hy 1 (Fin.last (length 1))
    have hs := hn y hy 2 (Fin.last (length 2))
    simp only [hanchor, hsecond, show ((1 : Fin 3) != 0) = true from rfl,
      show ((2 : Fin 3) != 0) = true from rfl] at ha hs
    exact ⟨ha, hs⟩
  have hprobePaths' : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ∃ (path₁ : Path (1 : G) (basedImage (p n).val.1
          (center n * base n * chart n (z₀ n))
          (center n * first n y * chart n (z₀ n))))
        (path₂ : Path (1 : G) (basedImage (p n).val.1
          (center n * anchors n (tile n y) * chart n (z₀ n))
          (center n * second n y * chart n (z₀ n)))),
        PathMetricBound path₁ (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E 0, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * (2 * η n) + C * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E 2, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * (2 * η n) + C * (1 + Real.log (2 + scale n))) := by
    filter_upwards [hprobePaths] with n hn y hy
    obtain ⟨p₀, hm₀, hh₀⟩ := hn y hy 0
    obtain ⟨p₂, hm₂, hh₂⟩ := hn y hy 2
    let p₀' : Path (1 : G) (basedImage (p n).val.1
        (center n * base n * chart n (z₀ n))
        (center n * first n y * chart n (z₀ n))) :=
      p₀.cast rfl (by simp only [base, first, hstart])
    let p₂' : Path (1 : G) (basedImage (p n).val.1
        (center n * anchors n (tile n y) * chart n (z₀ n))
        (center n * second n y * chart n (z₀ n))) :=
      p₂.cast rfl (by simp only [anchors, second, hthird, hanchor, hsecond])
    refine ⟨p₀', p₂', hm₀, hm₂, ?_, ?_⟩
    · intro t
      obtain ⟨w, hw, hb⟩ := hh₀ t
      refine ⟨w, hw, ?_⟩
      change ‖(height (p₀ t)).toAdd - scale n • w‖ ≤ _
      convert hb using 1
      ring
    · intro t
      obtain ⟨w, hw, hb⟩ := hh₂ t
      refine ⟨w, hw, ?_⟩
      change ‖(height (p₂ t)).toAdd - scale n • w‖ ≤ _
      convert hb using 1
      ring
  have hbase' : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (base n) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b false)‖ ≤ 2 * η n := by
    filter_upwards [hbaseProfiles] with n hn
    exact (hn false).trans (by nlinarith [hη0 n])
  have hfallback' : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (fallback n) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b true)‖ ≤ 2 * η n := by
    filter_upwards [hbaseProfiles] with n hn
    exact (hn true).trans (by nlinarith [hη0 n])
  exact R.offset_nonpos_of_independent_conditioned_probes π hπ μQ μI μ ν φ ι κ hc hφ
    actionQ act hact scale hscale hscale0 P₂ hμ πS hπS μQS μIS μS hφS σ hσ hμS
    S hS hι hΛ p d ZQ J hZm hJm hZ0 hZt hJ0 hJt good hgood hmass P₁ hv hvol
    tiles tile height center base anchors fallback first second chart q z₀ A (b false) (b true)
    (fun n => sample n * origin n) hfirst' hchart cell hcell hcell0 hcelltop
    hsmall hsurj (fun n => 2 * η n) δ C C (E 0) (E 2) Dbridge hδ hLip hD hpaths
    hprofiles' hbridge hprobePaths' ell tileLoss herr hbase' hfallback'
    htileLoss htile0 hHaar htiles

end PolycyclicRecognition

end

end OAI
