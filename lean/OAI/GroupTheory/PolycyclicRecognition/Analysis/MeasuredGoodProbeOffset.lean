import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasuredRegionOffset
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeImageGeometry
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RetainedProbeAnchors

namespace OAI

/-! # The measured offset inequality from retained good probes -/

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


variable {W V Z : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Apply the measured two-path argument to the retained good probes.
The actual source bridge and the common second-sheet profile give the
short target bridge. Empty tiles use the original neighboring anchor,
so only selected anchors require the good-profile estimate. -/
theorem MeasuredProbeRegions.offset_nonpos_of_good_probes
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
    (source : ℕ → Finset G) (tiles : ℕ → ℕ)
    (points : ∀ n, Fin (tiles n) → Finset G)
    {Y : ℕ → Type*} (good : ∀ n, Set (Y n))
    (tile : ∀ n, Y n → Fin (tiles n))
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (center base : ℕ → G) (anchorSuffix : ∀ n, Fin (tiles n) → G)
    (fallback : ℕ → G) (first second : ∀ n, Y n → G)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b₁ b₂ : W)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (η : ℕ → ℝ) (δ Apath Bpath : ℝ) (E₁ E₂ : Set W)
    (Dbridge : ℝ) (Λ : ℝ≥0) (hδ : 0 < δ)
    (hLip : ∀ n, LipschitzWith Λ (f n)) (hD : (Λ : ℝ) * Dbridge ≤ δ)
    (hpaths : ∀ᶠ n in atTop, R.ControlsTwoPaths
      (fun u d => ι u * κ d) φ (fun g q => act g q) height cell E₁ E₂ η Apath Bpath δ n)
    (hpoint : ∀ n j x, x ∈ points n j → ∃ y ∈ good n,
      tile n y = j ∧ f n (center n * first n y * chart n (z₀ n)) = x)
    (hprofiles : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n)
        (anchorSuffix n (tile n y)) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b₂)‖ ≤ η n ∧
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n)
        (second n y) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hbridge : ∀ᶠ n in atTop, ∀ y ∈ good n,
      dist (center n * second n y * chart n (z₀ n))
        (center n * first n y * chart n (z₀ n)) ≤ Dbridge * scale n)
    (hprobePaths : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ∃ (path₁ : Path (1 : G) (basedImage (f n)
          (center n * base n * chart n (z₀ n))
          (center n * first n y * chart n (z₀ n))))
        (path₂ : Path (1 : G) (basedImage (f n)
          (center n * anchorSuffix n (tile n y) * chart n (z₀ n))
          (center n * second n y * chart n (z₀ n)))),
        PathMetricBound path₁ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))))
    (hcover : ∀ n, ∀ x ∈ source n, ∃ j, x ∈ points n j)
    (P₁ : ℝ) (ell : W →L[ℝ] ℝ) (lower tileLoss : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hbase : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (base n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖ ≤ η n)
    (hfallback : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (fallback n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hlower : HasSubexponentialLowerBoundSeq scale lower)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hHaar : ∀ (g : G) (E : Set Q), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μQ E)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  let anchor := fun n => occupiedTileAnchor (points n) (anchorSuffix n) (fallback n)
  have hanchor : ∀ᶠ n in atTop, ∀ j,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (anchor n j)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n := by
    have hwitness : ∀ n j x, x ∈ points n j → ∃ y ∈ good n, tile n y = j := by
      intro n j x hx
      obtain ⟨y, hy, hj, _⟩ := hpoint n j x hx
      exact ⟨y, hy, hj⟩
    exact occupiedTileAnchor_profile_bound good tiles tile points anchorSuffix fallback
      (fun n g => rescaledMapProfile (fun x => (height (f n x)).toAdd) (center n) g
        (Real.log (scale n)) (chart n) (z₀ n))
      (fun n => A (q (z₀ n)) + b₂) η hwitness hfallback
      (hprofiles.mono (fun _ hn y hy => (hn y hy).1))
  have hgeometry := probe_image_two_path_geometry good tiles tile points height f
    center base anchorSuffix first second scale η chart q z₀ A b₂ E₁ E₂
    Apath Bpath δ Dbridge Λ hscale0 hη hδ hLip hD hpoint hprofiles hbridge hprobePaths
  apply R.offset_nonpos_of_two_paths π hπ μQ μI μ ν φ ι κ hc hφ actionQ act hact
    scale hscale hscale0 P₂ hμ source tiles points height f center base anchor
    chart q z₀ A b₁ b₂ cell hcell hcell0 hcelltop hsmall hsep hsurj
    η δ Apath Bpath E₁ E₂ hpaths _ hcover P₁ ell lower tileLoss
    hη hbase hanchor hlower htileLoss htile0 hHaar hsource htiles
  filter_upwards [hgeometry] with n hn
  intro j x hx
  obtain ⟨secondPoint, p₁, p₂, hm₁, hm₂, hh₁, hh₂, hs, hd⟩ := hn j x hx
  have ha : anchor n j = anchorSuffix n j := occupiedTileAnchor_eq _ _ _ hx
  have he : (f n (center n * anchor n j * chart n (z₀ n)))⁻¹ * secondPoint =
      (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * secondPoint := by rw [ha]
  refine ⟨secondPoint, p₁, p₂.cast rfl he, hm₁, hm₂.cast rfl he, hh₁, hh₂, ?_, hd⟩
  rw [he]
  exact hs

end PolycyclicRecognition

end

end OAI
