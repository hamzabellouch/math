import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasuredProbeOffset
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathConcatenation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeRestrictionComposition

namespace OAI

/-! # The offset inequality from measured, eventual probe lifts -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators

variable {N D G Q : Type*} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]


variable {W V Z : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Two actual controlled paths, a short image bridge and a small second
endpoint height suffice for the offset sign after measured probe packing. -/
theorem cone_offset_nonpos_of_measured_two_paths
    (π : N →* Q) (hπ : Continuous π) (σ : C(Q, N))
    (hs : ∀ q, π (σ q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) (μ : Measure N) (ν : Measure D)
    [SFinite μQ] [SFinite μI] [SFinite μ] [SFinite ν]
    [μQ.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (hμ : μ = Measure.map (quotientSectionHomeomorph π hπ σ hs).symm
      (μQ.prod μI))
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (actionQ : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * actionQ d q)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (source : ℕ → Finset G) (tiles : ℕ → ℕ)
    (points : ∀ n, Fin (tiles n) → Finset G)
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (center base : ℕ → G) (anchorSuffix : ∀ n, Fin (tiles n) → G)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b₁ b₂ : W)
    (B : ℕ → Set D)
    (T : ℕ → Set Q) (I : ℕ → Set π.ker)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hB : ∀ n, ν (B n) ≠ ⊤)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (η : ℕ → ℝ) (δ Apath Bpath : ℝ) (E₁ E₂ : Set W)
    (hpaths : ∀ᶠ n in atTop, ∀ (basePoint anchorPoint first second : G)
      (path₁ : Path (1 : G) (basePoint⁻¹ * first))
      (path₂ : Path (1 : G) (anchorPoint⁻¹ * second)),
      PathMetricBound path₁ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) →
      PathMetricBound path₂ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) →
      (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
        2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) →
      (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
        2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) →
      ‖(height (anchorPoint⁻¹ * second)).toAdd‖ ≤ δ * scale n →
      dist second first ≤ δ * scale n →
      ∃ p : N × D, ι p.1 * κ p.2 = anchorPoint⁻¹ * first ∧
        ∀ z ∈ cell,
          act (basePoint⁻¹ * (first * (ι z.1 * κ z.2))) 1 ∈ T n ∧
          quotientSectionResidual π σ hs (factorTranslate φ p z).1 ∈ I n ∧
          (factorTranslate φ p z).2 ∈ B n)
    (hgeometry : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      ∃ (second : G)
        (path₁ : Path (1 : G) ((f n (center n * base n * chart n (z₀ n)))⁻¹ * x))
        (path₂ : Path (1 : G) ((f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * second)),
        PathMetricBound path₁ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (Apath * scale n) (Bpath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + Apath * (1 + Real.log (2 + scale n))) ∧
        ‖(height ((f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * second)).toAdd‖ ≤
          δ * scale n ∧ dist second x ≤ δ * scale n)
    (hcover : ∀ n, ∀ x ∈ source n, ∃ j, x ∈ points n j)
    (P₁ P₂ : ℝ) (ell : W →L[ℝ] ℝ) (U V Dvol lower tileLoss : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hbase : ∀ᶠ n in atTop,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (base n)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖ ≤ η n)
    (hanchor : ∀ᶠ n in atTop, ∀ j,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (anchorSuffix n j)
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖ ≤ η n)
    (hU : HasSubexponentialUpperBoundSeq scale U)
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hDvol : HasSubexponentialUpperBoundSeq scale Dvol)
    (hlower : HasSubexponentialLowerBoundSeq scale lower)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (hU0 : ∀ n, 0 ≤ U n) (hV0 : ∀ n, 0 ≤ V n) (hDvol0 : ∀ n, 0 ≤ Dvol n)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hT : ∀ n, μQ (T n) ≠ ⊤) (hI : ∀ n, μI (I n) ≠ ⊤)
    (hHaar : ∀ (g : G) (E : Set Q), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μQ E)
    (hTvol : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIvol : ∀ n, (μI (I n)).toReal ≤ V n * Real.exp (P₂ * scale n))
    (hDBound : ∀ n, (ν (B n)).toReal ≤ Dvol n)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  have hlifts : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      ∃ p : N × D,
        ι p.1 * κ p.2 = (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * x ∧
        ∀ z ∈ cell,
          act ((f n (center n * base n * chart n (z₀ n)))⁻¹ *
            (x * (ι z.1 * κ z.2))) 1 ∈ T n ∧
          quotientSectionResidual π σ hs (factorTranslate φ p z).1 ∈ I n ∧
          (factorTranslate φ p z).2 ∈ B n := by
    filter_upwards [hpaths, hgeometry] with n hn hg
    intro j x hx
    obtain ⟨second, path₁, path₂, hm₁, hm₂, hh₁, hh₂, hs, hd⟩ := hg j x hx
    exact hn _ _ x second path₁ path₂ hm₁ hm₂ hh₁ hh₂ hs hd
  exact cone_offset_nonpos_of_measured_probe_lifts π hπ σ hs μQ μI μ ν hμ φ ι κ hc hφ
    actionQ act hact scale hscale hscale0 source tiles points height f center base anchorSuffix
    chart q z₀ A b₁ b₂ B T I cell hcell hcell0 hcelltop hsmall hB hsep hsurj hlifts
    hcover P₁ P₂ ell η U V Dvol lower tileLoss hη hbase hanchor
    hU hV hDvol hlower htileLoss hU0 hV0 hDvol0 htile0 hT hI hHaar hTvol hIvol hDBound hsource htiles

end PolycyclicRecognition

end

end OAI
