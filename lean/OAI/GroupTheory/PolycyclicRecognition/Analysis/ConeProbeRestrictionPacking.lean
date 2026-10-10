import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeProfileOffsetPacking
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeQuotientRestriction

namespace OAI

/-! # Simultaneous two-frame restrictions for the offset packing -/

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

/-- A quotient restriction in the first sheet and an ideal restriction in
the second sheet combine for the same thickened endpoints. The containing
product regions and translated quotient coordinates are constructed here. -/
theorem cone_offset_nonpos_of_probe_restrictions
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
    (p : ∀ n, Fin (tiles n) → G → N × D)
    (frame : ∀ n, Fin (tiles n) → N × D)
    (hframe : ∀ n j,
      (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ *
        f n (center n * base n * chart n (z₀ n)) =
          ι (frame n j).1 * κ (frame n j).2)
    (B : ℕ → Set D)
    (T : ℕ → Set Q) (I : ℕ → Set π.ker)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hB : ∀ n, ν (B n) ≠ ⊤)
    (hp : ∀ n j, ∀ x ∈ points n j,
      ι (p n j x).1 * κ (p n j x).2 = (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * x)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hfirst : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      act ((f n (center n * base n * chart n (z₀ n)))⁻¹ *
        (x * (ι z.1 * κ z.2))) 1 ∈ T n)
    (hideal : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      quotientSectionResidual π σ hs (factorTranslate φ (p n j x) z).1 ∈ I n)
    (hD : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      (factorTranslate φ (p n j x) z).2 ∈ B n)
    (hcover : ∀ n, ∀ x ∈ source n, ∃ j, x ∈ points n j)
    (P₁ P₂ : ℝ) (ell : W →L[ℝ] ℝ) (η U V Dvol lower tileLoss : ℕ → ℝ)
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
    (hα : ∀ n j, μQ (actionQ (frame n j).2 '' T n) =
      ENNReal.ofReal (Real.exp (ell
        (height ((f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ *
          f n (center n * base n * chart n (z₀ n)))).toAdd)) * μQ (T n))
    (hTvol : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIvol : ∀ n, (μI (I n)).toReal ≤ V n * Real.exp (P₂ * scale n))
    (hDBound : ∀ n, (ν (B n)).toReal ≤ Dvol n)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  let E := fun n j => {u : N | π u ∈ π (frame n j).1 • (actionQ (frame n j).2 '' T n) ∧
    quotientSectionResidual π σ hs u ∈ I n}
  have hthick : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      factorTranslate φ (p n j x) '' cell ⊆ E n j ×ˢ B n := by
    filter_upwards [hfirst, hideal, hD] with n hnFirst hnIdeal hnD
    intro j x hx
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟨?_, hnIdeal j x hx z hz⟩, hnD j x hx z hz⟩
    have hpoint : (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ *
        (x * (ι z.1 * κ z.2)) =
          ι (factorTranslate φ (p n j x) z).1 * κ (factorTranslate φ (p n j x) z).2 := by
      rw [← mul_assoc, ← hp n j x hx]
      exact (factorTranslate_projection φ ι κ hc (p n j x) z).symm
    exact quotient_restriction_in_anchor_frame ι κ π actionQ act hact
      (f n (center n * base n * chart n (z₀ n)))
      (f n (center n * anchorSuffix n j * chart n (z₀ n)))
      (x * (ι z.1 * κ z.2)) (factorTranslate φ (p n j x) z).1 (frame n j).1
      (factorTranslate φ (p n j x) z).2 (frame n j).2 hpoint (hframe n j) (T n)
      (hnFirst j x hx z hz)
  exact cone_offset_nonpos_of_profile_cells π hπ σ hs μQ μI μ ν hμ φ ι κ hc hφ
    scale hscale hscale0 source tiles points height f center base anchorSuffix chart q z₀ A b₁ b₂
    p E B T I (fun n j => π (frame n j).1) (fun n j => (actionQ (frame n j).2).toEquiv)
    cell hcell hcell0 hcelltop hsmall hB hp hsep hthick hcover
    P₁ P₂ ell η U V Dvol lower tileLoss hη hbase hanchor hU hV hDvol hlower htileLoss
    hU0 hV0 hDvol0 htile0 hT hI hα hTvol hIvol (fun _ _ _ hx => hx)
    hDBound hsource htiles

end PolycyclicRecognition

end

end OAI
