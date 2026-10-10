import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeOffsetPacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeAnchorHaarBounds
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteProfileEnvelope

namespace OAI

/-! # The offset inequality with the actual affine-profile Haar multiplier -/

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

/-- The sign follows from the two measured affine profiles, the actual
anchor-frame Haar law, and the simultaneous coordinate restrictions on
thickened cells. No offset multiplier estimate is an assumption. -/
theorem cone_offset_nonpos_of_profile_cells
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
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (source : ℕ → Finset G) (tiles : ℕ → ℕ)
    (points : ∀ n, Fin (tiles n) → Finset G)
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (center base : ℕ → G) (anchorSuffix : ∀ n, Fin (tiles n) → G)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b₁ b₂ : W)
    (p : ∀ n, Fin (tiles n) → G → N × D)
    (E : ∀ n, Fin (tiles n) → Set N) (B : ℕ → Set D)
    (T : ℕ → Set Q) (I : ℕ → Set π.ker)
    (q₀ : ∀ n, Fin (tiles n) → Q) (α : ∀ n, Fin (tiles n) → Q ≃ Q)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hB : ∀ n, ν (B n) ≠ ⊤)
    (hp : ∀ n j, ∀ x ∈ points n j,
      ι (p n j x).1 * κ (p n j x).2 = (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * x)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      factorTranslate φ (p n j x) '' cell ⊆ E n j ×ˢ B n)
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
    (hα : ∀ n j, μQ (α n j '' T n) =
      ENNReal.ofReal (Real.exp (ell
        (height ((f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ *
          f n (center n * base n * chart n (z₀ n)))).toAdd)) * μQ (T n))
    (hTvol : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIvol : ∀ n, (μI (I n)).toReal ≤ V n * Real.exp (P₂ * scale n))
    (hcoordinates : ∀ n j, ∀ x ∈ E n j,
      π x ∈ q₀ n j • (α n j '' T n) ∧ quotientSectionResidual π σ hs x ∈ I n)
    (hDBound : ∀ n, (ν (B n)).toReal ≤ Dvol n)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  obtain ⟨η', hη', _, hbase', hanchor'⟩ := exists_finite_profile_envelope
    (fun n => ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n) (base n)
      (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₁)‖₊)
    (fun n j => ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n)
      (anchorSuffix n j) (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b₂)‖₊)
    η hη hbase hanchor
  let ε := fun n => ‖ell‖ * (η' n + η' n)
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, add_zero, mul_zero] using (hη'.add hη').const_mul ‖ell‖
  have hαbound (n j) : μQ (α n j '' T n) ≤ ENNReal.ofReal
      (Real.exp (-ell (b₂ - b₁) * scale n + ε n * scale n)) * μQ (T n) := by
    have hb := anchor_haar_bound_of_affine_profiles height (f n) (center n) (base n)
      (anchorSuffix n j) (Real.log (scale n)) (chart n) q A b₁ b₂ (z₀ n)
      (hbase' n) (hanchor' n j) ell μQ (α n j) (T n) (hα n j)
    simpa only [Real.exp_log (hscale0 n)] using hb
  exact cone_offset_nonpos_of_lifted_cells π hπ σ hs μQ μI μ ν hμ φ ι κ hc hφ
    scale hscale source tiles points
    (fun n j => f n (center n * anchorSuffix n j * chart n (z₀ n))) p E B T I q₀ α
    cell hcell hcell0 hcelltop hsmall hB hp hsep hthick hcover P₁ P₂ (ell (b₂ - b₁))
    ε U V Dvol lower tileLoss hε hU hV hDvol hlower htileLoss hU0 hV0 hDvol0
    htile0 hT hI hαbound hTvol hIvol hcoordinates hDBound hsource htiles

end PolycyclicRecognition

end

end OAI
