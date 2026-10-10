import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeProbeRestrictionPacking
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

/-- Actual simultaneous probe restrictions and the quotient Haar character
force the affine offset sign. Factor lifts and tile frames are chosen here;
no independent compatibility premise about these choices is required. -/
theorem cone_offset_nonpos_of_measured_probe_lifts
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
    (hlifts : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      ∃ p : N × D,
        ι p.1 * κ p.2 = (f n (center n * anchorSuffix n j * chart n (z₀ n)))⁻¹ * x ∧
        ∀ z ∈ cell,
          act ((f n (center n * base n * chart n (z₀ n)))⁻¹ *
            (x * (ι z.1 * κ z.2))) 1 ∈ T n ∧
          quotientSectionResidual π σ hs (factorTranslate φ p z).1 ∈ I n ∧
          (factorTranslate φ p z).2 ∈ B n)
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
    (hHaar : ∀ (g : G) (E : Set Q), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μQ E)
    (hTvol : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIvol : ∀ n, (μI (I n)).toReal ≤ V n * Real.exp (P₂ * scale n))
    (hDBound : ∀ n, (ν (B n)).toReal ≤ Dvol n)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell (b₂ - b₁) ≤ 0 := by
  classical
  let start := fun n j => f n (center n * anchorSuffix n j * chart n (z₀ n))
  let origin := fun n => f n (center n * base n * chart n (z₀ n))
  let P := fun (n : ℕ) (j : Fin (tiles n)) (x : G) (p : N × D) => ∀ z ∈ cell,
    act ((origin n)⁻¹ * (x * (ι z.1 * κ z.2))) 1 ∈ T n ∧
    quotientSectionResidual π σ hs (factorTranslate φ p z).1 ∈ I n ∧
    (factorTranslate φ p z).2 ∈ B n
  obtain ⟨p, hp, hrestr⟩ := choose_eventual_probe_lifts
    (fun p : N × D => ι p.1 * κ p.2) hsurj
    (fun n j x => (start n j)⁻¹ * x) points P hlifts
  have hf : ∀ n j, ∃ frame : N × D,
      ι frame.1 * κ frame.2 = (start n j)⁻¹ * origin n :=
    fun n j => hsurj _
  choose frame hframe using hf
  have hfirst : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      act ((origin n)⁻¹ * (x * (ι z.1 * κ z.2))) 1 ∈ T n :=
    hrestr.mono (fun _ hn j x hx z hz => (hn j x hx z hz).1)
  have hideal : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      quotientSectionResidual π σ hs (factorTranslate φ (p n j x) z).1 ∈ I n :=
    hrestr.mono (fun _ hn j x hx z hz => (hn j x hx z hz).2.1)
  have hD : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j, ∀ z ∈ cell,
      (factorTranslate φ (p n j x) z).2 ∈ B n :=
    hrestr.mono (fun _ hn j x hx z hz => (hn j x hx z hz).2.2)
  have hα (n j) : μQ (actionQ (frame n j).2 '' T n) =
      ENNReal.ofReal (Real.exp (ell (height ((start n j)⁻¹ * origin n)).toAdd)) * μQ (T n) := by
    have he : act ((start n j)⁻¹ * origin n) '' T n =
        π (frame n j).1 • (actionQ (frame n j).2 '' T n) := by
      rw [← hframe n j, ← Set.image_smul, Set.image_image]
      congr 1
      funext q
      exact hact _ _ q
    have hh := hHaar ((start n j)⁻¹ * origin n) (T n)
    rw [he, measure_smul] at hh
    exact hh
  exact cone_offset_nonpos_of_probe_restrictions π hπ σ hs μQ μI μ ν hμ φ ι κ hc hφ
    actionQ act hact scale hscale hscale0 source tiles points height f center base anchorSuffix
    chart q z₀ A b₁ b₂ p frame (fun n j => (hframe n j).symm) B T I
    cell hcell hcell0 hcelltop hsmall hB (fun n j x _ => hp n j x) hsep
    hfirst hideal hD hcover P₁ P₂ ell η U V Dvol lower tileLoss hη hbase hanchor
    hU hV hDvol hlower htileLoss hU0 hV0 hDvol0 htile0 hT hI hα hTvol hIvol hDBound hsource htiles

end PolycyclicRecognition

end

end OAI
