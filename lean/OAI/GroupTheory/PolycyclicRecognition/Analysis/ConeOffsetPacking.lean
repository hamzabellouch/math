import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceSectionTileVolume
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AnchoredTilePacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeOffsetExponent

namespace OAI

/-! # The offset inequality from actual lifted cells and section volumes

The first-sheet quotient restriction and the second-sheet ideal restriction
bound all lifted cells. The tile count and source count then cancel their
template exponents, leaving the sign of the quotient trace.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise BigOperators

/-- The covering need not partition the endpoints, and empty tiles are
allowed. A common real cardinal bound still sums over the finite cover. -/
theorem card_le_real_finite_cover {G : Type*} {k : ℕ}
    (s : Finset G) (t : Fin k → Finset G)
    (hcover : ∀ x ∈ s, ∃ j, x ∈ t j) {B : ℝ}
    (hbound : ∀ j, ((t j).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ (k : ℝ) * B := by
  classical
  have hsub : s ⊆ Finset.univ.biUnion t := by
    intro x hx
    obtain ⟨j, hj⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩
  calc
    (s.card : ℝ) ≤ ((Finset.univ.biUnion t).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ j : Fin k, ((t j).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin k, B := Finset.sum_le_sum (fun j _ => hbound j)
    _ = (k : ℝ) * B := by simp

variable {N D G Q : Type*} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup Q] [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [MeasurableSpace D]
  [BorelSpace N] [BorelSpace Q] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]

/-- This is the geometric counting endgame: restrictions on actual
quotient and ideal coordinates imply the offset trace inequality.
No point-count estimate or offset-sign assertion is assumed. -/
theorem cone_offset_nonpos_of_lifted_cells
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
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (source : ℕ → Finset G) (tiles : ℕ → ℕ)
    (points : ∀ n, Fin (tiles n) → Finset G)
    (anchor : ∀ n, Fin (tiles n) → G)
    (p : ∀ n, Fin (tiles n) → G → N × D)
    (E : ∀ n, Fin (tiles n) → Set N) (B : ℕ → Set D)
    (T : ℕ → Set Q) (I : ℕ → Set π.ker)
    (q₀ : ∀ n, Fin (tiles n) → Q) (α : ∀ n, Fin (tiles n) → Q ≃ Q)
    (cell : Set (N × D)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    {ρ : ℝ} (hsmall : ∀ z ∈ cell, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hB : ∀ n, ν (B n) ≠ ⊤)
    (hp : ∀ n j, ∀ x ∈ points n j,
      ι (p n j x).1 * κ (p n j x).2 = (anchor n j)⁻¹ * x)
    (hsep : ∀ n j, ∀ x ∈ points n j, ∀ y ∈ points n j,
      x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      factorTranslate φ (p n j x) '' cell ⊆ E n j ×ˢ B n)
    (hcover : ∀ n, ∀ x ∈ source n, ∃ j, x ∈ points n j)
    (P₁ P₂ ell : ℝ) (ε U V Dvol lower tileLoss : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hU : HasSubexponentialUpperBoundSeq scale U)
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hDvol : HasSubexponentialUpperBoundSeq scale Dvol)
    (hlower : HasSubexponentialLowerBoundSeq scale lower)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (hU0 : ∀ n, 0 ≤ U n) (hV0 : ∀ n, 0 ≤ V n) (hDvol0 : ∀ n, 0 ≤ Dvol n)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hT : ∀ n, μQ (T n) ≠ ⊤) (hI : ∀ n, μI (I n) ≠ ⊤)
    (hα : ∀ n j, μQ (α n j '' T n) ≤
      ENNReal.ofReal (Real.exp (-ell * scale n + ε n * scale n)) * μQ (T n))
    (hTvol : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIvol : ∀ n, (μI (I n)).toReal ≤ V n * Real.exp (P₂ * scale n))
    (hcoordinates : ∀ n j, ∀ x ∈ E n j,
      π x ∈ q₀ n j • (α n j '' T n) ∧ quotientSectionResidual π σ hs x ∈ I n)
    (hDBound : ∀ n, (ν (B n)).toReal ≤ Dvol n)
    (hsource : ∀ᶠ n in atTop,
      lower n * Real.exp (scale n * P₁) ≤ (source n).card)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) : ell ≤ 0 := by
  obtain ⟨A, hA, hA0, hAv⟩ := sequence_section_tile_family_volume_exponent
    π hπ σ hs μQ μI scale hscale E T I q₀ α P₂ ell ε U V hε
    hU hV hU0 hV0 hT hI hα hTvol hIvol hcoordinates
  have hEfinite : ∀ n j, μ (E n j) ≠ ⊤ := by
    intro n j
    simpa only [hμ] using (hAv n j).1
  have hEvol : ∀ n j, (μ (E n j)).toReal ≤ A n * Real.exp ((P₂ - ell) * scale n) := by
    intro n j
    simpa only [hμ] using (hAv n j).2
  obtain ⟨loss, hloss, hloss0, hcount⟩ := sequence_anchored_tile_separated_count φ ι κ hc μ ν hφ
    scale hscale tiles points anchor p E B cell hcell hcell0 hcelltop hEfinite hB
    hp hsmall hsep hthick A Dvol hA hDvol hA0 hDvol0 P₂ ell hEvol hDBound
  have hupper := htileLoss.mul hloss htile0
  have hexponent : P₁ ≤ P₁ - ell := exponent_le_of_sequence_subexponential_bounds
    hscale hlower hupper (by
      filter_upwards [hsource, htiles, hcount] with n hsrc htilesn hcountn
      have hsum := card_le_real_finite_cover (source n) (points n) (hcover n) hcountn
      calc
        lower n * Real.exp (scale n * P₁) ≤ ((source n).card : ℝ) := hsrc
        _ ≤ (tiles n : ℝ) * (loss n * Real.exp ((P₂ - ell) * scale n)) := hsum
        _ ≤ (tileLoss n * Real.exp (scale n * (P₁ - P₂))) *
            (loss n * Real.exp ((P₂ - ell) * scale n)) :=
          mul_le_mul_of_nonneg_right htilesn
            (mul_nonneg (hloss0 n) (Real.exp_pos _).le)
        _ = (tileLoss n * loss n) * Real.exp (scale n * (P₁ - ell)) := by
          rw [mul_mul_mul_comm, ← Real.exp_add]
          congr 2
          ring)
  linarith

end PolycyclicRecognition

end

end OAI
