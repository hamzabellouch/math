import OAI.Analysis.LipschitzHilbert.Phase.AngularBinOverlap
import OAI.Analysis.LipschitzHilbert.Fourier.LineCounting

namespace OAI

/-! The line-counting theorem instantiated with the actual angular bins. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.AngularBins

/-- A single jointly measurable count for every reference line and every
angular bin. Its definition is independent of the separated list later
tested against it. The overlap constant is the proved `10*(1+c)`. -/
theorem angular_line_counting {X : Type*} [MeasurableSpace X]
    (s : ℝ) {M : ℕ} (hM : 0 < M) {c : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M)
    (u : X × ℝ → ℝ) (hu : Measurable u)
    {H θ : ℝ} (hH : 0 < H) (hθ : 0 < θ) :
    ∃ N : X × ℝ → ℝ≥0∞, Measurable N ∧
      (∀ (p : X × ℝ) (bins : Finset (Bin M)),
        (∀ b ∈ bins, ∃ a d : ℝ, a < d ∧ d - a ≤ H ∧ p.2 ∈ Icc a d ∧
          θ * (d - a) ≤ ∫ x in Icc a d, binFunction s c u b (p.1, x)) →
        (bins.card : ℝ≥0∞) ≤ N p) ∧
      ∀ (p : X) (a b : ℝ), a ≤ b → ∀ lambda : ℝ, 0 ≤ lambda →
        volume.real ({x | ENNReal.ofReal lambda < N (p, x)} ∩ Icc a b) ≤
          96 * (b - a + H) * Real.exp (-θ * lambda / (240 * (1 + c))) := by
  obtain ⟨N, hN, hpopular, htail⟩ := line_counting
    (fun b => binFunction s c u b)
    (fun b => measurable_binFunction s c u hu b)
    (fun b p => binFunction_bounds s c u b p)
    (show 0 < 10 * (1 + c) by positivity) hH hθ
    (fun t p => finite_binFunction_sum s hM hc hcM u t p)
  refine ⟨N, hN, hpopular, ?_⟩
  intro p a b hab lambda hlambda
  simpa only [show (24 : ℝ) * (10 * (1 + c)) = 240 * (1 + c) by ring] using
    htail p a b hab lambda hlambda

end LipschitzHilbert.AngularBins

end

end OAI
