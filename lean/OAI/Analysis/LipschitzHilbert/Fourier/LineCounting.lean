import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineRootCount
import OAI.Analysis.LipschitzHilbert.Estimates.RootTailGluing

namespace OAI

/-! The measurable line-counting lemma used for simultaneous separated directions. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

open DyadicLineGrid

/-- A single jointly measurable count dominates every finite collection of
popular bins, and its tail is exponentially small on every bounded interval.
Only finite partial sums of the countable bin family are needed as data. -/
theorem line_counting {X B : Type*} [MeasurableSpace X] [Countable B]
    (f : B → X × ℝ → ℝ) (hf : ∀ b, Measurable (f b))
    (hbound : ∀ b p, 0 ≤ f b p ∧ f b p ≤ 1)
    {C H θ : ℝ} (hC : 0 < C) (hH : 0 < H) (hθ : 0 < θ)
    (hsum : ∀ s : Finset B, ∀ p, (∑ b ∈ s, f b p) ≤ C) :
    ∃ N : X × ℝ → ℝ≥0∞, Measurable N ∧
      (∀ (p : X × ℝ) (bins : Finset B), (∀ b ∈ bins, ∃ a c : ℝ, a < c ∧ c - a ≤ H ∧ p.2 ∈ Icc a c ∧
        θ * (c - a) ≤ ∫ x in Icc a c, f b (p.1, x)) → (bins.card : ℝ≥0∞) ≤ N p) ∧
      ∀ (p : X) (a b : ℝ), a ≤ b → ∀ lambda : ℝ, 0 ≤ lambda →
        volume.real ({x | ENNReal.ofReal lambda < N (p, x)} ∩ Icc a b) ≤
          96 * (b - a + H) * Real.exp (-θ * lambda / (24 * C)) := by
  obtain ⟨top, htop0, htop1⟩ := exists_root_scale hH
  refine ⟨selectedCount f top (θ / 6), measurable_selectedCount f hf top (θ / 6), ?_, ?_⟩
  · intro p bins hb
    exact popular_bins_card_le_selectedCount f hf hbound hθ.le htop0 p bins hb
  · intro p a b hab lambda hlambda
    have hβ : 0 < θ / 6 := by positivity
    let fl : B → ℝ → ℝ := fun bin x => f bin (p, x)
    have hfl : ∀ bin, Measurable (fl bin) := fun bin =>
      (hf bin).comp (measurable_const.prodMk measurable_id)
    have hg := two_dyadic_root_exponential_tail_scale (A := C / (θ / 6)) (H := H) top hab
      (div_pos hC hβ) hlambda htop1.le
      (fun q => gridCount fl q top (θ / 6)) (by
        intro q _ j _ t ht
        have h := gridCount_root_tail fl q top hβ hC hfl
          (fun bin x => hbound bin (p, x)) (fun s x => hsum s (p, x)) j ht
        simpa only [cell_length] using h)
    have hexp : -lambda / (4 * (C / (θ / 6))) = -θ * lambda / (24 * C) := by
      field_simp [hC.ne', hθ.ne']
      ring
    rw [hexp] at hg
    convert hg using 2
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, selectedCount_eq_gridCounts, fl]

end LipschitzHilbert

end

end OAI
