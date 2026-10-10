import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPenaltyFamily
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicSeparable

namespace OAI

/-! Strong convergence of the compact observations for weakly varying loads. -/

open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace DefocusingNLS
namespace SpectralPenaltyFamily
variable {R l : ℝ}

theorem observation_tendsto (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (F : ℕ → StrongDual ℝ (SpectralHarmonicPair ell R))
    (F₀ : StrongDual ℝ (SpectralHarmonicPair ell R)) (M : ℝ) (hF : ∀ n, ‖F n‖ ≤ M)
    (hF0 : ∀ v, Tendsto (fun n => F n v) atTop (𝓝 (F₀ v))) :
    Tendsto (fun n => spectralHarmonicObservation ell R (hl.trans hlR)
      (s.inverse ell n (F n))) atTop
      (𝓝 (spectralHarmonicObservation ell R (hl.trans hlR) (s.limitInverse ell F₀))) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : TopologicalSpace.SeparableSpace (SpectralHarmonicPair ell R) :=
    spectralHarmonicPair_separable ell R
  apply tendsto_of_subseq_tendsto
  intro ns hns
  let u := fun n => s.inverse ell (ns n) (F (ns n))
  have hb (n : ℕ) : ‖u n‖ ≤ M/s.lower :=
    (s.inverse_norm ell (ns n) (F (ns n))).trans
      (div_le_div_of_nonneg_right (hF (ns n)) s.lower_pos.le)
  obtain ⟨u₀,_,φ,hφ,hu⟩ := spectralRealHilbert_weak_subsequence u (M/s.lower) hb
  have hc := (s.reindex (ns ∘ φ) (hns.comp hφ.tendsto_atTop)).weak_limit_unique ell hl hlR
    (F ∘ ns ∘ φ) F₀ M (fun n => hF (ns (φ n)))
    (fun v => (hF0 v).comp (hns.comp hφ.tendsto_atTop)) u₀ hu
  refine ⟨φ,?_⟩
  have ho := spectralHarmonicObservation_weakSequence ell R (hl.trans hlR)
    (u ∘ φ) u₀ (M/s.lower) (fun n => hb (φ n)) hu
  change u₀=s.limitInverse ell F₀ at hc
  rw [hc] at ho
  exact ho

end SpectralPenaltyFamily
end DefocusingNLS

end OAI
