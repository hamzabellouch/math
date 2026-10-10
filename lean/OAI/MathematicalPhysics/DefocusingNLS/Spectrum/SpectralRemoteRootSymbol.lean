import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteRootBlocks
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolComposition
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! Uniform logarithmic jets of the actual leading roots. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_root_smooth (h j : ℝ) :
    ContDiffOn ℝ ∞ (homogeneousSpectralLocalizationRemoteRoot h j) (Iio (1/16)) := by
  have hs : ContDiffOn ℝ ∞ (fun c : ℝ => Real.sqrt (1/16-c)) (Iio (1/16)) :=
    (contDiffOn_const.sub contDiffOn_id).sqrt (fun c hc => ne_of_gt (sub_pos.mpr hc))
  have hr : ContDiffOn ℝ ∞ (fun c : ℝ => ((-1/4+j*Real.sqrt (1/16-c) : ℝ) : ℂ))
      (Iio (1/16)) := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_const.add (contDiffOn_const.mul hs))
  exact contDiffOn_const.mul hr

theorem spectralRemote_root_continuous (h j : ℝ) :
    Continuous (homogeneousSpectralLocalizationRemoteRoot h j) := by
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_const.add (continuous_const.mul
      (continuous_const.sub continuous_id).sqrt)))

theorem spectralRemote_root_uniform_symbol
    {L : ℕ → ℝ} {c : ℕ → ℝ → ℝ} (h j : ℝ)
    (hc : HasUniformLogJetBound L 0 c)
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), |c n t| ≤ 1/32) :
    HasUniformLogJetBound L 0 (fun n t => homogeneousSpectralLocalizationRemoteRoot h j (c n t)) := by
  apply spectralRemote_uniform_compact_comp isOpen_Iio (isCompact_Icc : IsCompact (Icc (-1/32 : ℝ) (1/32)))
    (fun _ hx => lt_of_le_of_lt hx.2 (by norm_num)) (spectralRemote_root_smooth h j) hc
  exact hsmall.mono (fun _ hn t ht => by simpa only [mem_Icc,neg_div] using abs_le.mp (hn t ht))

end DefocusingNLS

end OAI
