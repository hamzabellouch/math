import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialSmoothCompact
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Extend smooth-core volume compactness to the completed radial H¹ domain. -/

open Filter Topology Set
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralRadialVolume_weakNull (R : ℝ) (hR : 0 < R)
    (u : ℕ → SpectralRadialEnergy R) (M : ℝ) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ L : SpectralRadialEnergy R →L[ℂ] ℂ,
      Tendsto (fun n => L (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => spectralRadialValue R (u n)) atTop (𝓝 0) := by
  have happrox (n : ℕ) : ∃ f : 𝓢(ℝ,ℂ),
      dist (u n) (spectralRadialSmoothEmbedding R f) < 1/((n : ℝ)+1) :=
    (spectralRadialSmoothEmbedding_dense R).exists_dist_lt (u n) (by positivity)
  choose f hf using happrox
  have herr : Tendsto (fun n => spectralRadialSmoothEmbedding R (f n)-u n) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [dist_eq_norm,norm_sub_rev] using (hf n).le
  have hbound (n : ℕ) : ‖spectralRadialSmoothEmbedding R (f n)‖ ≤ M+1 := by
    have hsmall : 1/((n : ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have htri := norm_le_norm_sub_add (spectralRadialSmoothEmbedding R (f n)) (u n)
    have he : ‖spectralRadialSmoothEmbedding R (f n)-u n‖ ≤ 1/((n : ℝ)+1) := by
      simpa only [dist_eq_norm,norm_sub_rev] using (hf n).le
    linarith [hu n]
  have hweakf (L : SpectralRadialEnergy R →L[ℂ] ℂ) :
      Tendsto (fun n => L (spectralRadialSmoothEmbedding R (f n))) atTop (𝓝 0) := by
    have he := L.continuous.continuousAt.tendsto.comp herr
    have h := he.add (hweak L)
    simpa only [Function.comp_def,map_sub,map_zero,sub_add_cancel,zero_add] using h
  have hfvol := spectralRadialSmooth_weakNull_volume R hR f (M+1) hbound hweakf
  have hevol := (spectralRadialValue R).continuous.continuousAt.tendsto.comp herr
  have h := hfvol.sub hevol
  simpa only [Function.comp_def,map_sub,map_zero,spectralRadialSmoothEmbedding_value,
    sub_sub_cancel,sub_self] using h

end DefocusingNLS

end OAI
