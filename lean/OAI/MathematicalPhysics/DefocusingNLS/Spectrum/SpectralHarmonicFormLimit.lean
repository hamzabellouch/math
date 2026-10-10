import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicWeightDifference

namespace OAI

/-! Passing to the limit in the base form with weak arguments and varying mass weights. -/

open MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralHarmonicPairForm_difference_bound (ell : ℕ) (R : ℝ)
    (w z : SpectralHarmonicWeight R) (δ : ℝ) (hδ : 0 ≤ δ)
    (hr : ∀ᵐ r ∂radialPressureMeasure R, ‖w.density r-z.density r‖ ≤ δ)
    (ha : ∀ᵐ r ∂spectralAngularMeasure R, ‖w.density r-z.density r‖ ≤ δ)
    (u v : SpectralHarmonicPair ell R) :
    ‖spectralHarmonicPairForm ell R w u v-spectralHarmonicPairForm ell R z u v‖ ≤ 6*δ*‖u‖*‖v‖ := by
  have hf := spectralHarmonicForm_difference_bound ell R w z δ hδ hr ha u.fst v.fst
  have hs := spectralHarmonicForm_difference_bound ell R w z δ hδ hr ha u.snd v.snd
  have hfb : 3*δ*‖u.fst‖*‖v.fst‖ ≤ 3*δ*‖u‖*‖v‖ := by
    gcongr
    · exact WithLp.norm_fst_le _ u
    · exact WithLp.norm_fst_le _ v
  have hsb : 3*δ*‖u.snd‖*‖v.snd‖ ≤ 3*δ*‖u‖*‖v‖ := by
    gcongr
    · exact WithLp.norm_snd_le _ u
    · exact WithLp.norm_snd_le _ v
  change ‖(spectralHarmonicForm ell R w u.fst v.fst+spectralHarmonicForm ell R w u.snd v.snd)-
      (spectralHarmonicForm ell R z u.fst v.fst+spectralHarmonicForm ell R z u.snd v.snd)‖ ≤ _
  rw [add_sub_add_comm]
  exact (norm_add_le _ _).trans (by linarith [hf.trans hfb,hs.trans hsb])

theorem spectralHarmonicPairForm_tendsto (ell : ℕ) (R : ℝ)
    (w : ℕ → SpectralHarmonicWeight R) (w₀ : SpectralHarmonicWeight R)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hr : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, ‖(w n).density r-w₀.density r‖ ≤ δ n)
    (ha : ∀ n, ∀ᵐ r ∂spectralAngularMeasure R, ‖(w n).density r-w₀.density r‖ ≤ δ n)
    (u : ℕ → SpectralHarmonicPair ell R) (u₀ : SpectralHarmonicPair ell R)
    (M : ℝ) (hM : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ L : SpectralHarmonicPair ell R →L[ℝ] ℝ,
      Tendsto (fun n => L (u n)) atTop (𝓝 (L u₀))) (v : SpectralHarmonicPair ell R) :
    Tendsto (fun n => spectralHarmonicPairForm ell R (w n) (u n) v) atTop
      (𝓝 (spectralHarmonicPairForm ell R w₀ u₀ v)) := by
  have he : Tendsto (fun n => spectralHarmonicPairForm ell R (w n) (u n) v-
      spectralHarmonicPairForm ell R w₀ (u n) v) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (show Tendsto (fun n => δ n*(6*M*‖v‖)) atTop (𝓝 0) from by
        simpa only [zero_mul] using hδ0.mul_const (6*M*‖v‖))
    calc
      _ ≤ 6*δ n*‖u n‖*‖v‖ := spectralHarmonicPairForm_difference_bound
        ell R (w n) w₀ (δ n) (hδ n) (hr n) (ha n) (u n) v
      _ ≤ 6*δ n*M*‖v‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hM n) (mul_nonneg (by norm_num) (hδ n)))
        (norm_nonneg v)
      _ = _ := by ring
  have hb := hweak ((spectralHarmonicPairForm ell R w₀).flip v)
  simpa only [ContinuousLinearMap.flip_apply,sub_add_cancel,zero_add] using he.add hb

end DefocusingNLS

end OAI
