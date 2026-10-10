import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorCompact
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDyadicPartition

namespace OAI

/-! # A concrete low/high frequency splitting on the Schwartz domain

The low cutoff equals one up to R and vanishes beyond 2R. Its complement
does not increase any homogeneous Fourier energy.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousFrequencyBump (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : E) where
  rIn := R
  rOut := 2 * R
  rIn_pos := hR
  rIn_lt_rOut := by linarith

noncomputable def homogeneousFrequencyCutoff (R : ℝ) (hR : 0 < R) : 𝓢(E, ℂ) :=
  ((homogeneousFrequencyBump R hR).hasCompactSupport.comp_left
    (g := Complex.ofReal) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (homogeneousFrequencyBump R hR).contDiff)

@[simp] theorem homogeneousFrequencyCutoff_apply (R : ℝ) (hR : 0 < R) (ξ : E) :
    homogeneousFrequencyCutoff R hR ξ = ((homogeneousFrequencyBump R hR) ξ : ℂ) := rfl

theorem homogeneousFrequencyCutoff_one (R : ℝ) (hR : 0 < R) (ξ : E) (hξ : ‖ξ‖ ≤ R) :
    homogeneousFrequencyCutoff R hR ξ = 1 := by
  rw [homogeneousFrequencyCutoff_apply, (homogeneousFrequencyBump R hR).one_of_mem_closedBall]
  · simp
  · simpa only [homogeneousFrequencyBump, Metric.mem_closedBall, dist_zero_right] using hξ

theorem homogeneousFrequencyCutoff_zero (R : ℝ) (hR : 0 < R) (ξ : E) (hξ : 2 * R ≤ ‖ξ‖) :
    homogeneousFrequencyCutoff R hR ξ = 0 := by
  rw [homogeneousFrequencyCutoff_apply, (homogeneousFrequencyBump R hR).zero_of_le_dist]
  · simp
  · simpa only [homogeneousFrequencyBump, dist_zero_right] using hξ

theorem homogeneousFrequencyCutoff_complement_norm (R : ℝ) (hR : 0 < R) (ξ : E) :
    ‖1 - homogeneousFrequencyCutoff R hR ξ‖ ≤ 1 := by
  let b := homogeneousFrequencyBump R hR
  have hb0 : 0 ≤ b ξ := b.nonneg
  have hb1 : b ξ ≤ 1 := b.le_one
  change ‖(1 : ℂ) - (b ξ : ℂ)‖ ≤ 1
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hb1)]
  linarith

noncomputable def homogeneousLowFrequencyPart (R : ℝ) (hR : 0 < R) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  Classical.choose (radianFourierKernel_surjective
    (SchwartzMap.smulLeftCLM ℂ (homogeneousFrequencyCutoff R hR) (radianFourierKernel f)))

theorem homogeneousLowFrequencyPart_fourier (R : ℝ) (hR : 0 < R) (f : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierKernel (homogeneousLowFrequencyPart R hR f) ξ =
      homogeneousFrequencyCutoff R hR ξ * radianFourierKernel f ξ := by
  have h := Classical.choose_spec (radianFourierKernel_surjective
    (SchwartzMap.smulLeftCLM ℂ (homogeneousFrequencyCutoff R hR) (radianFourierKernel f)))
  rw [show radianFourierKernel (homogeneousLowFrequencyPart R hR f) = _ from h]
  exact SchwartzMap.smulLeftCLM_apply_apply (homogeneousFrequencyCutoff R hR).hasTemperateGrowth _ _

noncomputable def homogeneousHighFrequencyPart (R : ℝ) (hR : 0 < R) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  f - homogeneousLowFrequencyPart R hR f

theorem homogeneousHighFrequencyPart_fourier (R : ℝ) (hR : 0 < R) (f : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierKernel (homogeneousHighFrequencyPart R hR f) ξ =
      (1 - homogeneousFrequencyCutoff R hR ξ) * radianFourierKernel f ξ := by
  change radianFourierCLM (f - homogeneousLowFrequencyPart R hR f) ξ = _
  rw [map_sub, sub_apply, radianFourierCLM_apply, radianFourierCLM_apply,
    homogeneousLowFrequencyPart_fourier]
  ring

theorem homogeneousHighFrequencyPart_zero (R : ℝ) (hR : 0 < R) (f : 𝓢(E, ℂ)) (ξ : E)
    (hξ : ‖ξ‖ < R) : radianFourierKernel (homogeneousHighFrequencyPart R hR f) ξ = 0 := by
  rw [homogeneousHighFrequencyPart_fourier, homogeneousFrequencyCutoff_one R hR ξ hξ.le,
    sub_self, zero_mul]

theorem homogeneousHighFrequencyPart_energy_le (s R : ℝ) (hs : 0 ≤ s) (hR : 0 < R)
    (f : 𝓢(E, ℂ)) :
    homogeneousFrequencyEnergy s (radianFourierKernel (homogeneousHighFrequencyPart R hR f)) ≤
      homogeneousFrequencyEnergy s (radianFourierKernel f) := by
  have hi : Integrable (fun ξ : E => ‖ξ‖ ^ (2 * s) * ‖radianFourierKernel f ξ‖ ^ 2) := by
    have h := homogeneousFourierMagnitude_sq_integrable s hs (radianFourierKernel f)
    convert h using 1
    funext ξ
    simp only [homogeneousFourierMagnitude, mul_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 2
    ring
  apply integral_mono_of_nonneg (ae_of_all _ (fun ξ => by positivity)) hi
  filter_upwards [] with ξ
  rw [homogeneousHighFrequencyPart_fourier, norm_mul, mul_pow]
  have hc := pow_le_pow_left₀ (norm_nonneg _)
    (homogeneousFrequencyCutoff_complement_norm R hR ξ) 2
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖radianFourierKernel f ξ‖))
    (Real.rpow_nonneg (norm_nonneg ξ) (2 * s))).trans_eq (by rw [one_pow, one_mul])

end DefocusingNLS

end OAI
