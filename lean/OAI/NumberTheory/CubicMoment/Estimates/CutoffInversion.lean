import OAI.NumberTheory.CubicMoment.Estimates.FourierSmoothing

namespace OAI

/-!
# Integral representation of the interval cutoff

The same concrete smoothing used for the proved endpoint error is the
inverse Fourier integral of its compactly supported frequency multiplier.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform Convolution

namespace CubicFirstMoment

private theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) hf

theorem integrable_concrete_intervalSmoothing {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    Integrable (intervalSmoothing (scaledKernel truncationKernel T) a b) := by
  rw [intervalSmoothing_eq_convolution]
  exact (integrable_scaledKernel truncationKernel.integrable hT).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_intervalStep a b)

theorem continuous_concrete_intervalSmoothing {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    Continuous (intervalSmoothing (scaledKernel truncationKernel T) a b) := by
  rw [intervalSmoothing_eq_convolution]
  have hbounded : BddAbove (Set.range (fun y => ‖scaledKernel truncationKernel T y‖)) := by
    refine ⟨T * SchwartzMap.seminorm ℝ 0 0 truncationKernel, ?_⟩
    rintro z ⟨y, rfl⟩
    simp only [scaledKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ truncationKernel _) hT.le
  have hcont : Continuous (scaledKernel truncationKernel T) := by
    unfold scaledKernel
    exact continuous_const.mul (truncationKernel.continuous.comp (continuous_const.mul continuous_id))
  exact hbounded.continuous_convolution_left_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) hcont (integrable_intervalStep a b)

theorem integrable_fourier_intervalSmoothing {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    Integrable (𝓕 (intervalSmoothing (scaledKernel truncationKernel T) a b)) := by
  have hc := continuous_fourier_of_integrable (integrable_concrete_intervalSmoothing hT a b)
  have hs : HasCompactSupport (𝓕 (intervalSmoothing (scaledKernel truncationKernel T) a b)) := by
    apply HasCompactSupport.intro' (K := Set.Icc (-T) T) isCompact_Icc isClosed_Icc
    intro ξ hξ
    apply fourier_intervalSmoothing_zero hT
    simp only [Set.mem_Icc, not_and_or, not_le] at hξ
    rcases hξ with hξ | hξ
    · linarith [neg_abs_le ξ]
    · exact hξ.le.trans (le_abs_self ξ)
  exact hc.integrable_of_hasCompactSupport hs

/-- The inverse integral has support only in the prescribed frequency band,
by `fourier_intervalSmoothing_zero`. -/
theorem concrete_interval_fourier_integral {T : ℝ} (hT : 0 < T) (a b s : ℝ) :
    intervalSmoothing (scaledKernel truncationKernel T) a b s =
      ∫ ξ : ℝ, Complex.exp ((2 * Real.pi * ξ * s : ℝ) * Complex.I) *
        (frequencyCutoff (ξ/T) * 𝓕 (fun x => (intervalStep a b x : ℂ)) ξ) := by
  have h := (integrable_concrete_intervalSmoothing hT a b).fourierInv_fourier_eq (v := s)
    (integrable_fourier_intervalSmoothing hT a b)
    (continuous_concrete_intervalSmoothing hT a b).continuousAt
  rw [Real.fourierInv_eq'] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [fourier_intervalSmoothing hT]
  change Complex.exp ((2 * Real.pi * inner ℝ ξ s : ℝ) * Complex.I) * _ = _
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
