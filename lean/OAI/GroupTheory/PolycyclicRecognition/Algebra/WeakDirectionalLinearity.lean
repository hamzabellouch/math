import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoordinateFlowDerivative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace OAI

/-! # Linearity of locally bounded weak directional derivatives -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped ContDiff

theorem integrable_test_smul_of_locallyIntegrableOn
    {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {μ : Measure E} {Ω : Set E} {f : E → W} (hf : LocallyIntegrableOn f Ω μ)
    {φ : E → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Ω) :
    Integrable (fun x => φ x • f x) μ := by
  have hi := (hf.integrableOn_compact_subset hsφ hcφ).continuousOn_smul hφ.continuousOn hcφ
  apply (integrableOn_iff_integrable_of_support_subset (s := tsupport φ) ?_).mp hi
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  simp [hz] at hx

theorem ae_add_of_weak_directional_derivatives
    {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (Ω : Set E) (hΩ : IsOpen Ω) (q : V → E → W)
    (hq : ∀ v, LocallyIntegrableOn (q v) Ω μ)
    (Y : E → V →L[ℝ] E) (hY : Continuous Y) (f : E → W) (hf : Continuous f)
    (hweak : ∀ v (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ g, φ g • q v g ∂μ) = -(∫ g, fderiv ℝ φ g (Y g v) • f g ∂μ))
    (v w : V) : ∀ᵐ g ∂μ, g ∈ Ω → q (v + w) g = q v g + q w g := by
  have hr (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (u : V) :
      Integrable (fun g => fderiv ℝ φ g (Y g u) • f g) μ := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((hφ.continuous_fderiv (by simp)).clm_apply (hY.clm_apply continuous_const)).smul hf
    · apply (hcφ.fderiv ℝ).mono'
      intro g hg
      apply subset_tsupport (fderiv ℝ φ)
      change fderiv ℝ φ g ≠ 0
      intro hz
      change (fderiv ℝ φ g (Y g u) • f g) ≠ 0 at hg
      exact hg (by simp [hz])
  have hz : ∀ᵐ g ∂μ, g ∈ Ω → (q (v + w) - (q v + q w)) g = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hq (v + w)).sub ((hq v).add (hq w)))
    intro φ hφ hcφ hsφ
    have hi u := integrable_test_smul_of_locallyIntegrableOn (hq u) hφ.continuous hcφ hsφ
    have hisum : Integrable (fun g => φ g • q v g + φ g • q w g) μ := (hi v).add (hi w)
    simp only [Pi.sub_apply, Pi.add_apply, smul_sub, smul_add]
    rw [integral_sub (hi _) hisum, integral_add (hi _) (hi _)]
    rw [hweak (v + w) φ hφ hcφ hsφ, hweak v φ hφ hcφ hsφ, hweak w φ hφ hcφ hsφ]
    simp only [map_add, add_smul]
    rw [integral_add (hr φ hφ hcφ v) (hr φ hφ hcφ w)]
    abel
  filter_upwards [hz] with g hg hgΩ
  exact sub_eq_zero.mp (hg hgΩ)

end PolycyclicRecognition

end

end OAI
