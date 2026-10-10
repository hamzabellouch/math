import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution

namespace HarmonicCounterexample.Analytic

abbrev E3 := EuclideanSpace ℝ (Fin 3)

lemma weak_continuous_convolution_derivative
    (u : E3 → ℝ) (W : E3 → E3 →L[ℝ] ℝ) (hu : Continuous u) (hW : Continuous W)
    (hweak : ∀ (φ : E3 → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ a : E3,
      (∫ y, u y*fderiv ℝ φ y a) = -(∫ y, φ y*W y a))
    (κ : E3 → ℝ) (hκ : ContDiff ℝ ∞ κ) (hsκ : HasCompactSupport κ) (x : E3) :
    HasFDerivAt (κ ⋆[lsmul ℝ ℝ,volume] u)
      ((κ ⋆[lsmul ℝ ℝ,volume] W) x) x := by
  have hh := hsκ.hasFDerivAt_convolution_right (μ:=volume) (lsmul ℝ ℝ) hu.locallyIntegrable
    (hκ.of_le (by simp)) x
  have hf : (u ⋆[lsmul ℝ ℝ,volume] κ) = (κ ⋆[lsmul ℝ ℝ,volume] u) := by
    ext z
    rw [convolution_eq_swap,convolution_def]
    apply integral_congr_ae
    filter_upwards with y
    simp [mul_comm]
  rw [hf] at hh
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro a
  have hφ : ContDiff ℝ ∞ (fun y : E3 ↦ κ (x-y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have hsφ : HasCompactSupport (fun y : E3 ↦ κ (x-y)) :=
    hsκ.comp_homeomorph (Homeomorph.subLeft x)
  have hd (y : E3) : fderiv ℝ (fun z ↦ κ (x-z)) y a = -fderiv ℝ κ (x-y) a := by
    have h := ((hκ.differentiable (by simp) (x-y)).hasFDerivAt).comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    have h' : HasFDerivAt (fun z : E3 ↦ κ (x-z)) (-(fderiv ℝ κ (x-y))) y := by
      convert! h using 1
      ext v
      simp
    have he := congrArg (fun L : E3 →L[ℝ] ℝ ↦ L a) h'.fderiv
    simpa only [_root_.neg_apply] using he
  have hi : Integrable (fun y ↦ κ (x-y) • W y) volume := by
    have h := hsκ.convolutionExists_left (μ:=volume) (lsmul ℝ ℝ) hκ.continuous hW.locallyIntegrable x
    rw [←convolutionExistsAt_flip] at h
    exact h
  rw [convolution_eq_swap]
  simp only [lsmul_apply]
  rw [ContinuousLinearMap.integral_apply hi]
  rw [convolution_precompR_apply (lsmul ℝ ℝ) hu.locallyIntegrable
    (hsκ.fderiv ℝ) (hκ.continuous_fderiv (by simp)),convolution_def]
  have he := hweak _ hφ hsφ a
  simp_rw [hd,mul_neg,integral_neg] at he
  simpa only [lsmul_apply,smul_eq_mul,smul_apply] using (neg_inj.mp he).symm

noncomputable def regularizingBump (n : ℕ) : ContDiffBump (0 : E3) where
  rIn := 1/((n:ℝ)+1)
  rOut := 2/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

lemma regularizingBump_tendsto :
    Tendsto (fun n ↦ (regularizingBump n).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul 2
  simpa only [regularizingBump,mul_one_div, mul_zero] using h

theorem continuous_weak_hasFDerivAt
    (u : E3 → ℝ) (W : E3 → E3 →L[ℝ] ℝ) (hu : Continuous u) (hW : Continuous W)
    (hweak : ∀ (φ : E3 → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ a : E3,
      (∫ y, u y*fderiv ℝ φ y a) = -(∫ y, φ y*W y a)) (x : E3) :
    HasFDerivAt u (W x) x := by
  let f : ℕ → E3 → ℝ := fun n ↦ (regularizingBump n).normed volume ⋆[lsmul ℝ ℝ,volume] u
  let f' : ℕ → E3 → E3 →L[ℝ] ℝ := fun n ↦
    (regularizingBump n).normed volume ⋆[lsmul ℝ ℝ,volume] W
  have hder (n : ℕ) (y : E3) : HasFDerivAt (f n) (f' n y) y :=
    weak_continuous_convolution_derivative u W hu hW hweak _
      (regularizingBump n).contDiff_normed (regularizingBump n).hasCompactSupport_normed y
  have hjoint : Tendsto (fun p : ℕ × E3 ↦ f' p.1 p.2) (atTop ×ˢ 𝓝 x) (𝓝 (W x)) := by
    apply ContDiffBump.convolution_tendsto_right
      (φ:=fun p : ℕ × E3 ↦ regularizingBump p.1)
      (g:=fun _ : ℕ × E3 ↦ W)
      (regularizingBump_tendsto.comp tendsto_fst)
    · exact Eventually.of_forall fun _ ↦ hW.aestronglyMeasurable
    · exact (hW.tendsto x).comp tendsto_snd
    · exact tendsto_snd
  have hlim : Tendsto (fun p : ℕ × E3 ↦ W p.2) (atTop ×ˢ 𝓝 x) (𝓝 (W x)) :=
    (hW.tendsto x).comp tendsto_snd
  have hf' : TendstoUniformlyOnFilter f' W atTop (𝓝 x) :=
    (hlim.prodMk_nhds hjoint).mono_right (nhds_le_uniformity (W x))
  apply hasFDerivAt_of_tendstoUniformlyOnFilter hf'
  · exact Eventually.of_forall fun p ↦ hder p.1 p.2
  · exact Eventually.of_forall fun y ↦
      ContDiffBump.convolution_tendsto_right_of_continuous regularizingBump_tendsto hu y

end HarmonicCounterexample.Analytic

end

end OAI
