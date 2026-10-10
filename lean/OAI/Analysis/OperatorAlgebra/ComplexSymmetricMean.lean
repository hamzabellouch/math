import OAI.Analysis.ModularRecovery.Mean

namespace OAI

/-! The complex linear version of the proved symmetric-interval mean.
It is positive, normalized and translation invariant for a free ultrafilter. -/

noncomputable section
open Filter
open scoped ComplexOrder

namespace WeakPureInfiniteness
open BoundedRecovery

private def meanRealPart (f : BoundedContinuousFunction ℝ ℂ) :
    BoundedContinuousFunction ℝ ℝ := Complex.reCLM.compLeftContinuousBounded ℝ f

private def meanImagPart (f : BoundedContinuousFunction ℝ ℂ) :
    BoundedContinuousFunction ℝ ℝ := Complex.imCLM.compLeftContinuousBounded ℝ f

def complexSymmetricMean (ω : Ultrafilter ℕ) (f : BoundedContinuousFunction ℝ ℂ) : ℂ :=
  (fixedMean ω (meanRealPart f) : ℂ) + (fixedMean ω (meanImagPart f) : ℂ) * Complex.I

lemma complexSymmetricMean_add (ω : Ultrafilter ℕ)
    (f g : BoundedContinuousFunction ℝ ℂ) :
    complexSymmetricMean ω (f + g) = complexSymmetricMean ω f + complexSymmetricMean ω g := by
  have hr : meanRealPart (f + g) = meanRealPart f + meanRealPart g := by ext t; simp [meanRealPart]
  have hi : meanImagPart (f + g) = meanImagPart f + meanImagPart g := by ext t; simp [meanImagPart]
  unfold complexSymmetricMean
  rw [hr, hi]
  change ((meanCLM ω) (meanRealPart f + meanRealPart g) : ℂ) +
    ((meanCLM ω) (meanImagPart f + meanImagPart g) : ℂ) * Complex.I = _
  rw [map_add, map_add]
  simp only [Complex.ofReal_add, meanCLM_apply]
  ring

lemma complexSymmetricMean_smul (ω : Ultrafilter ℕ)
    (c : ℂ) (f : BoundedContinuousFunction ℝ ℂ) :
    complexSymmetricMean ω (c • f) = c * complexSymmetricMean ω f := by
  have hr : meanRealPart (c • f) = c.re • meanRealPart f - c.im • meanImagPart f := by
    ext t
    simp [meanRealPart, meanImagPart, Complex.mul_re]
  have hi : meanImagPart (c • f) = c.re • meanImagPart f + c.im • meanRealPart f := by
    ext t
    simp [meanRealPart, meanImagPart, Complex.mul_im]
  unfold complexSymmetricMean
  rw [hr, hi]
  change ((meanCLM ω) (c.re • meanRealPart f - c.im • meanImagPart f) : ℂ) +
    ((meanCLM ω) (c.re • meanImagPart f + c.im • meanRealPart f) : ℂ) * Complex.I = _
  rw [map_sub, map_add, map_smul, map_smul, map_smul, map_smul]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

lemma complexSymmetricMean_norm_le (ω : Ultrafilter ℕ)
    (f : BoundedContinuousFunction ℝ ℂ) : ‖complexSymmetricMean ω f‖ ≤ 2 * ‖f‖ := by
  have hr : ‖meanRealPart f‖ ≤ ‖f‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    intro t
    exact (Complex.abs_re_le_norm (f t)).trans (f.norm_coe_le_norm t)
  have hi : ‖meanImagPart f‖ ≤ ‖f‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    intro t
    exact (Complex.abs_im_le_norm (f t)).trans (f.norm_coe_le_norm t)
  calc
    _ ≤ ‖(fixedMean ω (meanRealPart f) : ℂ)‖ +
        ‖(fixedMean ω (meanImagPart f) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = ‖fixedMean ω (meanRealPart f)‖ + ‖fixedMean ω (meanImagPart f)‖ := by simp
    _ ≤ ‖f‖ + ‖f‖ := add_le_add ((norm_fixedMean_le ω _).trans hr) ((norm_fixedMean_le ω _).trans hi)
    _ = _ := by ring

def complexSymmetricMeanCLM (ω : Ultrafilter ℕ) : BoundedContinuousFunction ℝ ℂ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := complexSymmetricMean ω
      map_add' := complexSymmetricMean_add ω
      map_smul' := complexSymmetricMean_smul ω }
    2 (complexSymmetricMean_norm_le ω)

lemma complexSymmetricMean_const (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop) (c : ℂ) :
    complexSymmetricMean ω (BoundedContinuousFunction.const ℝ c) = c := by
  have hr : meanRealPart (BoundedContinuousFunction.const ℝ c) =
      BoundedContinuousFunction.const ℝ c.re := rfl
  have hi : meanImagPart (BoundedContinuousFunction.const ℝ c) =
      BoundedContinuousFunction.const ℝ c.im := rfl
  simp only [complexSymmetricMean, hr, hi, BoundedContinuousFunction.const_apply,
    fixedMean_const ω hω, Complex.re_add_im]

def complexTranslateBCF (f : BoundedContinuousFunction ℝ ℂ) (s : ℝ) :
    BoundedContinuousFunction ℝ ℂ :=
  f.compContinuous ⟨fun t => t + s, continuous_id.add continuous_const⟩

lemma complexSymmetricMean_translate (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (f : BoundedContinuousFunction ℝ ℂ) (s : ℝ) :
    complexSymmetricMean ω (complexTranslateBCF f s) = complexSymmetricMean ω f := by
  have hr : meanRealPart (complexTranslateBCF f s) = translateBCF (meanRealPart f) s := rfl
  have hi : meanImagPart (complexTranslateBCF f s) = translateBCF (meanImagPart f) s := rfl
  simp only [complexSymmetricMean, hr, hi, fixedMean_translate ω hω]

lemma complexSymmetricMean_nonneg (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (f : BoundedContinuousFunction ℝ ℂ) (hf : ∀ t, 0 ≤ f t) :
    0 ≤ complexSymmetricMean ω f := by
  have hi : meanImagPart f = 0 := by
    ext t
    exact (Complex.le_def.mp (hf t)).2.symm
  have hr : 0 ≤ fixedMean ω (meanRealPart f) := by
    have h := fixedMean_mono ω (BoundedContinuousFunction.const ℝ 0) (meanRealPart f)
      (fun t => (Complex.le_def.mp (hf t)).1)
    change fixedMean ω (fun _ : ℝ => 0) ≤ _ at h
    rw [fixedMean_const ω hω] at h
    exact h
  simp only [complexSymmetricMean, hi]
  have hz : fixedMean ω (0 : BoundedContinuousFunction ℝ ℝ) = 0 := (meanCLM ω).map_zero
  rw [hz, Complex.ofReal_zero, zero_mul, add_zero]
  exact_mod_cast hr

end WeakPureInfiniteness

end

end OAI
