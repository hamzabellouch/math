import OAI.Analysis.ModularTheory.CoreIntegrals
import OAI.Analysis.ModularTheory.FourierTranslation
import OAI.Analysis.OperatorAlgebra.ScalarSliceContinuity

namespace OAI

/-! Scalar translation integrals commute on integrable L² vectors.  The
proof uses bounded Schwartz test vectors, so every Fubini interchange has
an explicit product-integrable majorant. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace SchwartzMap

namespace WeakPureInfiniteness

lemma scalar_convolution_test_center (g : ℝ → ℂ)
    (h : BoundedContinuousFunction ℝ ℂ) (t : ℝ) :
    (∫ s : ℝ, star (h s) * g (s - t)) =
      ∫ r : ℝ, star (h (r + t)) * g r := by
  simpa only [add_sub_cancel_right] using
    (integral_add_right_eq_self (fun s : ℝ => star (h s) * g (s - t)) t).symm

lemma scalar_convolution_test_swap (k g : ℝ → ℂ)
    (hk : Integrable k) (hg : Integrable g) (h : BoundedContinuousFunction ℝ ℂ) :
    (∫ t : ℝ, k t * ∫ s : ℝ, star (h s) * g (s - t)) =
      ∫ t : ℝ, g t * ∫ s : ℝ, star (h s) * k (s - t) := by
  have hi : Integrable (fun p : ℝ × ℝ => k p.1 * g p.2 * star (h (p.2 + p.1)))
      (volume.prod volume) := by
    apply ((hk.norm.mul_prod hg.norm).mul_const ‖h‖).mono'
      ((hk.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd).mul
        ((h.continuous.comp (continuous_snd.add continuous_fst)).star.aestronglyMeasurable))
    filter_upwards [] with p
    simpa only [Pi.mul_apply, Function.comp_def, Pi.add_apply, norm_mul, norm_star] using
      (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm (p.2 + p.1))
        (mul_nonneg (norm_nonneg (k p.1)) (norm_nonneg (g p.2))))
  calc
    _ = ∫ t : ℝ, ∫ r : ℝ, k t * g r * star (h (r + t)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [scalar_convolution_test_center, ← integral_const_mul]
      congr 1
      funext r
      ring
    _ = ∫ r : ℝ, ∫ t : ℝ, k t * g r * star (h (r + t)) := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with r
      rw [scalar_convolution_test_center, ← integral_const_mul]
      congr 1
      funext t
      rw [add_comm t r]
      ring

lemma scalar_translation_schwartz_inner (h : 𝓢(ℝ, ℂ))
    (g : Lp ℂ 2 (volume : Measure ℝ)) (t : ℝ) :
    inner ℂ (h.toLp 2) (modularLpTranslate volume t g) =
      ∫ s : ℝ, star (h s) * g (s - t) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h.coeFn_toLp 2 (volume : Measure ℝ), modularLpTranslate_ae volume t g]
    with s hh hg
  rw [hh, hg]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

lemma integratedScalarTranslation_schwartz_inner (k : ℝ → ℂ) (hk : Integrable k)
    (g : Lp ℂ 2 (volume : Measure ℝ)) (h : 𝓢(ℝ, ℂ)) :
    inner ℂ (h.toLp 2) (integratedModularTranslation k hk g) =
      ∫ t : ℝ, k t * ∫ s : ℝ, star (h s) * g (s - t) := by
  have hi := BoundedRecovery.integrable_smul_bounded_orbit hk
    (continuous_modularLpTranslate g) (fun t => (modularLpTranslate volume t).norm_map g |>.le)
  rw [integratedModularTranslation_apply, ← integral_inner hi]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [inner_smul_right, scalar_translation_schwartz_inner]

theorem integratedScalarTranslation_comm (k g : Lp ℂ 2 (volume : Measure ℝ))
    (hk : Integrable (k : ℝ → ℂ)) (hg : Integrable (g : ℝ → ℂ)) :
    integratedModularTranslation k hk g = integratedModularTranslation g hg k := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  apply ext_inner_left ℂ
  intro h
  apply hd.induction_on (p := fun h =>
    inner ℂ h (integratedModularTranslation k hk g) =
      inner ℂ h (integratedModularTranslation g hg k)) h
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro h
    change inner ℂ (h.toLp 2) (integratedModularTranslation k hk g) =
      inner ℂ (h.toLp 2) (integratedModularTranslation g hg k)
    rw [integratedScalarTranslation_schwartz_inner, integratedScalarTranslation_schwartz_inner]
    exact scalar_convolution_test_swap k g hk hg h.toBoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma scalarVectorLp_translate (g : Lp ℂ 2 (volume : Measure ℝ)) (x : H) (t : ℝ) :
    modularLpTranslate volume t (scalarVectorLp volume g x) =
      scalarVectorLp volume (modularLpTranslate volume t g) x := by
  apply Lp.ext
  filter_upwards [modularLpTranslate_ae volume t (scalarVectorLp volume g x),
    (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae
      (scalarVectorLp_ae volume g x),
    scalarVectorLp_ae volume (modularLpTranslate volume t g) x,
    modularLpTranslate_ae volume t g] with s h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

lemma scalarVectorLp_integratedTranslation (k : ℝ → ℂ) (hk : Integrable k)
    (g : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    integratedModularTranslation k hk (scalarVectorLp volume g x) =
      scalarVectorLp volume (integratedModularTranslation k hk g) x := by
  have hi := BoundedRecovery.integrable_smul_bounded_orbit hk
    (continuous_modularLpTranslate g) (fun t => (modularLpTranslate volume t).norm_map g |>.le)
  change _ = (ContinuousLinearMap.toSpanSingleton ℂ x).compLpL 2 volume
    (integratedModularTranslation k hk g)
  rw [integratedModularTranslation_apply, integratedModularTranslation_apply,
    ← ContinuousLinearMap.integral_comp_comm _ hi]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [map_smul, scalarVectorLp_translate]
  rfl

lemma scalarVectorLp_convolution_synthesis (g u : Lp ℂ 2 (volume : Measure ℝ))
    (hg : Integrable (g : ℝ → ℂ)) (hu : Integrable (u : ℝ → ℂ)) (x : H) :
    integratedModularTranslation g hg (scalarVectorLp volume u x) =
      ∫ t : ℝ, u t • scalarVectorLp volume (modularLpTranslate volume t g) x := by
  rw [scalarVectorLp_integratedTranslation, integratedScalarTranslation_comm g u hg hu,
    ← scalarVectorLp_integratedTranslation, integratedModularTranslation_apply]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [scalarVectorLp_translate]

end WeakPureInfiniteness

end

end OAI
