import OAI.NumberTheory.CubicMoment.Estimates.HeightAveraging
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Absolute Fubini for a bounded height polynomial and an integrable
Mellin weight. No mean estimate or interchange is assumed. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma continuous_height_convolution {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) :
    Continuous (fun t => ∫ s : ℝ, f s*G (t+u+s)) := by
  apply continuous_of_dominated (bound := fun s => ‖f s‖*M)
  · intro t
    exact (hf.mul (hG.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · intro t
    filter_upwards with s
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound _) (_root_.norm_nonneg _)
  · exact hfi.norm.mul_const M
  · filter_upwards with s
    exact continuous_const.mul (hG.comp ((continuous_id.add continuous_const).add continuous_const))

lemma integrable_height_convolution_kernel {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun p : ℝ × ℝ => f p.1*G (p.2+u+p.1))
      (volume.prod (volume.restrict (Icc a b))) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let K : ℝ × ℝ → ℝ := fun p => f p.1*G (p.2+u+p.1)
  have hc : Continuous K :=
    (hf.comp continuous_fst).mul (hG.comp ((continuous_snd.add continuous_const).add continuous_fst))
  have hm : AEStronglyMeasurable K (volume.prod μ) := hc.aestronglyMeasurable
  have hb (s : ℝ) : (∫ t, ‖K (s,t)‖ ∂μ) ≤ (b-a)*M*‖f s‖ := by
    have hki : IntervalIntegrable (fun t => ‖K (s,t)‖) volume a b :=
      ((hc.comp (continuous_const.prodMk continuous_id)).norm).intervalIntegrable a b
    have hi := intervalIntegral.integral_mono_on hab hki
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖f s‖*M) volume a b)
      (fun t _ => by
        dsimp [K]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg (f s)))
    rw [intervalIntegral.integral_const,smul_eq_mul] at hi
    simpa only [μ,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,
      mul_comm,mul_left_comm,mul_assoc] using hi
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall (fun s =>
    (hc.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc),?_⟩
  apply (hfi.norm.const_mul ((b-a)*M)).mono' hm.norm.integral_prod_right'
  exact Filter.Eventually.of_forall (fun s => by
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => _root_.norm_nonneg _))]
    exact hb s)

lemma height_convolution_interval_swap {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ∫ s : ℝ, f s*G (t+u+s)) =
      ∫ s : ℝ, f s*(∫ t in a..b, G (t+u+s)) := by
  have hi := integrable_height_convolution_kernel hf hfi hG hbound u hab
  have hs := (integral_integral_swap (f := fun s t : ℝ => f s*G (t+u+s)) hi).symm
  simp only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab] at hs
  rw [hs]
  apply integral_congr_ae
  filter_upwards with s
  exact intervalIntegral.integral_const_mul _ _

lemma integrable_height_convolution_interval {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun s : ℝ => f s*(∫ t in a..b, G (t+u+s))) := by
  have hi := (integrable_height_convolution_kernel hf hfi hG hbound u hab).integral_prod_left
  simp only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_const_mul] at hi
  exact hi

lemma intervalIntegrable_height_convolution {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun t => ∫ s : ℝ, f s*G (t+u+s)) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  exact (integrable_height_convolution_kernel hf hfi hG hbound u hab).integral_prod_right

theorem dyadicHeightMean_convolution {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    dyadicHeightMean (fun t => ∫ s : ℝ, f s*G (t+u+s)) T =
      ∫ s : ℝ, f s*dyadicHeightMean (fun t => G (t+u+s)) T := by
  have hp : T ≤ 2*T := by linarith
  have hn : -2*T ≤ -T := by linarith
  have hip := integrable_height_convolution_interval hf hfi hG hbound u hp
  have hin := integrable_height_convolution_interval hf hfi hG hbound u hn
  rw [dyadicHeightMean,height_convolution_interval_swap hf hfi hG hbound u hp,
    height_convolution_interval_swap hf hfi hG hbound u hn,← integral_add hip hin,← integral_div]
  apply integral_congr_ae
  filter_upwards with s
  dsimp [dyadicHeightMean]
  ring

end CubicFirstMoment

end

end OAI
