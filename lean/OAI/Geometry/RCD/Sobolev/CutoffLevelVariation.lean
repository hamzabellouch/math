import OAI.Geometry.RCD.Heat.HeatCutoffEnergy

namespace OAI

/-! # Differentiating the localized upper-level square

The positive part need not be differentiable at the level. Its squared
L² norm has a quadratic remainder, including at that level. This supplies
the nonlinear time test used in the heat level-set iteration.
-/

open Set Filter MeasureTheory
open scoped NNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

theorem upperLevelPart_square_remainder (k a b : ℝ) :
    |(upperLevelPart k b)^2-(upperLevelPart k a)^2-
      2*upperLevelPart k a*(b-a)| ≤ (b-a)^2 := by
  unfold upperLevelPart
  by_cases ha : 0 ≤ a-k <;> by_cases hb : 0 ≤ b-k
  · rw [max_eq_left ha,max_eq_left hb]
    have he : (b-k)^2-(a-k)^2-2*(a-k)*(b-a) = (b-a)^2 := by ring
    rw [he,abs_of_nonneg (sq_nonneg _)]
  · rw [max_eq_left ha,max_eq_right (le_of_not_ge hb)]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (a-b),mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hb)]
  · rw [max_eq_right (le_of_not_ge ha),max_eq_left hb]
    simp only [zero_pow (by decide : (2:ℕ)≠0),sub_zero,mul_zero,zero_mul]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  · rw [max_eq_right (le_of_not_ge ha),max_eq_right (le_of_not_ge hb)]
    simp only [zero_pow (by decide : (2:ℕ)≠0),sub_zero,mul_zero,zero_mul,abs_zero]
    exact sq_nonneg _

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

theorem cutoff_level_square_remainder
    {χ : X → ℝ} {L B : ℝ≥0} (hχ : LipschitzWith L χ)
    (hb : ∀ x, |χ x| ≤ B) {k : ℝ} (hk : 0 ≤ k) (f g : Lp ℝ 2 μ) :
    let N := lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable B hb)
    let P := (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
    |‖N (P g)‖^2-‖N (P f)‖^2-2*inner ℝ (N (N (P f))) (g-f)| ≤
      (B:ℝ)^2*‖g-f‖^2 := by
  intro N P
  have hN (u : Lp ℝ 2 μ) : N u =ᵐ[μ] fun x => χ x*u x := by
    filter_upwards [lpMultiplier_coe μ
      (boundedMultiplier μ χ hχ.continuous.measurable B hb) u,
      boundedMultiplier_coe μ χ hχ.continuous.measurable B hb] with x hx hv
    rw [hx,hv]
  have hP (u : Lp ℝ 2 μ) : P u =ᵐ[μ] fun x => upperLevelPart k (u x) :=
    (upperLevelPart_lipschitz k).coeFn_compLp (upperLevelPart_zero hk) u
  have hnn : N (N (P f)) =ᵐ[μ] fun x => χ x^2*upperLevelPart k (f x) := by
    filter_upwards [hN (N (P f)),hN (P f),hP f] with x h1 h2 h3
    rw [h1,h2,h3]
    ring
  have hfi : Integrable (fun x => χ x^2*(upperLevelPart k (f x))^2) μ := by
    apply (Lp.memLp (N (P f))).integrable_sq.congr
    filter_upwards [hN (P f),hP f] with x h1 h2
    rw [h1,h2,mul_pow]
  have hgi : Integrable (fun x => χ x^2*(upperLevelPart k (g x))^2) μ := by
    apply (Lp.memLp (N (P g))).integrable_sq.congr
    filter_upwards [hN (P g),hP g] with x h1 h2
    rw [h1,h2,mul_pow]
  have hpi : Integrable (fun x => χ x^2*upperLevelPart k (f x)*(g x-f x)) μ := by
    apply ((Lp.memLp (N (N (P f)))).integrable_mul (Lp.memLp (g-f))).congr
    filter_upwards [hnn,Lp.coeFn_sub g f] with x h1 h2
    simp only [Pi.mul_apply,h1,h2,Pi.sub_apply]
  have he : ‖N (P g)‖^2-‖N (P f)‖^2-2*inner ℝ (N (N (P f))) (g-f) =
      ∫ x, χ x^2*((upperLevelPart k (g x))^2-(upperLevelPart k (f x))^2-
        2*upperLevelPart k (f x)*(g x-f x)) ∂μ := by
    rw [cutoff_L2_norm_sq μ (P g) hχ hb,cutoff_L2_norm_sq μ (P f) hχ hb,L2.inner_def]
    have h1 := integral_congr_ae ((hP g).mono fun x hx =>
      congrArg (fun z : ℝ => χ x^2*z^2) hx)
    have h2 := integral_congr_ae ((hP f).mono fun x hx =>
      congrArg (fun z : ℝ => χ x^2*z^2) hx)
    rw [h1,h2]
    have hp : (∫ x, ⟪N (N (P f)) x,(g-f) x⟫_ℝ ∂μ) =
        ∫ x, χ x^2*upperLevelPart k (f x)*(g x-f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hnn,Lp.coeFn_sub g f] with x h1 h2
      simp only [Real.inner_apply,h1,h2,Pi.sub_apply]
    rw [hp,← integral_const_mul,← integral_sub hgi hfi]
    have hsub := integral_sub (hgi.sub hfi) (hpi.const_mul 2)
    simp only [Pi.sub_apply] at hsub
    rw [← hsub]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [he]
  have hi : Integrable (fun x => χ x^2*((upperLevelPart k (g x))^2-
      (upperLevelPart k (f x))^2-2*upperLevelPart k (f x)*(g x-f x))) μ := by
    apply ((hgi.sub hfi).sub (hpi.const_mul 2)).congr
    exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply]
      ring
  calc
    _ ≤ ∫ x, |χ x^2*((upperLevelPart k (g x))^2-(upperLevelPart k (f x))^2-
        2*upperLevelPart k (f x)*(g x-f x))| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (B:ℝ)^2*(g-f) x^2 ∂μ := by
      apply integral_mono_ae hi.abs ((Lp.memLp (g-f)).integrable_sq.const_mul _)
      filter_upwards [Lp.coeFn_sub g f] with x hsub
      rw [hsub,Pi.sub_apply,abs_mul,abs_of_nonneg (sq_nonneg _)]
      have hc : χ x^2 ≤ (B:ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) B.coe_nonneg).mpr (hb x)
      exact (mul_le_mul_of_nonneg_left (upperLevelPart_square_remainder k (f x) (g x))
        (sq_nonneg _)).trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
    _ = _ := by rw [integral_const_mul,integral_sq_Lp]

theorem cutoff_level_square_hasFDerivAt
    {χ : X → ℝ} {L B : ℝ≥0} (hχ : LipschitzWith L χ)
    (hb : ∀ x, |χ x| ≤ B) {k : ℝ} (hk : 0 ≤ k) (f : Lp ℝ 2 μ) :
    let N := lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable B hb)
    let P := (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
    HasFDerivAt (fun g => ‖N (P g)‖^2) ((2:ℝ) • innerSL ℝ (N (N (P f)))) f := by
  intro N P
  rw [hasFDerivAt_iff_tendsto]
  apply squeeze_zero (fun g => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun g => ?_) (show Tendsto (fun g : Lp ℝ 2 μ => (B:ℝ)^2*‖g-f‖) (𝓝 f) (𝓝 0) by
      have hc : Continuous (fun g : Lp ℝ 2 μ => (B:ℝ)^2*‖g-f‖) :=
        continuous_const.mul (continuous_id.sub continuous_const).norm
      simpa only [sub_self,norm_zero,mul_zero] using hc.tendsto f)
  have h := mul_le_mul_of_nonneg_left (cutoff_level_square_remainder μ hχ hb hk f g)
    (inv_nonneg.mpr (norm_nonneg (g-f)))
  have he : ‖g-f‖⁻¹*((B:ℝ)^2*‖g-f‖^2) = (B:ℝ)^2*‖g-f‖ := by
    by_cases hz : ‖g-f‖ = 0
    · simp only [hz,inv_zero,zero_mul,mul_zero]
    · field_simp
  simpa only [smul_apply,innerSL_apply_apply,smul_eq_mul,
    Real.norm_eq_abs,he] using h

end RegularPointCoordinates

end

end OAI
