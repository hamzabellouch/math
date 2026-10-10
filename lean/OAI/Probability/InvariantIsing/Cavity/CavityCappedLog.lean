import OAI.Probability.InvariantIsing.Cavity.CavityLogFloor
import OAI.Probability.InvariantIsing.Cavity.CavityFrameMoments

namespace OAI

/-! The negative logarithm of a capped cavity weight is controlled by
the original energy moments, uniformly in the cap. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology

namespace InvariantIsing

lemma cavity_capped_log_negative_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (hiH : Integrable H ν) {T : ℝ} (hT : 0 ≤ T) :
    max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0 ≤ ∫ x, |H x| ∂ν := by
  have him : Integrable (fun x => min (H x) T) ν := by
    apply (hiH.abs.add (integrable_const |T|)).mono'
      (hH.min measurable_const).aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      change |min (H x) T| ≤ |H x| + |T|
      apply abs_le.mpr
      constructor
      · exact le_min (by linarith [neg_abs_le (H x), abs_nonneg T])
          (by linarith [neg_abs_le T, abs_nonneg (H x)])
      · exact (min_le_left _ _).trans (by linarith [le_abs_self (H x), abs_nonneg T]))
  have hie : Integrable (fun x => Real.exp (min (H x) T)) ν := by
    apply Integrable.of_bound ((hH.min measurable_const).exp).aestronglyMeasurable (Real.exp T)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (min_le_right _ _)
  have hz := integral_exp_pos hie
  have hj : (∫ x, min (H x) T ∂ν) ≤ Real.log (∫ x, Real.exp (min (H x) T) ∂ν) :=
    (Real.le_log_iff_exp_le hz).mpr (exp_integral_le_partition him hie)
  have hl : -(∫ x, |H x| ∂ν) ≤ ∫ x, min (H x) T ∂ν := by
    rw [← integral_neg]
    apply integral_mono hiH.abs.neg him
    intro x
    exact le_min (neg_abs_le _) ((neg_nonpos.mpr (abs_nonneg _)).trans hT)
  exact max_le (by linarith) (integral_nonneg fun _ => abs_nonneg _)

lemma cavity_capped_log_negative_sq_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H R : X → ℝ)
    (hH : Measurable H) (hiH : Integrable H ν)
    (hiH2 : Integrable (fun x => |H x| ^ 2) ν)
    (hiR4 : Integrable (fun x => R x ^ 4) ν)
    {C T : ℝ} (_hC : 0 ≤ C) (hT : 0 ≤ T) (hbound : ∀ x, |H x| ≤ C * (1 + R x ^ 2)) :
    (max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0)^2 ≤
      2 * C ^ 2 * (1 + ∫ x, R x ^ 4 ∂ν) := by
  have hl := cavity_capped_log_negative_bound ν H hH hiH hT
  have hj := (convexOn_pow 2 (𝕜 := ℝ)).map_integral_le (by fun_prop)
    isClosed_Ici (ae_of_all _ (fun x => abs_nonneg (H x))) hiH.abs hiH2
  have hp : (max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0)^2 ≤ ∫ x, |H x|^2 ∂ν := by
    exact (pow_le_pow_left₀ (le_max_right _ _) hl 2).trans hj
  have hu : (∫ x, |H x|^2 ∂ν) ≤ 2 * C ^ 2 * (1 + ∫ x, R x ^ 4 ∂ν) := by
    have hb := integral_mono hiH2 ((integrable_const 1).add hiR4 |>.const_mul (2 * C ^ 2))
      (fun x => by
        change |H x| ^ 2 ≤ 2 * C ^ 2 * (1 + R x ^ 4)
        have hs := pow_le_pow_left₀ (abs_nonneg (H x)) (hbound x) 2
        nlinarith [sq_nonneg (R x ^ 2 - 1), sq_nonneg C])
    simpa only [integral_const_mul, Pi.add_apply, integral_add (integrable_const 1) hiR4,
      integral_const, probReal_univ, one_smul] using hb
  exact hp.trans hu

theorem cavity_capped_log_negative_sq_of_growth {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H R : X → ℝ) (hH : Measurable H)
    (hiR4 : Integrable (fun x => R x ^ 4) ν)
    {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hbound : ∀ x, |H x| ≤ C * (1 + R x ^ 2)) :
    (max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0)^2 ≤
      2 * C ^ 2 * (1 + ∫ x, R x ^ 4 ∂ν) := by
  have hs x : |H x|^2 ≤ 2 * C^2 * (1 + R x^4) := by
    have hh := pow_le_pow_left₀ (abs_nonneg (H x)) (hbound x) 2
    nlinarith [sq_nonneg (R x^2 - 1), sq_nonneg C]
  have hiH : Integrable H ν := by
    apply (((integrable_const 1).add hiR4).const_mul (2 * C)).mono' hH.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      change |H x| ≤ 2 * C * (1 + R x^4)
      have hh := mul_le_mul_of_nonneg_left
        (show 1 + R x^2 ≤ 2 * (1 + R x^4) by nlinarith [sq_nonneg (R x^2 - 1)]) hC
      nlinarith [hbound x]
  have hiH2 : Integrable (fun x => |H x|^2) ν := by
    apply (((integrable_const 1).add hiR4).const_mul (2 * C^2)).mono'
      (hH.abs.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hs x
  exact cavity_capped_log_negative_sq_bound ν H R hH hiH hiH2 hiR4 hC hT hbound

end InvariantIsing

end

end OAI
