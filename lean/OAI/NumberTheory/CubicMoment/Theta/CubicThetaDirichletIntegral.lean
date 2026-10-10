import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothMellin

namespace OAI

/-! Absolute interchange for the actual frequency Dirichlet series along
a vertical line. This will be applied to the dual series on a far-left
Mellin contour, where its argument has real part greater than two. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaDirichlet_integral_summable {a : Eisenstein→ℂ} {C σ : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C) (hσ : 2<σ)
    (u : ℝ→ℂ) (hre : ∀ t, (u t).re=σ)
    (H : ℝ→ℂ) (hH : Integrable H) :
    Summable (fun n : MetaplecticDualArgument =>
      a n.val*∫ t : ℝ, H t*(‖cubicThetaFrequency n.val‖:ℂ)^(-u t)) := by
  have hw := (cubicTheta_mellin_weight_summable hC ha hσ).subtype
    (fun n : Eisenstein => n≠0)
  have hw' : Summable (fun n : MetaplecticDualArgument =>
      ‖a n.val‖*‖cubicThetaFrequency n.val‖^(-σ)) := hw.congr (fun n => by
    dsimp only [Function.comp_apply]
    exact ite_eq_right n.property)
  apply (hw'.mul_right (∫ t : ℝ, ‖H t‖)).of_norm_bounded
  intro n
  rw [norm_mul]
  have hbound : ‖∫ t : ℝ, H t*(‖cubicThetaFrequency n.val‖:ℂ)^(-u t)‖ ≤
      ‖cubicThetaFrequency n.val‖^(-σ)*(∫ t : ℝ, ‖H t‖) := by
    rw [←integral_const_mul]
    apply norm_integral_le_of_norm_le (hH.norm.const_mul _)
    filter_upwards with t
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
      (cubicThetaFrequency_pos n.property),Complex.neg_re,hre]
    exact le_of_eq (mul_comm _ _)
  exact (mul_le_mul_of_nonneg_left hbound (_root_.norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

theorem cubicThetaDirichlet_integral {a : Eisenstein→ℂ} {C σ : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C) (hσ : 2<σ)
    (u : ℝ→ℂ) (hu : Continuous u) (hre : ∀ t, (u t).re=σ)
    (H : ℝ→ℂ) (hH : Integrable H) :
    (∫ t : ℝ, H t*cubicThetaDirichlet a (u t)) =
      ∑' n : MetaplecticDualArgument,
        a n.val*∫ t : ℝ, H t*(‖cubicThetaFrequency n.val‖:ℂ)^(-u t) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  let F (n : MetaplecticDualArgument) (t : ℝ) : ℂ :=
    H t*(a n.val*(‖cubicThetaFrequency n.val‖:ℂ)^(-u t))
  have hn (n : MetaplecticDualArgument) (t : ℝ) :
      ‖F n t‖=(‖a n.val‖*‖cubicThetaFrequency n.val‖^(-σ))*‖H t‖ := by
    dsimp only [F]
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
      (cubicThetaFrequency_pos n.property),Complex.neg_re,hre]
    ring
  have hFi (n : MetaplecticDualArgument) : Integrable (F n) := by
    have : NeZero (‖cubicThetaFrequency n.val‖:ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr (cubicThetaFrequency_pos n.property).ne'⟩
    have hc : Continuous (fun t => a n.val*(‖cubicThetaFrequency n.val‖:ℂ)^(-u t)) :=
      continuous_const.mul ((differentiable_const_cpow_of_neZero _).continuous.comp hu.neg)
    exact (hH.norm.const_mul _).mono' (hH.aestronglyMeasurable.mul hc.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun t => (hn n t).le))
  have hw := (cubicTheta_mellin_weight_summable hC ha hσ).subtype
    (fun n : Eisenstein => n≠0)
  have hmass (n : MetaplecticDualArgument) : (∫ t : ℝ, ‖F n t‖) =
      (‖a n.val‖*‖cubicThetaFrequency n.val‖^(-σ))*(∫ t : ℝ, ‖H t‖) := by
    simp_rw [hn]
    rw [integral_const_mul]
  have hsum : Summable (fun n : MetaplecticDualArgument => ∫ t : ℝ, ‖F n t‖) := by
    have hw' : Summable (fun n : MetaplecticDualArgument =>
        ‖a n.val‖*‖cubicThetaFrequency n.val‖^(-σ)) := hw.congr (fun n => by
      dsimp only [Function.comp_apply]
      exact ite_eq_right n.property)
    simpa only [hmass] using hw'.mul_right (∫ t : ℝ, ‖H t‖)
  have hinter := integral_tsum_of_summable_integral_norm hFi hsum
  calc
    _ = ∫ t : ℝ, ∑' n : MetaplecticDualArgument, F n t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [cubicThetaDirichlet_nonzero,tsum_mul_left]
    _ = ∑' n : MetaplecticDualArgument, ∫ t : ℝ, F n t := hinter.symm
    _ = _ := by
      apply tsum_congr
      intro n
      rw [←integral_const_mul]
      congr 1
      funext t
      dsimp [F]
      ring

end CubicFirstMoment

end

end OAI
