import OAI.NumberTheory.CubicMoment.Estimates.SmallBVarianceRemainder
import OAI.NumberTheory.CubicMoment.Estimates.ThinAnnulusCount
import OAI.NumberTheory.CubicMoment.Estimates.SchwartzLattice

namespace OAI

/-! The exact zero mode scales with the radial cell width. -/
noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma thin_radial_integral_bound (W : ℝ → ℂ) {J : ℝ} (hJ : 0 < J)
    (hW : ∀ x, ‖W x‖ ≤ 1)
    (hsupport : ∀ x, W x ≠ 0 → 1 ≤ x ∧ x ≤ 1+1/J) :
    ‖∫ z : ℂ, W (Complex.normSq z)‖ ≤ Real.pi/J := by
  let R := Real.sqrt (1+1/J)
  let S := closedBall (0:ℂ) R \ ball 0 1
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [one_div_pos.mpr hJ])
  have hm : MeasurableSet S := measurableSet_closedBall.diff measurableSet_ball
  have hfin : volume S ≠ ⊤ := by
    apply measure_ne_top_of_subset sdiff_subset
    rw [Complex.volume_closedBall]
    finiteness
  have hg : Integrable (S.indicator (fun _ : ℂ => (1:ℝ))) :=
    (integrable_indicator_iff hm).mpr (integrableOn_const hfin)
  have hbound : ∀ z : ℂ, ‖W (Complex.normSq z)‖ ≤ S.indicator (fun _ => (1:ℝ)) z := by
    intro z
    by_cases hz : W (Complex.normSq z) = 0
    · rw [hz,norm_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) z
    · have hs := hsupport (Complex.normSq z) hz
      have hzS : z ∈ S := by
        refine ⟨?_,?_⟩
        · change dist z 0 ≤ R
          rw [dist_zero_right]
          have hr := Real.sq_sqrt (show 0 ≤ 1+1/J by positivity)
          rw [Complex.normSq_eq_norm_sq] at hs
          dsimp [R]
          nlinarith [_root_.norm_nonneg z,Real.sqrt_nonneg (1+1/J)]
        · change ¬dist z 0 < 1
          rw [dist_zero_right,Complex.normSq_eq_norm_sq] at *
          nlinarith [_root_.norm_nonneg z]
      simpa only [indicator_of_mem hzS] using hW (Complex.normSq z)
  have harea : volume.real S = Real.pi/J := by
    have hsub : ball (0:ℂ) 1 ⊆ closedBall 0 R :=
      (ball_subset_ball hR1).trans ball_subset_closedBall
    have hcfin : volume (closedBall (0:ℂ) R) ≠ ⊤ := by
      rw [Complex.volume_closedBall]
      finiteness
    rw [show S = closedBall (0:ℂ) R \ ball 0 1 from rfl,
      measureReal_sdiff hsub measurableSet_ball hcfin,complex_ball_real_volume _ (by norm_num)]
    have hcv : volume.real (closedBall (0:ℂ) R) = R^2*Real.pi := by
      simp only [measureReal_def,Complex.volume_closedBall,ENNReal.toReal_mul,
        ENNReal.toReal_pow,ENNReal.toReal_ofReal hR,ENNReal.coe_toReal,NNReal.coe_real_pi]
    rw [hcv,show R^2 = 1+1/J from Real.sq_sqrt (by positivity)]
    ring
  calc
    _ ≤ ∫ z : ℂ, S.indicator (fun _ => (1:ℝ)) z :=
      norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)
    _ = volume.real S := by rw [integral_indicator_const _ hm,smul_eq_mul,mul_one]
    _ = _ := harea

theorem thin_normProfileFourier_zero (W : ℝ → ℂ) {J : ℝ} (hJ : 0 < J)
    (hW : ∀ x, ‖W x‖ ≤ 1)
    (hsupport : ∀ x, W x ≠ 0 → 1 ≤ x ∧ x ≤ 1+1/J) :
    ‖normProfileFourier W 0‖ ≤ (2*Real.pi/Real.sqrt 3)/J := by
  rw [normProfileFourier,traceFourier_zero,norm_smul,
    Real.norm_of_nonneg (show 0 ≤ 2/Real.sqrt 3 by positivity)]
  apply (mul_le_mul_of_nonneg_left (thin_radial_integral_bound W hJ hW hsupport)
    (show 0 ≤ 2/Real.sqrt 3 by positivity)).trans_eq
  ring

theorem thin_varianceZeroMode_bound (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b) (β : Eisenstein → ℂ)
    (W : ℝ → ℂ) {A J : ℝ} (hA : 0 ≤ A) (hJ : 0 < J)
    (hW : ∀ x, ‖W x‖ ≤ 1)
    (hsupport : ∀ x, W x ≠ 0 → 1 ≤ x ∧ x ≤ 1+1/J) :
    ‖varianceZeroMode S β W A‖ ≤
      (2*Real.pi/(9*Real.sqrt 3))*(A/J)*∑ b ∈ S, ‖β b‖^2 := by
  have hb := commonGramZeroMode_sum_bound S (commonRowFactors S) hS
    (fun k hk => commonRowFactors_spec hS hk) (fun b => star (β b)) W hA
  simp only [norm_star] at hb
  apply hb.trans
  have ht := div_le_div_of_nonneg_right (thin_normProfileFourier_zero W hJ hW hsupport)
    (by norm_num : (0:ℝ) ≤ 9)
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ht hA) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans_eq
  ring

end CubicFirstMoment

end

end OAI
