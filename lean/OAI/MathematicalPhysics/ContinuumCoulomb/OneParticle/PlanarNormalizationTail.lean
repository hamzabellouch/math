import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarExponentialEnvelope
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatBoxCoordinates

namespace OAI

/-! Quantitative truncation of the actual planar normalization integral.
All constants below depend only on the fixed manufactured forcing. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarNormalizationTailConstant : ℝ :=
  planarExponentialConstant (1 / 2) ^ 2 *
    ∫ r : PlanarPosition, Real.exp (-(1 / 2 : ℝ) * ‖r‖)

theorem planarNormalizationTailConstant_nonnegative :
    0 ≤ planarNormalizationTailConstant := by
  unfold planarNormalizationTailConstant
  exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem real_quarter_exponential_integral :
    (∫ x : ℝ, Real.exp (-(1 / 4 : ℝ) * |x|)) = 8 := by
  rw [integral_comp_abs (f := fun x : ℝ => Real.exp (-(1 / 4 : ℝ) * x))]
  have h := integral_exp_mul_Ioi (by norm_num : -(1 / 4 : ℝ) < 0) 0
  norm_num at h ⊢
  linarith

theorem planar_half_exponential_integral_le :
    (∫ r : PlanarPosition, Real.exp (-(1 / 2 : ℝ) * ‖r‖)) ≤ 64 := by
  let g := fun x : ℝ => Real.exp (-(1 / 4 : ℝ) * |x|)
  have hg : Integrable g := Integrable.of_integral_ne_zero (by
    change (∫ x : ℝ, Real.exp (-(1 / 4 : ℝ) * |x|)) ≠ 0
    rw [real_quarter_exponential_integral]
    norm_num)
  have hprod : Integrable (fun p : ℝ × ℝ => g p.1 * g p.2) := by
    simpa only [Measure.volume_eq_prod] using hg.mul_prod hg
  have hbound (p : ℝ × ℝ) : Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖) ≤
      g p.1 * g p.2 := by
    have h0 : |p.1| ≤ ‖planarPairEquiv.symm p‖ := by
      simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
        Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 0
    have h1 : |p.2| ≤ ‖planarPairEquiv.symm p‖ := by
      simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 1
    dsimp only [g]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hi : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖)) := by
    apply hprod.mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hbound p)
  rw [planarPair_integral]
  apply (integral_mono hi hprod hbound).trans_eq
  rw [Measure.volume_eq_prod, integral_prod_mul]
  change (∫ x : ℝ, Real.exp (-(1 / 4 : ℝ) * |x|)) *
    (∫ x : ℝ, Real.exp (-(1 / 4 : ℝ) * |x|)) = 64
  rw [real_quarter_exponential_integral]
  norm_num

theorem planarNormalizationTailConstant_le : planarNormalizationTailConstant ≤ 1024 := by
  have he := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  norm_num at he
  have hC : 0 ≤ planarExponentialConstant (1 / 2) :=
    (planarExponentialConstant_positive (by norm_num) (by norm_num)).le
  have hC' : planarExponentialConstant (1 / 2) ≤ 4 := by
    unfold planarExponentialConstant
    norm_num
    linarith
  have hm := planar_half_exponential_integral_le
  have hm0 : 0 ≤ ∫ r : PlanarPosition, Real.exp (-(1 / 2 : ℝ) * ‖r‖) :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  unfold planarNormalizationTailConstant
  nlinarith

theorem planarResolvent_square_tail_pointwise {L : ℝ} (r : PlanarPosition)
    (hr : L ≤ ‖r‖) :
    planarResolventMode r ^ 2 ≤
      (planarExponentialConstant (1 / 2) ^ 2 * Real.exp (-(1 / 2 : ℝ) * L)) *
        Real.exp (-(1 / 2 : ℝ) * ‖r‖) := by
  have he := pow_le_pow_left₀ (planarResolventMode_positive r).le
    (planarResolventMode_exponential_envelope (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) r) 2
  rw [mul_pow, ← Real.exp_nat_mul] at he
  have hexp : Real.exp ((2 : ℝ) * (-(1 / 2 : ℝ) * ‖r‖)) ≤
      Real.exp (-(1 / 2 : ℝ) * L) * Real.exp (-(1 / 2 : ℝ) * ‖r‖) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  exact he.trans ((mul_le_mul_of_nonneg_left hexp
    (sq_nonneg (planarExponentialConstant (1 / 2)))).trans_eq (by ring))

theorem planarNormalization_tail (L : ℝ) :
    (∫ r in {r : PlanarPosition | L ≤ ‖r‖}, planarResolventMode r ^ 2) ≤
      planarNormalizationTailConstant * Real.exp (-(1 / 2 : ℝ) * L) := by
  let C := planarExponentialConstant (1 / 2) ^ 2 * Real.exp (-(1 / 2 : ℝ) * L)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi := (planar_exp_norm_integrable (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
  have h := setIntegral_mono_on planarResolventMode_square_integrable.integrableOn
    hi.integrableOn (isClosed_le continuous_const continuous_norm).measurableSet
    (fun r hr => planarResolvent_square_tail_pointwise r hr)
  have h' := integral_mono_measure
    (μ := volume.restrict {r : PlanarPosition | L ≤ ‖r‖}) (Measure.restrict_le_self) (Filter.Eventually.of_forall (fun r =>
      mul_nonneg hC (Real.exp_pos _).le)) hi
  calc
    _ ≤ ∫ r in {r : PlanarPosition | L ≤ ‖r‖}, C * Real.exp (-(1 / 2 : ℝ) * ‖r‖) := h
    _ ≤ ∫ r : PlanarPosition, C * Real.exp (-(1 / 2 : ℝ) * ‖r‖) := h'
    _ = _ := by rw [integral_const_mul]; unfold planarNormalizationTailConstant C; ring

end ContinuumCoulomb

end

end OAI
