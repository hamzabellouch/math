import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialRiesz

namespace OAI

/-! The energy norm is the literal radial quadratic form, including
its exponential Fourier potential. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicTheta_l2_norm_sq_measure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {X : Type*} [MeasurableSpace X] {μ : Measure X} (F : Lp E 2 μ) :
    ‖F‖^2=∫ t : X, ‖F t‖^2 ∂μ := by
  calc
    _ = (inner ℂ F F).re := (inner_self_eq_norm_sq (𝕜:=ℂ) F).symm
    _ = ∫ t : X, (inner ℂ (F t) (F t)).re ∂μ :=
      (integral_re (L2.integrable_inner (𝕜:=ℂ) F F)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      exact inner_self_eq_norm_sq (𝕜:=ℂ) (F t)

lemma cubicTheta_l2_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (F : Lp E 2 (volume : Measure ℝ)) :
    ‖F‖^2=∫ t : ℝ, ‖F t‖^2 := cubicTheta_l2_norm_sq_measure F

lemma cubicThetaRadialJet_norm_sq {A : ℝ} (hA : 0 ≤ A) (f : ℝ → ℂ) (t : ℝ) :
    ‖cubicThetaRadialJet A f t‖^2=
      ‖f t‖^2+‖deriv f t‖^2+A*Real.exp (2*t)*‖f t‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [cubicThetaRadialJet,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    norm_smul,Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg A) (Real.exp_nonneg t))]
  have he : Real.exp (2*t)=(Real.exp t)^2 := by rw [two_mul,Real.exp_add]; ring
  rw [he]
  simp only [mul_pow,Real.sq_sqrt hA]
  ring

lemma cubicThetaRadialGraph_norm_sq {A : ℝ} (hA : 0 ≤ A) (f : cubicThetaRadialTests) :
    ‖cubicThetaRadialGraph A f‖^2=
      ∫ t : ℝ, ‖(f:ℝ → ℂ) t‖^2+‖deriv (f:ℝ → ℂ) t‖^2+
        A*Real.exp (2*t)*‖(f:ℝ → ℂ) t‖^2 := by
  rw [cubicTheta_l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [(cubicThetaRadialJet_memLp A f).coeFn_toLp] with t ht
  change ‖((cubicThetaRadialJet_memLp A f).toLp _) t‖^2=_
  rw [ht,cubicThetaRadialJet_norm_sq hA]

end CubicFirstMoment

end

end OAI
