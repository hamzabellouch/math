import OAI.Probability.InvariantIsing.Gaussian.MPAngularCoordinates

namespace OAI

/-! Exact real change of variables for the literal MP density on its support interval. -/
noncomputable section
open Real Set MeasureTheory
namespace InvariantIsing

lemma continuous_mpAngle (α : ℝ) : Continuous (mpAngle α) :=
  continuous_const.add (continuous_const.mul continuous_cos)

lemma measurable_mpDensity (α : ℝ) : Measurable (mpDensity α) := by
  unfold mpDensity
  fun_prop

lemma mpAngle_deriv_nonpos {α x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    -(2*sqrt α)*sin x ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (by norm_num) (sqrt_nonneg _)))
    (sin_pos_of_pos_of_lt_pi hx.1 hx.2).le

theorem mpDensity_substitution {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ) :
    (∫ y in Icc (marchenkoPasturA α) (marchenkoPasturB α), mpDensity α y*g y) =
      ∫ x in Icc 0 Real.pi, (2*α/Real.pi)*((sin x)^2/mpAngle α x)*g (mpAngle α x) := by
  have h := integral_Icc_deriv_smul_of_deriv_nonpos
    (f := mpAngle α) (f' := fun x => -(2*sqrt α)*sin x)
    (g := fun y => mpDensity α y*g y)
    (continuous_mpAngle α).continuousOn (fun x _ => mpAngle_hasDerivAt α x)
    (fun _ hx => mpAngle_deriv_nonpos hx) pi_pos.le
  have he : (∫ x in Icc 0 Real.pi, (-(2*sqrt α)*sin x) •
      (mpDensity α (mpAngle α x)*g (mpAngle α x))) =
      -(∫ x in Icc 0 Real.pi, (2*α/Real.pi)*((sin x)^2/mpAngle α x)*g (mpAngle α x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [smul_eq_mul]
    calc
      _ = -((2*sqrt α*sin x)*mpDensity α (mpAngle α x)*g (mpAngle α x)) := by ring
      _ = _ := by rw [mpAngle_density_jacobian hα.le hx]
  rw [he,(mpAngle_endpoints hα.le).1,(mpAngle_endpoints hα.le).2] at h
  exact (neg_injective h).symm

end InvariantIsing

end

end OAI
