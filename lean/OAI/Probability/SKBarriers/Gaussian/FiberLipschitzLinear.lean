import Mathlib
import OAI.Probability.SKBarriers.Scalar.TiltedDirectionalMoment
import OAI.Probability.SKBarriers.Scalar.WindowIntegral

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fiberGaussian_linear_error_lipschitz (n : ℕ) (V F : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hFc : ContDiff ℝ 1 F) (hFg : HasExpGrowth F)
    (hFdg : HasExpGrowth (fderiv ℝ F)) (hFb : ∀ z, |F z|≤1)
    {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g) (hb : ∀ y, |g y|≤1)
    (L : ParameterSpace n →L[ℝ] ℝ) (x : ℝ) (a : Fin n → ℝ)
    (hinv : L (coordinateVector n a)=0) (ε : ℝ)
    (hscore : ∀ z, |fderiv ℝ V z (coordinateVector n a)|≤ε) :
    |(∫ z, coordinateLinear n a z*F z*g (L z) ∂(fiberGaussian n x).tilted V)-
      (∫ z, fderiv ℝ F z (coordinateVector n a)*g (L z) ∂(fiberGaussian n x).tilted V)|≤ε := by
  let μ := (fiberGaussian n x).tilted V
  let := fiberGaussian_tilted_probability n V hV x
  let D : ParameterSpace n → ℝ := fun z => fderiv ℝ F z (coordinateVector n a)
  have hDc : Continuous D := (hFc.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDg : HasExpGrowth D := hFdg.derivative_eval _
  have hDint : Integrable D μ := hDg.integrable_tilted_fiberGaussian n V hV hDc x
  have hLFint : Integrable (fun z => coordinateLinear n a z*F z) μ :=
    ((HasExpGrowth.linear _).mul hFg).integrable_tilted_fiberGaussian n V hV
      ((coordinateLinear n a).continuous.mul hFc.continuous) x
  have Hlim₁ := scalarWindow_integral_tendsto hg hb L.measurable hLFint
  have Hlim₂ := scalarWindow_integral_tendsto hg hb L.measurable hDint
  have HI (k : ℕ) : |(∫ z, coordinateLinear n a z*F z*scalarWindow g (1/((k:ℝ)+1)) (L z) ∂μ)-
      (∫ z, D z*scalarWindow g (1/((k:ℝ)+1)) (L z) ∂μ)|≤ε := by
    let h : ℝ := 1/((k:ℝ)+1)
    have hh : 0<h := by dsimp [h]; positivity
    let G : ParameterSpace n → ℝ := fun z => scalarWindow g h (L z)
    have hGc : ContDiff ℝ 1 G := (scalarWindow_contDiff hg.continuous h).comp L.contDiff
    have hGgrow := scalarWindow_comp_growth hg.continuous (B:=1) hb hh L
    have hGb (z) : |G z|≤1 := scalarWindow_bound hg.continuous (B:=1) hb hh (L z)
    have hGi : TranslationInvariant G (coordinateVector n a) := by
      intro z t
      simp only [G,map_add,map_smul,hinv,smul_zero,add_zero]
    have hd (z) : fderiv ℝ (fun z => F z*G z) z (coordinateVector n a)=D z*G z := by
      rw [fderiv_fun_mul (hFc.differentiable (by norm_num) z) (hGc.differentiable (by norm_num) z)]
      simp only [add_apply,smul_apply,smul_eq_mul,
        hGi.fderiv_zero (hGc.differentiable (by norm_num)) z,mul_zero,zero_add,D,mul_comm]
    have H := fiberGaussian_tilted_directional_stein n V (fun z => F z*G z) hV
      (hFc.mul hGc) (hFg.mul hGgrow.1)
      (HasExpGrowth.fderiv_mul (hFc.differentiable (by norm_num))
        (hGc.differentiable (by norm_num)) hFg hGgrow.1 hFdg hGgrow.2) x a
    simp_rw [hd] at H
    have he : (fun z => coordinateLinear n a z*(F z*G z))=
        fun z => coordinateLinear n a z*F z*G z := by funext z; ring
    rw [he] at H
    change (∫ z, coordinateLinear n a z*F z*G z ∂μ)=
      (∫ z, D z*G z ∂μ)+∫ z, F z*G z*fderiv ℝ V z (coordinateVector n a) ∂μ at H
    change |(∫ z, coordinateLinear n a z*F z*G z ∂μ)-(∫ z, D z*G z ∂μ)|≤ε
    rw [H,add_sub_cancel_left]
    have Hb := norm_integral_le_of_norm_le_const (μ:=μ)
      (f:=fun z => F z*G z*fderiv ℝ V z (coordinateVector n a))
      (C:=ε) (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_mul,abs_mul]
        have hFG : |F z| * |G z|≤1 :=
          (mul_le_mul (hFb z) (hGb z) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
        exact (mul_le_mul hFG (hscore z) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)))
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using Hb
  exact le_of_tendsto (Hlim₁.sub Hlim₂).abs (Eventually.of_forall HI)

end SK.Analytic

end
end

end OAI
