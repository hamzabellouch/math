import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyJointMoment
import OAI.Probability.SKBarriers.Gaussian.GaussianGrowth
import OAI.Probability.SKBarriers.Gaussian.GaussianIntegration
import OAI.Probability.SKBarriers.Gaussian.GaussianSecondStep

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

theorem fiberGaussian_stein (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : HasExpGrowth f) (hg' : HasExpGrowth (fderiv ℝ f))
    (x : ℝ) (i : Fin n) :
    (∫ z, coordinateProjection n i z*f z ∂fiberGaussian n x) =
      ∫ z, fderiv ℝ f z (coordinateAxis n i) ∂fiberGaussian n x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hleft (i : Fin (n+1)) : Integrable (fun z => coordinateProjection (n+1) i z*f z)
        (fiberGaussian (n+1) x) :=
      ((HasExpGrowth.linear _).mul hg).integrable_fiberGaussian (n+1)
        ((coordinateProjection (n+1) i).continuous.mul hf.continuous) x
    have hright (i : Fin (n+1)) : Integrable (fun z => fderiv ℝ f z (coordinateAxis (n+1) i))
        (fiberGaussian (n+1) x) :=
      (hg'.derivative_eval _).integrable_fiberGaussian (n+1)
        ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const) x
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hl := hleft (Fin.last n)
      have hr := hright (Fin.last n)
      simp only [coordinateAxis_last] at hr ⊢
      rw [fiberGaussian,integral_prod _ hl,integral_prod _ hr]
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [coordinateProjection,Fin.lastCases_last,ContinuousLinearMap.coe_snd']
      have hd (y : ℝ) : HasDerivAt (fun y => f (z,y)) (fderiv ℝ f (z,y) (0,1)) y := by
        exact (hf.differentiable (by norm_num) (z,y)).hasFDerivAt.comp_hasDerivAt y
          ((hasDerivAt_const y z).prodMk (hasDerivAt_id y))
      apply gaussian_integral_mul_eq_integral_deriv _ _ hd
        (hg.integrable_gaussian_section hf.continuous z)
      · exact (hg'.derivative_eval (0,1)).integrable_gaussian_section
          ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const) z
      · simpa only [coordinateProjection,Fin.lastCases_last,ContinuousLinearMap.coe_snd'] using
          ((HasExpGrowth.linear (coordinateProjection (n+1) (Fin.last n))).mul hg).integrable_gaussian_section
              ((coordinateProjection (n+1) (Fin.last n)).continuous.mul hf.continuous) z
    · have hl := hleft j.castSucc
      have hr := hright j.castSucc
      simp only [coordinateAxis_castSucc] at hr ⊢
      rw [fiberGaussian,integral_prod_symm _ hl,integral_prod_symm _ hr]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [coordinateProjection,Fin.lastCases_castSucc,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst']
      have hc : ContDiff ℝ 1 (fun z : ParameterSpace n => f (z,y)) :=
        hf.comp (contDiff_id.prodMk contDiff_const)
      have he : fderiv ℝ (fun z : ParameterSpace n => f (z,y)) =
          fun z => leftRestrict (fderiv ℝ f (z,y)) := by
        funext z
        exact (leftRestrict_hasFDerivAt f (hf.differentiable (by norm_num)) z y).fderiv
      have hcg : HasExpGrowth (fderiv ℝ (fun z : ParameterSpace n => f (z,y))) := by
        rw [he]
        exact (hg'.congr_bound zero_le_one (fun point =>
          (leftRestrict_apply_bound (fderiv ℝ f point)).trans_eq (one_mul _).symm)).section_right y
      have H := ih (fun z => f (z,y)) hc (hg.section_right y) hcg j
      simpa only [he,leftRestrict,ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply] using H

theorem fiberGaussian_tilted_stein (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) (i : Fin n) :
    (∫ z, coordinateProjection n i z ∂(fiberGaussian n x).tilted V) =
      ∫ z, fderiv ℝ V z (coordinateAxis n i) ∂(fiberGaussian n x).tilted V := by
  obtain ⟨hg,hg',hg''⟩ := hV.exp_growths 1
  simp only [one_mul] at hg hg' hg''
  have H := fiberGaussian_stein n (fun z => Real.exp (V z))
    (hV.1.exp.of_le (by norm_num)) hg hg' x i
  simp_rw [((hV.1.differentiable (by norm_num) _).hasFDerivAt.exp).fderiv,
    smul_apply,smul_eq_mul] at H
  simp only [integral_tilted_real_eq_div]
  congr 1
  rw [H]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

end SK.Analytic

end
end
end
end
end
end
end

end OAI
