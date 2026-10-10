import Mathlib
import OAI.Probability.SKBarriers.Scalar.RawDerivatives
import OAI.Probability.SKBarriers.Gaussian.GaussianLogStep
import OAI.Probability.SKBarriers.Gaussian.LogIntegralConvexity
import OAI.Probability.SKBarriers.Gaussian.ExponentialDerivatives

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
namespace SK.Analytic
section SmoothRecursion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def BoundedDerivs (f : E → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
    (∀ x, ‖fderiv ℝ f x‖ ≤ C) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ D)

theorem BoundedDerivs.const_mul {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) :
    BoundedDerivs (fun x => m*f x) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := hf
  have hd := hf.differentiable (by norm_num)
  have he : fderiv ℝ (fun x => m*f x) = fun x => m • fderiv ℝ f x := by
    funext x
    exact ((hd x).hasFDerivAt.const_mul m).fderiv
  refine ⟨contDiff_const.mul hf, |m| * C, |m| * D,
    mul_nonneg (abs_nonneg _) hC, mul_nonneg (abs_nonneg _) hD, ?_, ?_⟩
  · intro x
    rw [he, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
  · intro x
    rw [he]
    change ‖fderiv ℝ (m • fderiv ℝ f) x‖ ≤ |m| * D
    rw [((hf.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) x).hasFDerivAt.const_smul m |>.fderiv]
    exact (ContinuousLinearMap.opNorm_smul_le _ _).trans (by
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbb x) (abs_nonneg _))

theorem BoundedDerivs.exp_smooth_integral {f : E × ℝ → ℝ} (hf : BoundedDerivs f) :
    ContDiff ℝ 2 (fun x => ∫ y, Real.exp (f (x,y)) ∂gaussianReal 0 1) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := hf
  have hg : HasExpGrowth (fun x => Real.exp (f x)) := by
    simpa only [one_mul] using
      exp_mul_growth_of_fderiv_bound f (hf.differentiable (by norm_num)) C hC hb 1
  exact contDiff_two_gaussian_integral_fderiv _ hf.exp hg
    (fderiv_exp_growth f (hf.differentiable (by norm_num)) hg hC hb)
    (fderiv_fderiv_exp_growth f hf hg hC hD hb hbb)

theorem BoundedDerivs.positiveGaussianLogStep_smooth {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (m : ℝ) :
    ContDiff ℝ 2 (positiveGaussianLogStep m f) := by
  obtain ⟨hfd,C,D,hC,hD,hb,hbb⟩ := hf
  have hs := (BoundedDerivs.const_mul ⟨hfd,C,D,hC,hD,hb,hbb⟩ m).exp_smooth_integral
  apply (hs.log _).div_const
  intro x
  exact (positiveGaussianLogStep_partition_pos f (hfd.differentiable (by norm_num)) C hC hb m x).ne'

theorem positiveGaussianLogStep_convex {f : E × ℝ → ℝ} (hc : ConvexOn ℝ univ f)
    (hd : Differentiable ℝ f) (C : ℝ) (hC₀ : 0 ≤ C)
    (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) {m : ℝ} (hm : 0 < m) :
    ConvexOn ℝ univ (positiveGaussianLogStep m f) := by
  have hi : ∀ x, Integrable (fun y => Real.exp (m*f (x,y))) (gaussianReal 0 1) :=
    (exp_mul_growth_of_fderiv_bound f hd C hC₀ hC m).integrable_gaussian_section
      (Real.continuous_exp.comp (continuous_const.mul hd.continuous))
  have hcx : ∀ y, ConvexOn ℝ univ (fun x => m*f (x,y)) := by
    intro y
    refine ⟨convex_univ, ?_⟩
    intro x _ z _ a b ha hb hab
    have hh := hc.2 (mem_univ (x,y)) (mem_univ (z,y)) ha hb hab
    have he : a • (x,y)+b • (z,y) = (a • x+b • z,y) := by
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
        smul_eq_mul]
      rw [← add_mul, hab, one_mul]
    rw [he] at hh
    simp only [smul_eq_mul] at hh ⊢
    nlinarith [mul_le_mul_of_nonneg_left hh hm.le]
  have hg := convexOn_log_integral_exp (gaussianReal 0 1) (fun x y => m*f (x,y)) hi hcx
  have hi := hg.smul (inv_nonneg.mpr hm.le)
  change ConvexOn ℝ univ (fun x => Real.log
    (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1) / m)
  simpa only [div_eq_mul_inv, mul_comm, smul_eq_mul] using hi

end SmoothRecursion
end SK.Analytic

end
end
end
end
end
end

end OAI
