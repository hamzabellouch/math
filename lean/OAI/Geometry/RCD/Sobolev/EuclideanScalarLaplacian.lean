import OAI.Geometry.RCD.Metric.EuclideanGreenIdentity

namespace OAI

/-! # The scalar chain rule needed for compact interior torsion tests -/

open Set Metric MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff BigOperators
noncomputable section
namespace RegularPointCoordinates

theorem scalar_comp_fderiv_apply {n : ℕ} {F : ℝ → ℝ} {g : Euclidean n → ℝ}
    {x : Euclidean n} (hg : DifferentiableAt ℝ g x)
    (hF : DifferentiableAt ℝ F (g x)) (v : Euclidean n) :
    fderiv ℝ (fun z => F (g z)) x v=deriv F (g x)*fderiv ℝ g x v := by
  have h := hF.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt
  simpa only [Function.comp_def,smul_apply,smul_eq_mul] using congrArg (fun L : Euclidean n →L[ℝ] ℝ => L v) h.fderiv

theorem laplacian_scalar_comp {n : ℕ} {F : ℝ → ℝ} {g : Euclidean n → ℝ}
    (hF : ContDiff ℝ 2 F) (hg : ContDiff ℝ 2 g) (x : Euclidean n) :
    (Δ (fun z => F (g z))) x=deriv (deriv F) (g x)*
      (∑ i : Fin n, (fderiv ℝ g x (EuclideanSpace.single i 1))^2)+deriv F (g x)*(Δ g) x := by
  have hd (z v : Euclidean n) : fderiv ℝ (fun y => F (g y)) z v=
      deriv F (g z)*fderiv ℝ g z v :=
    scalar_comp_fderiv_apply (hg.differentiable (by norm_num) z) (hF.differentiable (by norm_num) _) v
  have hFd : Differentiable ℝ (deriv F) := hF.differentiable_deriv_two
  have hdd (v : Euclidean n) : fderiv ℝ (fun z => fderiv ℝ (fun y => F (g y)) z v) x v=
      deriv (deriv F) (g x)*(fderiv ℝ g x v)^2+
        deriv F (g x)*fderiv ℝ (fun z => fderiv ℝ g z v) x v := by
    simp_rw [hd]
    have hgd : ContDiff ℝ 1 (fun z => fderiv ℝ g z v) :=
      (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hFdcomp : DifferentiableAt ℝ (fun z => deriv F (g z)) x := by
      simpa only [Function.comp_def] using (hFd (g x)).comp x (hg.differentiable (by norm_num) x)
    rw [fderiv_fun_mul hFdcomp
      (hgd.differentiable (by norm_num) x)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [scalar_comp_fderiv_apply (hg.differentiable (by norm_num) x) (hFd _)]
    ring
  have hFc : ContDiff ℝ 2 (fun z => F (g z)) := by
    simpa only [Function.comp_def] using hF.comp hg
  rw [laplacian_eq_sum_second_directional hFc,laplacian_eq_sum_second_directional hg]
  simp_rw [hdd]
  rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]

end RegularPointCoordinates

end

end OAI
