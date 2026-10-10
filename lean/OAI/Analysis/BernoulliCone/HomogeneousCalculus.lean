import OAI.Analysis.BernoulliCone.PositiveQuotient

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.ConeCalculus
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma euler_identity {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hom : ∀ r : ℝ, 0 < r → ∀ y, f (r • y) = r*f y) :
    fderiv ℝ f x x = f x := by
  have hc : HasDerivAt (fun r : ℝ => f (r • x)) (fderiv ℝ f x x) 1 := by
    have hf1 : HasFDerivAt f (fderiv ℝ f x) ((fun r : ℝ => r • x) 1) := by simpa using hf.hasFDerivAt
    convert! hf1.comp_hasDerivAt 1 ((hasDerivAt_id (1:ℝ)).smul_const x) using 1
    simp
  have he : (fun r : ℝ => f (r • x)) =ᶠ[𝓝 1] (fun r => r*f x) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0:ℝ)<1)] with r hr
    exact hom r hr x
  apply hc.unique
  simpa using (((hasDerivAt_id (1:ℝ)).mul_const (f x)).congr_of_eventuallyEq he)

/-- Euler's homogeneous identity differentiated on the actual open smooth
phase. No Hessian or angular equation is assumed. -/
lemma hessian_radial {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O)
    (hom : ∀ r : ℝ, 0 < r → ∀ y, f (r • y) = r*f y)
    {x : E} (hx : x∈O) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v x = 0 := by
  have hs := hf.contDiffAt (hO.mem_nhds hx)
  have hd := hs.differentiableAt (by simp)
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hs.fderiv_right (m:=1) (by change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞); exact WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp)
  have he : (fun y => fderiv ℝ f y y) =ᶠ[𝓝 x] f := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact euler_identity ((hf.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)) hom
  have hh := (hD.hasFDerivAt.clm_apply (hasFDerivAt_id x)).congr_of_eventuallyEq he.symm
  have heq := congrArg (fun A : E →L[ℝ] ℝ => A v) (hh.unique hd.hasFDerivAt)
  simp only [add_apply,ContinuousLinearMap.coe_comp,
    Function.comp_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.flip_apply,id_eq] at heq
  linarith

variable {d : ℕ}

lemma laplacian_trace (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    Laplacian.laplacian f x = ∑ i, fderiv ℝ (fderiv ℝ f) x
      (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp [iteratedFDeriv_two_apply]
end Bernoulli.ConeCalculus

end
end

end OAI
