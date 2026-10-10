import OAI.Analysis.BernoulliCone.LowerSupport

namespace OAI

universe uE

section
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.ScalarLaplacian
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma deriv2_mul {f g : ℝ → ℝ} {t:ℝ}
    (hf:ContDiffAt ℝ 2 f t) (hg:ContDiffAt ℝ 2 g t) :
    deriv (deriv (fun s=>f s*g s)) t =
      deriv (deriv f) t*g t+2*deriv f t*deriv g t+f t*deriv (deriv g) t := by
  have hf' := (hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hg' := (hg.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have he : deriv (fun s=>f s*g s) =ᶠ[𝓝 t] fun s=>deriv f s*g s+f s*deriv g s := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with s hs ht
    exact deriv_mul (hs.differentiableAt (by norm_num)) (ht.differentiableAt (by norm_num))
  rw [he.deriv_eq]
  have hh := (hf'.hasDerivAt.mul (hg.differentiableAt (by norm_num)).hasDerivAt).add
    ((hf.differentiableAt (by norm_num)).hasDerivAt.mul hg'.hasDerivAt)
  change deriv (deriv f*g+f*deriv g) t = _
  rw [hh.deriv]
  ring

lemma line_deriv {f:E→ℝ} {x:E} (hf:DifferentiableAt ℝ f x) (v:E) :
    deriv (fun t:ℝ=>f (x+t • v)) 0 = inner ℝ (gradient f x) v := by
  have hl : HasDerivAt (fun t:ℝ=>x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hfx : HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • v) := by simpa using hf.hasFDerivAt
  simpa only [Function.comp_def,inner_gradient_left] using (hfx.comp_hasDerivAt 0 hl).deriv

lemma gradient_mul {f g:E→ℝ} {x:E} (hf:DifferentiableAt ℝ f x)
    (hg:DifferentiableAt ℝ g x) :
    gradient (fun y=>f y*g y) x = g x • gradient f x + f x • gradient g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_add_left,real_inner_smul_left,real_inner_smul_left,inner_gradient_left,
    inner_gradient_left,inner_gradient_left]
  change (fderiv ℝ (f*g) x) v = _
  rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma gradient_comp {φ:ℝ→ℝ} {f:E→ℝ} {x:E} (hφ:DifferentiableAt ℝ φ (f x))
    (hf:DifferentiableAt ℝ f x) :
    gradient (fun y=>φ (f y)) x = deriv φ (f x) • gradient f x := by
  apply ext_inner_right ℝ
  intro v
  change inner ℝ (gradient (φ ∘ f) x) v = _
  rw [inner_gradient_left,fderiv_comp x hφ hf,ContinuousLinearMap.comp_apply,
    fderiv_eq_deriv_mul,real_inner_smul_left,inner_gradient_left]

lemma laplacian_sum_line {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x) :
    Δ f x = ∑ i, deriv (deriv (fun t:ℝ=>f (x+t • stdOrthonormalBasis ℝ E i))) 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_two_apply]
  simp only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp_rw [Axisymmetric.line_second_derivative hf]

lemma laplacian_mul {f g:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x)
    (hg:ContDiffAt ℝ 2 g x) :
    Δ (fun y=>f y*g y) x = g x*Δ f x+2*inner ℝ (gradient f x) (gradient g x)+f x*Δ g x := by
  let b := stdOrthonormalBasis ℝ E
  have hfL (v:E) : ContDiffAt ℝ 2 (fun t:ℝ=>f (x+t • v)) 0 := by
    have hh : ContDiffAt ℝ 2 (fun t:ℝ=>x+t • v) 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    exact (show ContDiffAt ℝ 2 f (x+(0:ℝ) • v) by simpa using hf).comp 0 hh
  have hgL (v:E) : ContDiffAt ℝ 2 (fun t:ℝ=>g (x+t • v)) 0 := by
    have hh : ContDiffAt ℝ 2 (fun t:ℝ=>x+t • v) 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    exact (show ContDiffAt ℝ 2 g (x+(0:ℝ) • v) by simpa using hg).comp 0 hh
  rw [laplacian_sum_line (hf.mul hg),laplacian_sum_line hf,laplacian_sum_line hg]
  simp_rw [deriv2_mul (hfL _) (hgL _),zero_smul,add_zero,
    line_deriv (hf.differentiableAt (by norm_num)),line_deriv (hg.differentiableAt (by norm_num))]
  simp_rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,mul_assoc]
  have hc : (∑ i,inner ℝ (gradient f x) (b i)*inner ℝ (gradient g x) (b i))=
      inner ℝ (gradient f x) (gradient g x) := by
    convert b.sum_inner_mul_inner (gradient f x) (gradient g x) using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm (gradient g x) (b i)]
  dsimp only [b] at hc
  rw [←Finset.mul_sum,hc]
  ring

lemma laplacian_comp {φ:ℝ→ℝ} {f:E→ℝ} {x:E} (hφ:ContDiffAt ℝ 2 φ (f x))
    (hf:ContDiffAt ℝ 2 f x) :
    Δ (fun y=>φ (f y)) x = deriv (deriv φ) (f x)*‖gradient f x‖^2 + deriv φ (f x)*Δ f x := by
  let b := stdOrthonormalBasis ℝ E
  have he (v:E) : deriv (deriv (fun t:ℝ=>φ (f (x+t • v)))) 0 =
      deriv (deriv φ) (f x)*(inner ℝ (gradient f x) v)^2+
        deriv φ (f x)*deriv (deriv (fun t:ℝ=>f (x+t • v))) 0 := by
    have hfL : ContDiffAt ℝ 2 (fun t:ℝ=>f (x+t • v)) 0 := by
      have hh : ContDiffAt ℝ 2 (fun t:ℝ=>x+t • v) 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
      exact (show ContDiffAt ℝ 2 f (x+(0:ℝ) • v) by simpa using hf).comp 0 hh
    have hh := iteratedDeriv_comp_two (show ContDiffAt ℝ 2 φ (f (x+(0:ℝ) • v)) by simpa using hφ) hfL
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_def,zero_smul,add_zero,
      line_deriv (hf.differentiableAt (by norm_num))] using hh
  change Δ (φ ∘ f) x = _
  rw [laplacian_sum_line (hφ.comp x hf),laplacian_sum_line hf]
  simp only [Function.comp_apply]
  simp_rw [he,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [b.sum_sq_inner_left]
end Bernoulli.ScalarLaplacian

end
end

end OAI
