import Mathlib

namespace OAI
noncomputable section
open Set Filter InnerProductSpace
open scoped ContDiff Laplacian Topology
namespace FlatRadial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
def lift (f : ℝ → ℝ) (x : V) : ℝ := f (‖x‖^2)
def L (m : ℕ) (f : ℝ → ℝ) (y : ℝ) : ℝ := 4*y*deriv (deriv f) y+2*m*deriv f y
lemma lift_fderiv (f : ℝ → ℝ) (x : V) (hf : DifferentiableAt ℝ f (‖x‖^2)) :
    fderiv ℝ (lift f) x=(2*deriv f (‖x‖^2)) • innerSL ℝ x := by
  have hh := hf.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_id x).norm_sq
  change fderiv ℝ (f ∘ fun y : V => ‖id y‖^2) x=_
  rw [hh.fderiv]
  ext v
  simp [smul_eq_mul]
  ring
lemma second_lift (f : ℝ → ℝ) (x v : V) (hf : ContDiffAt ℝ 2 f (‖x‖^2)) :
    iteratedFDeriv ℝ 2 (lift f) x ![v,v] =
      4*deriv (deriv f) (‖x‖^2)*(inner ℝ x v)^2+2*deriv f (‖x‖^2)*‖v‖^2 := by
  have hfc : ContDiffAt ℝ 2 (lift (V := V) f) x := hf.comp x (contDiff_norm_sq ℝ).contDiffAt
  have hdfc : ContDiffAt ℝ 1 (deriv f) (‖x‖^2) :=
    (hf.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).clm_apply contDiffAt_const
  have hdf := hdfc.differentiableAt (by norm_num : (1:ℕ∞ω)≠0)
  have he : (fun y : V => fderiv ℝ (lift f) y v)=ᶠ[𝓝 x]
      (fun y => (2*deriv f (‖y‖^2))*inner ℝ y v) := by
    have hdnear := hf.eventually (by norm_num : (2:ℕ∞ω)≠∞)
    have hnear := (contDiff_norm_sq ℝ (n := 2)).continuous.continuousAt.eventually hdnear
    filter_upwards [hnear] with y hy
    rw [lift_fderiv f y (hy.differentiableAt (by norm_num))]
    rfl
  have hd1 := hdf.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_id x).norm_sq
  have hd2 : HasFDerivAt (fun y : V => inner ℝ y v) (innerSL ℝ v) x := by
    convert (innerSL ℝ v).hasFDerivAt using 1
    ext y
    exact (real_inner_comm y v).symm
  have hd := (hd1.const_mul 2).mul hd2
  change HasFDerivAt (fun y : V => 2*deriv f (‖y‖^2)*inner ℝ y v) _ x at hd
  have hfe := he.fderiv_eq (𝕜 := ℝ)
  have hEval := ((hfc.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  rw [iteratedFDeriv_two_apply]
  have hk : ((fderiv ℝ (fderiv ℝ (lift f)) x) v) v =
      fderiv ℝ (fun y => fderiv ℝ (lift f) y v) x v := by
    rw [hEval.fderiv]
    simp
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [hk,hfe,hd.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul,real_inner_self_eq_norm_sq]
  simp only [Function.comp_apply,id_eq,real_inner_comm v x]
  ring
variable [FiniteDimensional ℝ V]

lemma laplacian_lift (f : ℝ → ℝ) (x : V) (hf : ContDiffAt ℝ 2 f (‖x‖^2)) :
    Δ (lift (V := V) f) x=L (Module.finrank ℝ V) f (‖x‖^2) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [second_lift f x _ hf,(stdOrthonormalBasis ℝ V).norm_eq_one,
    one_pow,mul_one,Finset.sum_add_distrib,←Finset.mul_sum]
  have hs : (∑ i, (inner ℝ x (stdOrthonormalBasis ℝ V i))^2)=‖x‖^2 := by
    simpa only [real_inner_comm (stdOrthonormalBasis ℝ V _) x,←pow_two,real_inner_self_eq_norm_sq] using
      (stdOrthonormalBasis ℝ V).sum_inner_mul_inner x x
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,L]
  ring
end FlatRadial

end

end OAI
