import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusFourierSmooth

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def expCosLinear (L K : E →L[ℝ] ℝ) (p : ℝ) (x : E) : ℝ := exp (L x)*cos (K x+p)

lemma expCosLinear_deriv (L K : E →L[ℝ] ℝ) (p : ℝ) (x : E) :
    HasFDerivAt (expCosLinear L K p)
      (expCosLinear L K p x • L + expCosLinear L K (p+Real.pi/2) x • K) x := by
  have hh := (L.hasFDerivAt (x := x)).exp.mul ((K.hasFDerivAt.add_const p).cos)
  convert hh using 1 <;> ext v <;>
    simp [smul_eq_mul,expCosLinear,Pi.mul_apply,←add_assoc,cos_add_pi_div_two]
  ring

lemma expCosLinear_fderiv (L K : E →L[ℝ] ℝ) (p : ℝ) (x v : E) :
    fderiv ℝ (expCosLinear L K p) x v =
      expCosLinear L K p x*L v+expCosLinear L K (p+Real.pi/2) x*K v := by
  rw [(expCosLinear_deriv L K p x).fderiv]
  rfl

lemma expCosLinear_hessian (L K : E →L[ℝ] ℝ) (p : ℝ) (x v w : E) :
    (iteratedFDeriv ℝ 2 (expCosLinear L K p) x) ![v,w] =
      (L v*L w-K v*K w)*expCosLinear L K p x+
      (L v*K w+K v*L w)*expCosLinear L K (p+Real.pi/2) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (expCosLinear L K p)) x := by
    have hc : ContDiff ℝ 2 (expCosLinear L K p) := by unfold expCosLinear; fun_prop
    exact (hc.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have he := fderiv_clm_apply (c := fderiv ℝ (expCosLinear L K p)) hd
    (differentiableAt_const (c := w))
  have hfun : (fun y => fderiv ℝ (expCosLinear L K p) y w)=
      fun y => expCosLinear L K p y*L w+expCosLinear L K (p+Real.pi/2) y*K w := by
    funext y
    exact expCosLinear_fderiv L K p y w
  rw [hfun] at he
  have hh := ((expCosLinear_deriv L K p x).mul_const (L w)).add
    ((expCosLinear_deriv L K (p+Real.pi/2) x).mul_const (K w))
  have hhe := hh.fderiv
  change fderiv ℝ (fun y => expCosLinear L K p y*L w+
    expCosLinear L K (p+Real.pi/2) y*K w) x=_ at hhe
  rw [hhe] at he
  have hv := congrArg (fun A : E →L[ℝ] ℝ => A v) he
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,
    ContinuousLinearMap.flip_apply,add_apply,smul_apply,
    smul_eq_mul] at hv
  rw [←hv]
  have hp : p+Real.pi/2+Real.pi/2=p+Real.pi := by ring
  simp only [expCosLinear,hp,←add_assoc,cos_add_pi]
  ring

def flatAxis (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

def flatTensorLaplacianCLM (s : Fin 3 → ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Fin 3 → ℝ) ℝ →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ _ ℝ ![flatAxis 0,flatAxis 0]+
  s 0 • ContinuousMultilinearMap.apply ℝ _ ℝ ![flatAxis 1,flatAxis 1]+
  (2*s 1) • ContinuousMultilinearMap.apply ℝ _ ℝ ![flatAxis 1,flatAxis 2]+
  s 2 • ContinuousMultilinearMap.apply ℝ _ ℝ ![flatAxis 2,flatAxis 2]

def flatTensorLaplacian (s : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  flatTensorLaplacianCLM s (iteratedFDeriv ℝ 2 f x)

lemma flatPhaseMode_harmonic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (h : Fin 2 → ℤ) (p : ℝ) (x : Fin 3 → ℝ) :
    flatTensorLaplacian s (flatPhaseMode s h p) x=0 := by
  let L : (Fin 3 → ℝ) →L[ℝ] ℝ := -torusRate s h • ContinuousLinearMap.proj 0
  have hf : flatPhaseMode s h p=expCosLinear L (torusAngular h) p := rfl
  have hsq : torusRate s h^2=torusQuadratic s h := by
    apply sq_sqrt
    exact (by positivity : 0≤(1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2)).trans (hs _ _)
  rw [flatTensorLaplacian,hf]
  simp only [flatTensorLaplacianCLM,add_apply,
    smul_apply,ContinuousMultilinearMap.apply_apply,smul_eq_mul,
    expCosLinear_hessian]
  simp only [L,torusAngular,add_apply,smul_apply,
    ContinuousLinearMap.proj_apply,flatAxis,Pi.single_apply,smul_eq_mul]
  simp only [show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide,
    show (2:Fin 3)≠1 by decide,show (2:Fin 3)≠0 by decide,
    show (0:Fin 3)≠1 by decide,show (1:Fin 3)≠0 by decide,
    ite_true,ite_false,mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero,
    zero_sub,neg_mul,neg_neg,mul_neg]
  dsimp [torusQuadratic] at hsq
  have hm := congrArg (fun r => r*expCosLinear L (torusAngular h) p x) hsq
  dsimp [L,torusAngular] at hm
  linear_combination hm

lemma weighted_flatPhaseMode_harmonic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (h : Fin 2 → ℤ) (p a : ℝ) (x : Fin 3 → ℝ) :
    flatTensorLaplacian s (fun y => a*flatPhaseMode s h p y) x=0 := by
  change flatTensorLaplacianCLM s (iteratedFDeriv ℝ 2 (a • flatPhaseMode s h p) x)=0
  rw [iteratedFDeriv_const_smul_apply
    (((contDiff_infty.mp (flatPhaseMode_smooth s h p)) 2).contDiffAt),map_smul]
  change a • flatTensorLaplacian s (flatPhaseMode s h p) x=0
  rw [flatPhaseMode_harmonic hs,smul_zero]

theorem flatFourier_harmonic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B)
    {x : Fin 3 → ℝ} (hx : 0<x 0) :
    flatTensorLaplacian s (flatFourier s a phase) x=0 := by
  have hb := (flatMode_derivative_summable hs 2 hx).mul_left B
  have hn : Summable (fun h => ‖iteratedFDeriv ℝ 2
      (fun y => a h*flatPhaseMode s h (phase h) y) x‖) :=
    Summable.of_nonneg_of_le (fun h => norm_nonneg _)
      (fun h => weighted_phase_halfspace_bound ha 2 h le_rfl) hb
  rw [flatTensorLaplacian,flatFourier_iterated hs ha 2 hx,
    (flatTensorLaplacianCLM s).map_tsum hn.of_norm]
  have hz (h : Fin 2 → ℤ) : flatTensorLaplacianCLM s (iteratedFDeriv ℝ 2
      (fun y => a h*flatPhaseMode s h (phase h) y) x)=0 :=
    weighted_flatPhaseMode_harmonic hs h (phase h) (a h) x
  simp only [hz,tsum_zero]

end ScalarConductivity

end

end OAI
