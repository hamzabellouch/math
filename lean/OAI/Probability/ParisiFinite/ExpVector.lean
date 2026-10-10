import Mathlib
import OAI.Probability.ParisiFinite.GramPosSemidef

namespace OAI

/-! Exp Vector. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
namespace CoherentFock
open scoped Interval
open Complex MeasureTheory
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

def expVector (d : E) : Space E :=
  (Real.exp (‖d‖^2/2) : ℂ) • coherent d

@[simp] theorem inner_expVector (d e : E) :
    ⟪expVector d,expVector e⟫_ℂ = Complex.exp ⟪d,e⟫_ℂ := by
  simp only [expVector,inner_smul_left,inner_smul_right,inner_coherent,
    kernel]
  rw [Complex.conj_ofReal]
  simp only [Complex.ofReal_exp]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_expVector : Continuous (expVector (E := E)) :=
  ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_norm.pow 2 |>.div_const 2)))).smul continuous_coherent

@[simp] theorem expVector_zero : expVector (0 : E) = coherent 0 := by simp [expVector]

theorem eq_of_inner_coherent {x y : Space E}
    (h : ∀ d, ⟪x,coherent d⟫_ℂ = ⟪y,coherent d⟫_ℂ) : x=y := by
  have he : innerSL ℂ x = innerSL ℂ y := ext_coherent h
  exact ext_inner_right ℂ fun v => congrArg (fun f : Space E →L[ℂ] ℂ => f v) he

theorem eq_of_inner_expVector {x y : Space E}
    (h : ∀ d, ⟪expVector d,x⟫_ℂ = ⟪expVector d,y⟫_ℂ) : x=y := by
  apply eq_of_inner_coherent
  intro d
  have he := h d
  simp only [expVector,inner_smul_left,conj_ofReal] at he
  have hz : (Real.exp (‖d‖^2/2) : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero _
  have h' := mul_left_cancel₀ hz he
  simpa only [inner_conj_symm] using congrArg conj h'

theorem map_circleIntegral {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (L : F →L[ℂ] G) {f : ℂ → F} {c : ℂ} {r : ℝ} (hf : CircleIntegrable f c r) :
    L (∮ z in C(c,r), f z) = ∮ z in C(c,r), L (f z) := by
  simp only [circleIntegral]
  rw [← L.intervalIntegral_comp_comm hf.out]
  simp only [map_smul]

def oneParticle (d : E) : Space E :=
  (2*(Real.pi:ℂ)*I)⁻¹ • ∮ z in C(0,1), (1/z^2) • expVector (z • d)

theorem circleIntegrable_oneParticle_integrand (d : E) :
    CircleIntegrable (fun z : ℂ => (1/z^2) • expVector (z • d)) 0 1 := by
  apply ContinuousOn.circleIntegrable (by norm_num)
  have hscalar : ContinuousOn (fun z : ℂ => 1/z^2) (Metric.sphere 0 1) :=
    continuousOn_const.div (continuousOn_id.pow 2) fun z hz => by
      have h : ‖z‖ = 1 := by simpa [Metric.mem_sphere,dist_zero_right] using hz
      exact pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [h]; norm_num))
  exact hscalar.smul (continuous_expVector.comp (continuous_id.smul continuous_const)).continuousOn

@[simp] theorem inner_expVector_oneParticle (e d : E) :
    ⟪expVector e,oneParticle d⟫_ℂ = ⟪e,d⟫_ℂ := by
  rw [oneParticle,inner_smul_right]
  have hi := map_circleIntegral (innerSL ℂ (expVector e))
    (circleIntegrable_oneParticle_integrand d)
  simp only [innerSL_apply_apply,inner_smul_right,inner_expVector,inner_smul_right] at hi
  rw [hi]
  have hdiff : Differentiable ℂ (fun z : ℂ => Complex.exp (z*⟪e,d⟫_ℂ)) :=
    Complex.differentiable_exp.comp (differentiable_id.mul_const _)
  have hc := DifferentiableOn.deriv_eq_smul_circleIntegral (c := (0:ℂ))
    (R := (1:ℝ)) (by norm_num) hdiff.differentiableOn
  have hd : deriv (fun z : ℂ => Complex.exp (z*⟪e,d⟫_ℂ)) 0 = ⟪e,d⟫_ℂ := by
    have hh : HasDerivAt (fun z : ℂ => Complex.exp (z*⟪e,d⟫_ℂ)) ⟪e,d⟫_ℂ 0 := by
      simpa only [id_eq,zero_mul,Complex.exp_zero,one_mul] using
        (((hasDerivAt_id (0:ℂ)).mul_const ⟪e,d⟫_ℂ).cexp)
    exact hh.deriv
  simp only [sub_zero,smul_eq_mul,hd] at hc
  rw [hc]
  have hz : 2*(Real.pi:ℂ)*I ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  exact inv_mul_cancel_left₀ hz _

@[simp] theorem inner_oneParticle_expVector (d e : E) :
    ⟪oneParticle d,expVector e⟫_ℂ = ⟪d,e⟫_ℂ := by
  rw [← inner_conj_symm,inner_expVector_oneParticle,inner_conj_symm]

@[simp] theorem inner_oneParticle (d e : E) :
    ⟪oneParticle d,oneParticle e⟫_ℂ = ⟪d,e⟫_ℂ := by
  change ⟪oneParticle d,(2*(Real.pi:ℂ)*I)⁻¹ •
    ∮ z in C(0,1), (1/z^2) • expVector (z • e)⟫_ℂ = _
  rw [inner_smul_right]
  have hi := map_circleIntegral (innerSL ℂ (oneParticle d))
    (circleIntegrable_oneParticle_integrand e)
  simp only [innerSL_apply_apply,inner_smul_right,inner_oneParticle_expVector] at hi
  rw [hi]
  have hc := DifferentiableOn.deriv_eq_smul_circleIntegral (c := (0:ℂ))
    (R := (1:ℝ)) (by norm_num) (differentiable_id.mul_const ⟪d,e⟫_ℂ).differentiableOn
  have hd : deriv (fun z : ℂ => z*⟪d,e⟫_ℂ) 0 = ⟪d,e⟫_ℂ := by simp
  simp only [id_eq,sub_zero,smul_eq_mul,hd] at hc
  rw [hc]
  have hz : 2*(Real.pi:ℂ)*I ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  exact inv_mul_cancel_left₀ hz _

 

def oneParticleEmbedding : E →ₗᵢ[ℂ] Space E where
  toFun := oneParticle
  map_add' x y := by
    apply eq_of_inner_expVector
    intro d
    simp [inner_add_right]
  map_smul' z x := by
    apply eq_of_inner_expVector
    intro d
    simp [inner_smul_right]
  norm_map' d := by
    change ‖oneParticle d‖=‖d‖
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),inner_oneParticle]
    exact (norm_eq_sqrt_re_inner (𝕜 := ℂ) d).symm

@[simp] theorem oneParticle_orthogonal_vacuum (d : E) :
    ⟪coherent 0,oneParticle d⟫_ℂ = 0 := by
  rw [← expVector_zero,inner_expVector_oneParticle,inner_zero_left]

end CoherentFock

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
open Complex

@[simp] theorem norm_oneParticle (d : E) : ‖oneParticle d‖ = ‖d‖ :=
  oneParticleEmbedding.norm_map d

@[simp] theorem inner_coherent_oneParticle (e d : E) :
    ⟪coherent e,oneParticle d⟫_ℂ = (Real.exp (-‖e‖^2/2) : ℂ) * ⟪e,d⟫_ℂ := by
  have h := inner_expVector_oneParticle e d
  simp only [expVector,inner_smul_left] at h
  rw [Complex.conj_ofReal] at h
  have hex : (Real.exp (-‖e‖^2/2) : ℂ) * (Real.exp (‖e‖^2/2) : ℂ) = 1 := by
    have hs : -‖e‖^2/2+‖e‖^2/2 = 0 := by ring
    rw [← Complex.ofReal_mul,← Real.exp_add,hs,Real.exp_zero,Complex.ofReal_one]
  calc
    _ = ((Real.exp (-‖e‖^2/2) : ℂ) * (Real.exp (‖e‖^2/2) : ℂ)) *
      ⟪coherent e,oneParticle d⟫_ℂ := by rw [hex,one_mul]
    _ = _ := by rw [mul_assoc,h]

theorem W_neg_cancel (d : E) (x : Space E) : W d (W (-d) x)=x :=
  (weyl d).apply_symm_apply x

theorem inner_W_right (d : E) (x y : Space E) :
    ⟪x,W d y⟫_ℂ = ⟪W (-d) x,y⟫_ℂ := by
  calc
    _ = ⟪W d (W (-d) x),W d y⟫_ℂ := by rw [W_neg_cancel]
    _ = _ := inner_W d _ _

theorem inner_coherent_W_oneParticle (e d v : E) :
    ⟪coherent e,W d (oneParticle v)⟫_ℂ = kernel e d * ⟪e-d,v⟫_ℂ := by
  rw [inner_W_right,W_coherent,inner_smul_left,inner_coherent_oneParticle]
  rw [kernel_eq]
  have hi := inner_im_symm (𝕜 := ℂ) d e
  change (⟪d,e⟫_ℂ).im = -(⟪e,d⟫_ℂ).im at hi
  have he : -d+e = e-d := by abel
  rw [he]
  simp only [phase,inner_neg_left,Complex.neg_im,hi,neg_neg,
    ← Complex.exp_conj,Complex.ofReal_exp,map_mul,Complex.conj_ofReal,
    Complex.conj_I]
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

 

def fieldCoherent (v d : E) : Space E :=
  (-I) • W d (oneParticle v) - ((2*(⟪v,d⟫_ℂ).im : ℝ) : ℂ) • coherent d

theorem inner_coherent_field (e v d : E) :
    ⟪coherent e,fieldCoherent v d⟫_ℂ =
      I * (⟪v,d⟫_ℂ-⟪e,v⟫_ℂ) * kernel e d := by
  simp only [fieldCoherent,inner_sub_right,inner_smul_right,
    inner_coherent_W_oneParticle,inner_coherent,inner_sub_left]
  have hi : ⟪v,d⟫_ℂ-⟪d,v⟫_ℂ = (2*(⟪v,d⟫_ℂ).im : ℂ)*I := by
    rw [← inner_conj_symm d v]
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using Complex.sub_conj ⟪v,d⟫_ℂ
  calc
    _ = (-I*⟪e,v⟫_ℂ+I*⟪d,v⟫_ℂ-((2*(⟪v,d⟫_ℂ).im : ℝ):ℂ))*kernel e d := by ring
    _ = _ := by
      congr 1
      have him : ((2*(⟪v,d⟫_ℂ).im : ℝ):ℂ) = -I*(⟪v,d⟫_ℂ-⟪d,v⟫_ℂ) := by
        rw [hi]
        push_cast
        rw [show -I*(2*(⟪v,d⟫_ℂ).im*I) = -(2*(⟪v,d⟫_ℂ).im)*(I*I) by ring, I_mul_I]
        ring
      rw [him]
      ring

theorem fieldCoherent_symmetric (e v d : E) :
    ⟪coherent e,fieldCoherent v d⟫_ℂ = ⟪fieldCoherent v e,coherent d⟫_ℂ := by
  rw [show ⟪fieldCoherent v e,coherent d⟫_ℂ = conj ⟪coherent d,fieldCoherent v e⟫_ℂ
    from (inner_conj_symm _ _).symm,inner_coherent_field,inner_coherent_field]
  have hk : conj (kernel d e) = kernel e d := by
    rw [← inner_coherent,← inner_coherent,inner_conj_symm]
  simp only [map_mul,map_sub,Complex.conj_I,inner_conj_symm,hk]
  ring

theorem norm_fieldCoherent_le (v d : E) :
    ‖fieldCoherent v d‖ ≤ ‖v‖*(1+2*‖d‖) := by
  calc
    _ ≤ ‖(-I) • W d (oneParticle v)‖+
      ‖((2*(⟪v,d⟫_ℂ).im : ℝ):ℂ) • coherent d‖ := norm_sub_le _ _
    _ = ‖v‖+2*|(⟪v,d⟫_ℂ).im| := by
      simp [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ ‖v‖+2*(‖v‖*‖d‖) := by
      have hh := (Complex.abs_im_le_norm ⟪v,d⟫_ℂ).trans (norm_inner_le_norm v d)
      linarith
    _ = _ := by ring

 
theorem fieldCoherent_weyl_shift (v d e : E) :
    phase d e • fieldCoherent v (d+e) =
      W d (fieldCoherent v e) - ((2*(⟪v,d⟫_ℂ).im : ℝ):ℂ) • W d (coherent e) := by
  have hw := congrArg (fun A : Space E →L[ℂ] Space E => A (oneParticle v)) (W_mul d e)
  simp only [ContinuousLinearMap.comp_apply,smul_apply] at hw
  simp only [fieldCoherent,map_sub,map_smul,hw,W_coherent,inner_add_right,Complex.add_im]
  push_cast
  module

end CoherentFock

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
open Complex

 
def preField (v : E) : PreSpace E →ₗ[ℂ] Space E :=
  (Finsupp.linearCombination ℂ (fieldCoherent v)).comp toFinsupp.toLinearMap

@[simp] theorem preField_basis (v d : E) : preField v (basis d) = fieldCoherent v d := by
  classical
  simp [preField,basis]

theorem preField_eq_sum (v : E) (x : PreSpace E) :
    preField v x = (toFinsupp x).sum (fun e a => a • fieldCoherent v e) := rfl

theorem preField_symmetric (v : E) (x y : PreSpace E) :
    ⟪(↑x : Space E),preField v y⟫_ℂ = ⟪preField v x,(↑y : Space E)⟫_ℂ := by
  classical
  simp only [coe_eq_sum,preField_eq_sum,Finsupp.sum,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right]
  simp only [fieldCoherent_symmetric]

 

theorem preField_ker (v : E) {x : PreSpace E} (hx : (↑x : Space E)=0) :
    preField v x = 0 := by
  apply eq_of_inner_coherent
  intro d
  rw [inner_zero_left]
  have hh := preField_symmetric v x (basis d)
  simpa only [hx,inner_zero_left,coe_basis] using hh.symm

def spanEmbedding : PreSpace E →ₗ[ℂ] Space E :=
  UniformSpace.Completion.toComplL.toLinearMap

def fieldDomain : Submodule ℂ (Space E) := LinearMap.range (spanEmbedding (E := E))

def field (v : E) : fieldDomain (E := E) →ₗ[ℂ] Space E :=
  ((spanEmbedding (E := E)).ker.liftQ (preField v) (fun _ hx =>
    preField_ker v hx)).comp (spanEmbedding (E := E)).quotKerEquivRange.symm.toLinearMap

def inDomain (x : PreSpace E) : fieldDomain (E := E) :=
  (spanEmbedding (E := E)).rangeRestrict x

@[simp] theorem coe_inDomain (x : PreSpace E) : (inDomain x : Space E) = ↑x := rfl

@[simp] theorem field_inDomain (v : E) (x : PreSpace E) :
    field v (inDomain x) = preField v x := by
  change (spanEmbedding.ker.liftQ (preField v) (fun _ hx => preField_ker v hx))
    (spanEmbedding.quotKerEquivRange.symm ⟨spanEmbedding x,_⟩) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

theorem field_symmetric (v : E) (x y : fieldDomain (E := E)) :
    ⟪(x : Space E),field v y⟫_ℂ = ⟪field v x,(y : Space E)⟫_ℂ := by
  obtain ⟨x',hx⟩ := x.property
  obtain ⟨y',hy⟩ := y.property
  have hx' : inDomain x'=x := Subtype.ext hx
  have hy' : inDomain y'=y := Subtype.ext hy
  rw [← hx',← hy',field_inDomain,field_inDomain,coe_inDomain,coe_inDomain]
  exact preField_symmetric v x' y'

theorem preField_weyl_shift (v d : E) (x : PreSpace E) :
    preField v (preWLinear d x) = W d (preField v x) -
      ((2*(⟪v,d⟫_ℂ).im : ℝ):ℂ) • W d (↑x) := by
  classical
  let A := (preField v).comp (preWLinear d)
  let B := ((W d).toLinearMap.comp (preField v)) -
    ((2*(⟪v,d⟫_ℂ).im : ℝ):ℂ) • ((W d).toLinearMap.comp spanEmbedding)
  have hb (e : E) : A (basis e)=B (basis e) := by
    change preField v (preWLinear d (basis e)) = W d (preField v (basis e)) -
      ((2*(⟪v,d⟫_ℂ).im : ℝ):ℂ) • W d (↑(basis e))
    rw [preWLinear_basis,map_smul,preField_basis,preField_basis,coe_basis]
    exact fieldCoherent_weyl_shift v d e
  change A x=B x
  rw [← sum_basis x]
  simp only [Finsupp.sum,map_sum,map_smul,hb]

 

theorem coherent_taylor_one (d : E) :
    ‖coherent d-coherent 0-oneParticle d‖ ≤ ‖d‖^2 := by
  have hip : ⟪coherent d,oneParticle d⟫_ℂ =
      (Real.exp (-‖d‖^2/2)*‖d‖^2 : ℝ) := by
    rw [inner_coherent_oneParticle,inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hi0 : ⟪coherent 0,oneParticle d⟫_ℂ = 0 := oneParticle_orthogonal_vacuum d
  have hk : (kernel d 0).re = Real.exp (-‖d‖^2/2) := by
    unfold kernel
    simp only [norm_zero,inner_zero_right,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
      neg_zero,zero_div,Complex.ofReal_zero,add_zero]
    rw [← Complex.ofReal_exp]
    rfl
  have hn : ‖coherent d-coherent 0-oneParticle d‖^2 =
      2+‖d‖^2-2*(1+‖d‖^2)*Real.exp (-‖d‖^2/2) := by
    rw [norm_sub_sq (𝕜 := ℂ),norm_sub_sq (𝕜 := ℂ),inner_coherent,
      norm_coherent,norm_coherent,norm_oneParticle,inner_sub_left,hip,hi0]
    simp only [sub_zero,RCLike.re_to_complex,Complex.ofReal_re]
    rw [hk]
    ring
  have he : 1-‖d‖^2/2 ≤ Real.exp (-‖d‖^2/2) := by
    convert Real.add_one_le_exp (-‖d‖^2/2) using 1
    ring
  have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2*(1+‖d‖^2))
  have hsq : ‖coherent d-coherent 0-oneParticle d‖^2 ≤ (‖d‖^2)^2 := by
    rw [hn]
    nlinarith
  nlinarith [norm_nonneg (coherent d-coherent 0-oneParticle d),sq_nonneg ‖d‖]

end CoherentFock

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem coherent_sub_vacuum_le (d : E) : ‖coherent d-coherent (0:E)‖ ≤ ‖d‖ := by
  have hsq : ‖coherent d-coherent (0:E)‖^2 = 2-2*Real.exp (-‖d‖^2/2) := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    simp only [norm_coherent,one_pow,inner_coherent,kernel,inner_zero_right,norm_zero,
      ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,neg_zero,zero_div,add_zero]
    simp only [Complex.ofReal_zero,add_zero,← Complex.ofReal_exp]
    change 1-2*Real.exp (-‖d‖^2/2)+1 = _
    ring
  have he := Real.add_one_le_exp (-‖d‖^2/2)
  nlinarith [norm_nonneg (coherent d-coherent (0:E)),norm_nonneg d]

theorem phase_sub_one_le (d e : E) : ‖phase d e-1‖ ≤ ‖d‖*‖e‖ := by
  calc
    ‖phase d e-1‖ ≤ |(⟪d,e⟫_ℂ).im| := by
      simpa only [phase,mul_comm,Real.norm_eq_abs,abs_neg] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(⟪d,e⟫_ℂ).im))
    _ ≤ ‖⟪d,e⟫_ℂ‖ := Complex.abs_im_le_norm _
    _ ≤ ‖d‖*‖e‖ := norm_inner_le_norm d e

 

theorem W_coherent_sub_le (d e : E) :
    ‖W d (coherent e)-coherent e‖ ≤ ‖d‖*(1+2*‖e‖) := by
  have heq : W d (coherent e)-coherent e =
      (phase d e-phase e d) • coherent (d+e) + W e (coherent d-coherent 0) := by
    simp only [map_sub,W_coherent,phase_zero_right,add_zero,one_smul]
    rw [add_comm e d]
    module
  rw [heq]
  calc
    _ ≤ ‖(phase d e-phase e d) • coherent (d+e)‖ + ‖W e (coherent d-coherent 0)‖ := norm_add_le _ _
    _ = ‖phase d e-phase e d‖ + ‖coherent d-coherent (0:E)‖ := by
      rw [norm_smul,norm_coherent,mul_one,norm_W]
    _ ≤ (‖phase d e-1‖+‖phase e d-1‖)+‖d‖ := by
      gcongr
      · have ht := dist_triangle (phase d e) 1 (phase e d)
        rw [dist_comm 1 (phase e d)] at ht
        simpa only [dist_eq_norm] using ht
      · exact coherent_sub_vacuum_le d
    _ ≤ (‖d‖*‖e‖+‖e‖*‖d‖)+‖d‖ := by
      gcongr
      · exact phase_sub_one_le d e
      · exact phase_sub_one_le e d
    _ = _ := by ring

 
def tailBound (x : PreSpace E) : ℝ :=
  (toFinsupp x).sum (fun e a => ‖a‖*(1+2*‖e‖))

theorem W_coe_sub_le (d : E) (x : PreSpace E) :
    ‖W d (↑x)-(↑x : Space E)‖ ≤ ‖d‖*tailBound x := by
  classical
  rw [coe_eq_sum]
  simp only [Finsupp.sum,map_sum,map_smul,← Finset.sum_sub_distrib,← smul_sub]
  calc
    _ ≤ ∑ e ∈ (toFinsupp x).support, ‖(toFinsupp x) e • (W d (coherent e)-coherent e)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ e ∈ (toFinsupp x).support, ‖(toFinsupp x) e‖*(‖d‖*(1+2*‖e‖)) := by
      apply Finset.sum_le_sum
      intro e he
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (W_coherent_sub_le d e) (norm_nonneg _)
    _ = _ := by
      simp only [tailBound,Finsupp.sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring

 
theorem centered_probe (d e : E) :
    (W (-e)).comp ((W d).comp (W e)) =
      Complex.exp (((-2*(⟪d,e⟫_ℂ).im : ℝ) : ℂ)*Complex.I) • W d := by
  rw [W_mul]
  rw [ContinuousLinearMap.comp_smul,W_mul]
  simp only [smul_smul]
  have hd : -e+(d+e)=d := by abel
  rw [hd]
  have hp : phase d e * phase (-e) (d+e) =
      Complex.exp (((-2*(⟪d,e⟫_ℂ).im : ℝ) : ℂ)*Complex.I) := by
    have hi : (⟪e,e⟫_ℂ).im=0 := inner_self_im (𝕜 := ℂ) e
    have hs := inner_im_symm (𝕜 := ℂ) e d
    change (⟪e,d⟫_ℂ).im = -(⟪d,e⟫_ℂ).im at hs
    simp only [phase,← Complex.exp_add,inner_neg_left,inner_add_right,
      Complex.neg_im,Complex.add_im,hi,hs,neg_neg]
    congr 1
    push_cast
    ring
  rw [hp]

end CoherentFock

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
open Complex

 
theorem unitary_phase_remainder (x : ℝ) :
    ‖Complex.exp ((x:ℂ)*I)-1-(x:ℂ)*I‖ ≤ 3*x^2 := by
  have hn : ‖(x:ℂ)*I‖ = |x| := by simp
  by_cases hx : |x| ≤ 1
  · have hh := Complex.norm_exp_sub_one_sub_id_le (by rwa [hn] : ‖(x:ℂ)*I‖ ≤ 1)
    rw [hn,sq_abs] at hh
    nlinarith [sq_nonneg x]
  · have h := norm_sub_le (Complex.exp ((x:ℂ)*I)-1) ((x:ℂ)*I)
    have h' := norm_sub_le (Complex.exp ((x:ℂ)*I)) (1:ℂ)
    rw [Complex.norm_exp_ofReal_mul_I,norm_one] at h'
    rw [hn] at h
    have hx' : 1 ≤ |x| := le_of_not_ge hx
    have ha : |x|^2=x^2 := sq_abs x
    nlinarith [sq_nonneg (|x|-1)]

theorem oneParticle_add (v w : E) : oneParticle (v+w)=oneParticle v+oneParticle w :=
  oneParticleEmbedding.map_add v w

theorem oneParticle_real_smul (r : ℝ) (v : E) :
    oneParticle (r • v)=r • oneParticle v := by
  exact oneParticleEmbedding.map_smul_of_tower r v

theorem coherent_hasFDerivAt_zero :
    HasFDerivAt (coherent (E := E)) oneParticleEmbedding.toContinuousLinearMap 0 := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro c hc
  have h : ∀ᶠ d : E in 𝓝 0, ‖d‖ ≤ c := by
    filter_upwards [Metric.ball_mem_nhds (0:E) hc] with d hd
    have hh : ‖d‖ < c := by simpa only [Metric.mem_ball,dist_zero_right] using hd
    exact hh.le
  filter_upwards [h] with d hd
  simp only [sub_zero]
  exact (coherent_taylor_one d).trans (by nlinarith [norm_nonneg d])

 
theorem W_coherent_reorder (v d : E) :
    W v (coherent d) = Complex.exp (((-2*(⟪v,d⟫_ℂ).im:ℝ):ℂ)*I) •
      W d (coherent v) := by
  rw [W_coherent,W_coherent,add_comm d v,smul_smul]
  congr 1
  have hi := inner_im_symm (𝕜 := ℂ) d v
  change (⟪d,v⟫_ℂ).im = -(⟪v,d⟫_ℂ).im at hi
  simp only [phase,← Complex.exp_add,hi,neg_neg]
  congr 1
  push_cast
  ring

 
theorem W_coherent_taylor (v d : E) :
    ‖W v (coherent d)-coherent d-I • fieldCoherent v d‖ ≤
      ‖v‖^2*(1+2*‖d‖+12*‖d‖^2) := by
  let a : ℝ := -2*(⟪v,d⟫_ℂ).im
  let c : ℂ := Complex.exp ((a:ℂ)*I)
  have hc : ‖c‖=1 := Complex.norm_exp_ofReal_mul_I a
  have hb : |a| ≤ 2*‖v‖*‖d‖ := by
    dsimp [a]
    norm_num only [abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := (Complex.abs_im_le_norm ⟪v,d⟫_ℂ).trans (norm_inner_le_norm v d)
    nlinarith
  have hcf : ‖c-1‖ ≤ |a| := by
    simpa only [c,mul_comm,Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a))
  have hcr : ‖c-1-(a:ℂ)*I‖ ≤ 3*a^2 := unitary_phase_remainder a
  have hf : I • fieldCoherent v d = W d (oneParticle v) + ((a:ℂ)*I) • coherent d := by
    simp only [fieldCoherent,smul_sub,smul_smul,a]
    push_cast
    rw [mul_neg,I_mul_I,neg_neg,one_smul]
    module
  have he : W v (coherent d)-coherent d-I • fieldCoherent v d =
      c • W d (coherent v-coherent 0-oneParticle v) +
      (c-1) • W d (oneParticle v) + (c-1-(a:ℂ)*I) • coherent d := by
    rw [W_coherent_reorder,hf]
    change c • W d (coherent v)-coherent d-
      (W d (oneParticle v)+((a:ℂ)*I) • coherent d) = _
    simp only [map_sub,W_coherent,phase_zero_right,one_smul,add_zero]
    module
  rw [he]
  calc
    _ ≤ ‖c • W d (coherent v-coherent 0-oneParticle v)‖ +
        ‖(c-1) • W d (oneParticle v)‖ + ‖(c-1-(a:ℂ)*I) • coherent d‖ :=
      (norm_add_le _ _).trans (_root_.add_le_add_left (norm_add_le _ _) _)
    _ = ‖coherent v-coherent 0-oneParticle v‖ + ‖c-1‖*‖v‖ +
        ‖c-1-(a:ℂ)*I‖ := by
      simp only [norm_smul,hc,one_mul,norm_W,norm_oneParticle,norm_coherent,mul_one]
    _ ≤ ‖v‖^2+|a| *‖v‖+3*a^2 := by gcongr; exact coherent_taylor_one v
    _ ≤ ‖v‖^2*(1+2*‖d‖+12*‖d‖^2) := by
      have hsq : a^2 ≤ (2*‖v‖*‖d‖)^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) hb 2
      have hh := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
      nlinarith

 
def secondTailBound (x : PreSpace E) : ℝ :=
  (toFinsupp x).sum (fun e a => ‖a‖*(1+2*‖e‖+12*‖e‖^2))

theorem W_coe_taylor (v : E) (x : PreSpace E) :
    ‖W v (↑x)-(↑x : Space E)-I • preField v x‖ ≤ ‖v‖^2*secondTailBound x := by
  classical
  rw [coe_eq_sum,preField_eq_sum]
  simp only [Finsupp.sum,map_sum,map_smul,Finset.smul_sum,smul_comm I,
    ← Finset.sum_sub_distrib,← smul_sub]
  calc
    _ ≤ ∑ e ∈ (toFinsupp x).support,
      ‖(toFinsupp x) e • (W v (coherent e)-coherent e-I • fieldCoherent v e)‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ (toFinsupp x).support,
      ‖(toFinsupp x) e‖*(‖v‖^2*(1+2*‖e‖+12*‖e‖^2)) := by
      apply Finset.sum_le_sum
      intro e he
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (W_coherent_taylor v e) (norm_nonneg _)
    _ = _ := by
      simp only [secondTailBound,Finsupp.sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring

end CoherentFock

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
open Complex

theorem fieldCoherent_add (v w d : E) :
    fieldCoherent (v+w) d=fieldCoherent v d+fieldCoherent w d := by
  simp only [fieldCoherent,oneParticle_add,map_add,inner_add_left,Complex.add_im]
  push_cast
  module

theorem fieldCoherent_real_smul (r : ℝ) (v d : E) :
    fieldCoherent (r • v) d=r • fieldCoherent v d := by
  have hi : (⟪r • v,d⟫_ℂ).im = r*(⟪v,d⟫_ℂ).im := by
    rw [← Complex.coe_smul r v,inner_smul_left]
    simp
  simp only [fieldCoherent,oneParticle_real_smul,ContinuousLinearMap.map_smul_of_tower,hi]
  simp only [← Complex.coe_smul]
  push_cast
  module

theorem preField_real_smul (r : ℝ) (v : E) (x : PreSpace E) :
    preField (r • v) x=r • preField v x := by
  classical
  simp only [preField_eq_sum,Finsupp.sum,fieldCoherent_real_smul,Finset.smul_sum]
  congr 1
  ext d
  exact smul_comm _ _ _

 
theorem hasDerivAt_W_coe_zero (v : E) (x : PreSpace E) :
    HasDerivAt (fun r : ℝ => W (r • v) (↑x)) (I • preField v x) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hC : 0 ≤ ‖v‖^2*secondTailBound x := by
    classical
    simp only [secondTailBound,Finsupp.sum]
    positivity
  have hd : 0 < c/(‖v‖^2*secondTailBound x+1) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) hd] with r hr
  have hr' : |r| < c/(‖v‖^2*secondTailBound x+1) := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hr
  have hh := W_coe_taylor (r • v) x
  simp only [zero_smul,W_zero,ContinuousLinearMap.id_apply,sub_zero,
    preField_real_smul,smul_comm I r,norm_smul,Real.norm_eq_abs,mul_pow] at hh ⊢
  have hc' : |r| *(‖v‖^2*secondTailBound x+1) < c := (lt_div_iff₀ (by positivity)).mp hr'
  have hx' := mul_le_mul_of_nonneg_right hc'.le (abs_nonneg r)
  nlinarith [sq_nonneg r,abs_nonneg r]

end CoherentFock

namespace CoherentFock
open scoped Interval
open Complex MeasureTheory
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

 
theorem inner_oneParticle_eq_deriv (x : Space E) (d : E) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f)
    (he : ∀ z, ⟪x,expVector (z • d)⟫_ℂ = f z) :
    ⟪x,oneParticle d⟫_ℂ = deriv f 0 := by
  rw [oneParticle,inner_smul_right]
  have hi := map_circleIntegral (innerSL ℂ x) (circleIntegrable_oneParticle_integrand d)
  simp only [innerSL_apply_apply,inner_smul_right,he] at hi
  rw [hi]
  have hc := DifferentiableOn.deriv_eq_smul_circleIntegral (c := (0:ℂ))
    (R := (1:ℝ)) (by norm_num) hf.differentiableOn
  simp only [sub_zero,smul_eq_mul] at hc
  rw [hc]
  have hz : 2*(Real.pi:ℂ)*I ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  exact inv_mul_cancel_left₀ hz _

theorem inner_expVector_W_oneParticle (e d v : E) :
    ⟪expVector e,W d (oneParticle v)⟫_ℂ =
      Complex.exp ((-‖d‖^2/2 : ℝ)+⟪e,d⟫_ℂ) * ⟪e-d,v⟫_ℂ := by
  rw [expVector,inner_smul_left,inner_coherent_W_oneParticle,
    conj_ofReal,← mul_assoc]
  congr 1
  simp only [kernel,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem inner_W_oneParticle_expVector (d v e : E) :
    ⟪W d (oneParticle v),expVector e⟫_ℂ =
      Complex.exp ((-‖d‖^2/2 : ℝ)+⟪d,e⟫_ℂ) * ⟪v,e-d⟫_ℂ := by
  rw [← inner_conj_symm,inner_expVector_W_oneParticle,map_mul,
    ← Complex.exp_conj,map_add,conj_ofReal,inner_conj_symm,inner_conj_symm]

 
theorem inner_W_oneParticle_oneParticle (d v u : E) :
    ⟪W d (oneParticle v),oneParticle u⟫_ℂ =
      (Real.exp (-‖d‖^2/2) : ℂ) * (⟪v,u⟫_ℂ-⟪v,d⟫_ℂ*⟪d,u⟫_ℂ) := by
  let f : ℂ → ℂ := fun z => Complex.exp ((-‖d‖^2/2 : ℝ)+z*⟪d,u⟫_ℂ) *
    (z*⟪v,u⟫_ℂ-⟪v,d⟫_ℂ)
  have hf : Differentiable ℂ f :=
    (Complex.differentiable_exp.comp
      ((differentiable_const _).add (differentiable_id.mul_const _))).mul
      ((differentiable_id.mul_const _).sub_const _)
  rw [inner_oneParticle_eq_deriv (W d (oneParticle v)) u f hf (fun z => by
    simp only [inner_W_oneParticle_expVector,inner_sub_right,inner_smul_right,f])]
  have hd := ((((hasDerivAt_id (0:ℂ)).mul_const ⟪d,u⟫_ℂ).const_add
    ((-‖d‖^2/2 : ℝ):ℂ)).cexp).mul
      (((hasDerivAt_id (0:ℂ)).mul_const ⟪v,u⟫_ℂ).sub_const ⟪v,d⟫_ℂ)
  rw [show deriv f 0 = _ from hd.deriv]
  simp only [id_eq,zero_mul,add_zero,zero_sub,← Complex.ofReal_exp]
  ring

 
theorem W_oneParticle_sub_le (d v : E) :
    ‖W d (oneParticle v)-oneParticle v‖ ≤ 2*‖d‖*‖v‖ := by
  have hn : ‖W d (oneParticle v)-oneParticle v‖^2 =
      2*‖v‖^2-2*Real.exp (-‖d‖^2/2)*(‖v‖^2-‖⟪d,v⟫_ℂ‖^2) := by
    rw [norm_sub_sq (𝕜 := ℂ),norm_W,norm_oneParticle,inner_W_oneParticle_oneParticle,
      inner_self_eq_norm_sq_to_K,← inner_conj_symm v d]
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    simp only [RCLike.re_to_complex]
    change ‖v‖^2-2*((Real.exp (-‖d‖^2/2):ℂ)*
      ((‖v‖:ℂ)^2-(‖⟪d,v⟫_ℂ‖^2:ℝ))).re+‖v‖^2 = _
    simp only [← Complex.ofReal_pow,← Complex.ofReal_sub,← Complex.ofReal_mul,Complex.ofReal_re]
    ring
  have he0 := Real.exp_pos (-‖d‖^2/2)
  have he1 : Real.exp (-‖d‖^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖d‖])
  have he2 : 1-‖d‖^2/2 ≤ Real.exp (-‖d‖^2/2) := by
    convert Real.add_one_le_exp (-‖d‖^2/2) using 1
    ring
  have hi : ‖⟪d,v⟫_ℂ‖^2 ≤ ‖d‖^2*‖v‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) d v) 2
  have hh1 := mul_le_mul_of_nonneg_right he2 (sq_nonneg ‖v‖)
  have hh2 := mul_le_mul_of_nonneg_right he1 (sq_nonneg ‖⟪d,v⟫_ℂ‖)
  have hsq : ‖W d (oneParticle v)-oneParticle v‖^2 ≤ (2*‖d‖*‖v‖)^2 := by
    rw [hn]
    nlinarith [sq_nonneg ‖⟪d,v⟫_ℂ‖,mul_nonneg (sq_nonneg ‖d‖) (sq_nonneg ‖v‖)]
  nlinarith [norm_nonneg (W d (oneParticle v)-oneParticle v),norm_nonneg d,norm_nonneg v,
    mul_nonneg (norm_nonneg d) (norm_nonneg v)]

end CoherentFock

end

end OAI
