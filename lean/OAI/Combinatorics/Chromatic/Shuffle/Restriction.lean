import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SeparationCoefficients
import OAI.Combinatorics.Chromatic.Shuffle.ShuffleUnits

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma labeledPolynomial_cast {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
    {d e : I → ℕ} (h : d=e) (f : S d) :
    labeledPolynomial (A:=A) (castS h f)=labeledPolynomial f := by
  subst e
  rfl

omit [DecidableEq I] in
lemma labeledPolynomial_full (d : I → ℕ) (f : S d) :
    labeledPolynomial (A:=fun i=>Fin (d i)) f (fun _=>Finset.univ)=f.val := by
  let r : Realization d (A:=fun i=>Fin (d i)) (fun _=>Finset.univ) :=
    fun _=>(Equiv.subtypeUnivEquiv (fun _=>Finset.mem_univ _)).symm
  rw [labeledPolynomial_eq r]
  have hr : realizationMap r=id := rfl
  rw [hr,rename_id]
  rfl

omit [DecidableEq I] in
lemma rightInput_zero_rename {e : I → ℕ} (A : Cut 0 e) (f : S e) :
    rename (rightInput A) f.val=(castS (zero_add e).symm f).val := by
  classical
  have hempty : ∀ i,(A i).val=∅ := fun i=>Finset.card_eq_zero.mp (A i).property
  have huniv : ∀ i,(A i).valᶜ=Finset.univ := by intro i; rw [hempty]; exact Finset.compl_empty
  let r : Realization e (A:=fun i=>Fin ((0+e) i)) (fun _=>Finset.univ) :=
    fun i=>(rightEnum A i).trans (Equiv.subtypeEquivRight (fun x=>by rw [huniv]))
  have hr : realizationMap r=rightInput A := rfl
  rw [←hr,←labeledPolynomial_eq r,←labeledPolynomial_cast (zero_add e).symm f,
    labeledPolynomial_full]

omit [DecidableEq I] in
lemma leftInput_zero_rename {d : I → ℕ} (A : Cut d 0) (f : S d) :
    rename (leftInput A) f.val=(castS (add_zero d).symm f).val := by
  classical
  have huniv : ∀ i,(A i).val=Finset.univ := by
    intro i
    apply Finset.eq_univ_of_card
    simpa only [Fintype.card_fin,Pi.zero_apply,Nat.add_zero] using (A i).property
  let r : Realization d (A:=fun i=>Fin ((d+0) i)) (fun _=>Finset.univ) :=
    fun i=>(leftEnum A i).trans (Equiv.subtypeEquivRight (fun x=>by rw [huniv]))
  have hr : realizationMap r=leftInput A := rfl
  rw [←hr,←labeledPolynomial_eq r,←labeledPolynomial_cast (add_zero d).symm f,
    labeledPolynomial_full]

lemma restrictTensor_zero_left {e : I → ℕ} (A : Cut 0 e) (f : S e) :
    restrictTensor A (castS (zero_add e).symm f)=(1 : S 0)⊗ₜ[ℚ]f := by
  apply tensorValue_injective
  rw [tensorValue_restrictTensor,tensorValue_tmul,OneMemClass.coe_one,map_one,one_mul]
  apply rename_injective (cutSplit A) (cutSplit A).injective
  rw [rename_rename,rename_rename]
  have h₁ : cutSplit A ∘ (cutSplit A).symm=id := funext ((cutSplit A).apply_symm_apply)
  have h₂ : cutSplit A ∘ Sum.inr=rightInput A := rfl
  rw [h₁,h₂,rename_id,rightInput_zero_rename]
  rfl

lemma restrictTensor_zero_right {d : I → ℕ} (A : Cut d 0) (f : S d) :
    restrictTensor A (castS (add_zero d).symm f)=f⊗ₜ[ℚ](1 : S 0) := by
  apply tensorValue_injective
  rw [tensorValue_restrictTensor,tensorValue_tmul,OneMemClass.coe_one,map_one,mul_one]
  apply rename_injective (cutSplit A) (cutSplit A).injective
  rw [rename_rename,rename_rename]
  have h₁ : cutSplit A ∘ (cutSplit A).symm=id := funext ((cutSplit A).apply_symm_apply)
  have h₂ : cutSplit A ∘ Sum.inl=leftInput A := rfl
  rw [h₁,h₂,rename_id,leftInput_zero_rename]
  rfl

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.CoefficientIdeals
variable {R : Type*} [CommRing R]
lemma polynomial_map_quotient_eq_zero_iff (J : Ideal R) (p : Polynomial R) :
    Polynomial.map (Ideal.Quotient.mk J) p=0 ↔ ∀ n,p.coeff n∈J := by
  constructor
  · intro hp n
    have h:=congrArg (fun p : Polynomial (R⧸J)=>p.coeff n) hp
    simpa only [Polynomial.coeff_map,Polynomial.coeff_zero,Ideal.Quotient.eq_zero_iff_mem] using h
  · intro hp
    ext n
    simpa only [Polynomial.coeff_map,Polynomial.coeff_zero,Ideal.Quotient.eq_zero_iff_mem] using hp n
end ElementaryPositivity.CoefficientIdeals

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.CoefficientIdeals
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma relativeTaylorB_coeff_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : B a μ d ⊗[ℚ] B a μ e) : (relativeTaylorB a μ d e x).coeff 0=x := by
  rw [Polynomial.coeff_zero_eq_eval_zero,←map_zero (algebraMap ℚ (B a μ d ⊗[ℚ] B a μ e)),relativeTaylorB_eval]
  have he : translationB a μ d 0=LinearMap.id := LinearMap.ext (translationB_zero a μ d)
  rw [he,TensorProduct.map_id,LinearMap.id_apply]

lemma sourceTensorFiltration_cross_cancel (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e)
    (h : quotientTensor a (SlopeArithmetic.slope c η) d e (crossTensor d e)*x∈
      sourceTensorFiltration a c η hc θ d e W) :
    x∈sourceTensorFiltration a c η hc θ d e W := by
  let J:=sourceTensorFiltrationIdeal a c η hc θ d e W
  let q:=Ideal.Quotient.mk J
  have hh : ∀ n,(relativeTaylorB a (SlopeArithmetic.slope c η) d e
      (quotientTensor a (SlopeArithmetic.slope c η) d e (crossTensor d e)*x)).coeff n∈J := by
    apply ElementaryPositivity.CommonTranslation.polynomial_coeff_mem
    intro t
    rw [relativeTaylorB_eval]
    exact sourceTensorFiltration_translateLeft a c η hc θ d e W t _ h
  have hz:= (polynomial_map_quotient_eq_zero_iff J _).mpr hh
  rw [map_mul,Polynomial.map_mul,←relativeTaylor_quotient] at hz
  change Polynomial.map q (crossClearing a (SlopeArithmetic.slope c η) d e)*
    Polynomial.map q (relativeTaylorB a (SlopeArithmetic.slope c η) d e x)=0 at hz
  have hx : Polynomial.map q (relativeTaylorB a (SlopeArithmetic.slope c η) d e x)=0 :=
    ((crossClearing_monic a (SlopeArithmetic.slope c η) d e).map q).mul_right_eq_zero_iff.mp hz
  have hc0:=(polynomial_map_quotient_eq_zero_iff J _).mp hx 0
  rwa [relativeTaylorB_coeff_zero] at hc0

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
@[simp] lemma castS_trans {d e b : I → ℕ} (h : d=e) (k : e=b) (f : S d) :
    castS k (castS h f)=castS (h.trans k) f := by subst e; subst b; rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma castS_rfl {d : I → ℕ} (f : S d) : castS rfl f=f := rfl

def castB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) {d e : I → ℕ} (h : d=e)
    (f : B a μ d) : B a μ e := h ▸ f

@[simp] lemma castB_rfl (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) {d : I → ℕ}
    (f : B a μ d) : castB a μ rfl f=f := rfl
@[simp] lemma castB_trans (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) {d e b : I → ℕ}
    (h : d=e) (k : e=b) (f : B a μ d) : castB a μ k (castB a μ h f)=castB a μ (h.trans k) f := by
  subst e; subst b; rfl
lemma castB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) {d e : I → ℕ}
    (h : d=e) (f : S d) : castB a μ h (quotientAlg a μ d f)=quotientAlg a μ e (castS h f) := by
  subst e; rfl

lemma restriction_unit_kills_destabilizing (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (A : Cut d e)
    {f : S (d+e)} (hf : f∈destabilizingSpace a (slope c η) (d+e)) :
    quotientTensor a (slope c η) d e (restrictTensor A f)=0 := by
  rcases hs with rfl|rfl|hs
  · have ht : restrictTensor A f=(1 : S 0)⊗ₜ[ℚ]castS (zero_add e) f := by
      simpa only [castS_trans,castS_rfl] using restrictTensor_zero_left A (castS (zero_add e) f)
    rw [ht,quotientTensor_tmul]
    have hz : quotientAlg a (slope c η) e (castS (zero_add e) f)=0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (castS_mem_destabilizing a _ _ hf)
    rw [hz,TensorProduct.tmul_zero]
  · have ht : restrictTensor A f=castS (add_zero d) f⊗ₜ[ℚ](1 : S 0) := by
      simpa only [castS_trans,castS_rfl] using restrictTensor_zero_right A (castS (add_zero d) f)
    rw [ht,quotientTensor_tmul]
    have hz : quotientAlg a (slope c η) d (castS (add_zero d) f)=0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (castS_mem_destabilizing a _ _ hf)
    rw [hz,TensorProduct.zero_tmul]
  · exact restriction_kills_destabilizingSpace a c η hc hs A hf

noncomputable def restrictionBUnit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (A : Cut d e) :
    B a (slope c η) (d+e) →ₐ[ℚ] B a (slope c η) d⊗[ℚ]B a (slope c η) e :=
  Ideal.Quotient.liftₐ (destabilizingIdeal a (slope c η) (d+e))
    ((quotientTensor a (slope c η) d e).comp (restrictTensorAlg A))
    (by intro f hf; exact restriction_unit_kills_destabilizing a c η hc hs A hf)

@[simp] lemma restrictionBUnit_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (A : Cut d e) (f : S (d+e)) :
    restrictionBUnit a c η hc hs A (quotientAlg a (slope c η) (d+e) f)=
    quotientTensor a (slope c η) d e (restrictTensor A f) := rfl

lemma restrictionBUnit_eq_restrictionB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : slope c η d=slope c η e) (A : Cut d e) :
    restrictionBUnit a c η hc (Or.inr (Or.inr hs)) A=restrictionB a c η hc hs A := rfl

lemma restrictionBUnit_zero_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {e : I → ℕ} (A : Cut 0 e) (f : B a (slope c η) e) :
    restrictionBUnit a c η hc (Or.inl rfl) A (castB a _ (zero_add e).symm f)=
      (1 : B a (slope c η) 0)⊗ₜ[ℚ]f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change restrictionBUnit a c η hc (Or.inl rfl) A
      (castB a _ (zero_add e).symm (quotientAlg a (slope c η) e f))=
      (1 : B a (slope c η) 0)⊗ₜ[ℚ]quotientAlg a (slope c η) e f
    rw [castB_mk,restrictionBUnit_mk,restrictTensor_zero_left,quotientTensor_tmul,map_one]

lemma restrictionBUnit_zero_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d : I → ℕ} (A : Cut d 0) (f : B a (slope c η) d) :
    restrictionBUnit a c η hc (Or.inr (Or.inl rfl)) A (castB a _ (add_zero d).symm f)=
      f⊗ₜ[ℚ](1 : B a (slope c η) 0) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change restrictionBUnit a c η hc (Or.inr (Or.inl rfl)) A
      (castB a _ (add_zero d).symm (quotientAlg a (slope c η) d f))=
      quotientAlg a (slope c η) d f⊗ₜ[ℚ](1 : B a (slope c η) 0)
    rw [castB_mk,restrictionBUnit_mk,restrictTensor_zero_right,quotientTensor_tmul,map_one]

end ElementaryPositivity.RawShuffle

end

end OAI
