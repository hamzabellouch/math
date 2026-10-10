import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalConvolutionQuotient
import OAI.Combinatorics.Chromatic.GradedAlgebra.NilpotentLogarithm
import OAI.Combinatorics.Chromatic.GradedAlgebra.ConvolutionPostcomposition

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open WithConv ElementaryPositivity.FiniteLog
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

noncomputable def convSeries (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A))
    (p : PowerSeries ℚ) : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A) :=
  toConv (DirectSum.toModule ℚ _ _ (fun k=>∑ r ∈ Finset.range (dimensionSize k.1.val+1),
    PowerSeries.coeff r p • (f^r).ofConv.comp (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k)))

lemma convSeries_lof (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A))
    (p : PowerSeries ℚ) (k : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k) :
    (convSeries a c η hc θ f p).ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=
      ∑ r ∈ Finset.range (dimensionSize k.1.val+1), PowerSeries.coeff r p •
        (f^r).ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x) := by
  rw [convSeries,ofConv_toConv,DirectSum.toModule_lof]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply]

lemma convolutionProjection_series (n : ℕ)
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) (p : PowerSeries ℚ) :
    convolutionProjection a c η hc θ n (convSeries a c η hc θ f p)=
      nilEval (convolutionProjection a c η hc θ n f) p := by
  rw [nilEval_eq_sum (convolutionProjection_nilpotent a c η hc θ n hf)]
  simp only [←map_pow,←map_smul,←map_sum]
  rw [convolutionProjection_eq_iff]
  intro k hk x
  rw [convSeries_lof]
  simp only [ofConv_sum,ofConv_smul,LinearMap.sum_apply,LinearMap.smul_apply]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro r hr hsmall
  rw [Finset.mem_range,not_lt] at hsmall
  rw [convVanishes_pow a c η hc θ hf r k (by omega) x,smul_zero]

lemma convolutionProjection_jointly_injective
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A))
    (h : ∀ n, convolutionProjection a c η hc θ n f=convolutionProjection a c η hc θ n g) : f=g := by
  apply ofConv_injective
  apply DirectSum.linearMap_ext
  intro k
  ext x
  exact (convolutionProjection_eq_iff a c η hc θ (dimensionSize k.1.val+1) f g).mp
    (h _) k (by omega) x

lemma convSeries_post (φ : A →ₐ[ℚ] B)
    (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) (p : PowerSeries ℚ) :
    convPost φ (convSeries a c η hc θ f p)=convSeries a c η hc θ (convPost φ f) p := by
  apply ofConv_injective
  apply DirectSum.linearMap_ext
  intro k
  ext x
  simp only [LinearMap.comp_apply]
  rw [convPost_apply,convSeries_lof,convSeries_lof]
  simp only [map_sum,map_smul,←map_pow,convPost_apply]

lemma convSeries_order_one
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)} (p : PowerSeries ℚ)
    (hp : PowerSeries.constantCoeff p=0) : convVanishes a c η hc θ 1 (convSeries a c η hc θ f p) := by
  intro k hk x
  have hd : dimensionSize k.1.val=0 := by omega
  rw [convSeries_lof,hd]
  simp only [zero_add,Finset.sum_range_one,PowerSeries.coeff_zero_eq_constantCoeff,hp,zero_smul]

lemma convVanishes_one_add_product {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) (hg : convVanishes a c η hc θ 1 g) :
    convVanishes a c η hc θ 1 ((1+f)*(1+g)-1) := by
  rw [show (1+f)*(1+g)-1=f+g+f*g by noncomm_ring]
  exact convVanishes_add a c η hc θ (convVanishes_add a c η hc θ hf hg)
    (convVanishes_mono a c η hc θ (by omega : 1 ≤ 1+1) (convVanishes_mul a c η hc θ hf hg))

lemma convSeries_log_product {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hfg : Commute f g) (hf : convVanishes a c η hc θ 1 f) (hg : convVanishes a c η hc θ 1 g) :
    convSeries a c η hc θ ((1+f)*(1+g)-1) (PowerSeries.log ℚ)=
      convSeries a c η hc θ f (PowerSeries.log ℚ)+convSeries a c η hc θ g (PowerSeries.log ℚ) := by
  apply convolutionProjection_jointly_injective a c η hc θ
  intro n
  rw [convolutionProjection_series a c η hc θ n (convVanishes_one_add_product a c η hc θ hf hg),
    map_add,convolutionProjection_series a c η hc θ n hf,
    convolutionProjection_series a c η hc θ n hg]
  simp only [map_sub,map_mul,map_add,map_one]
  exact nilEval_log_mul_of_commute (hfg.map (convolutionProjection a c η hc θ n))
    ⟨n,convolutionProjection_nilpotent a c η hc θ n hf⟩
    ⟨n,convolutionProjection_nilpotent a c η hc θ n hg⟩

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def signedLeft : UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ :=
  (TensorProduct.mk ℚ _ _).flip (globalUnit a c η hc θ)
noncomputable def signedRight : UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ :=
  TensorProduct.mk ℚ _ _ (globalUnit a c η hc θ)

lemma signedLeft_apply (x : UnitalShuffle a c η hc θ) :
    signedLeft a c η hc θ x=x⊗ₜ[ℚ]globalUnit a c η hc θ := rfl
lemma signedRight_apply (x : UnitalShuffle a c η hc θ) :
    signedRight a c η hc θ x=globalUnit a c η hc θ⊗ₜ[ℚ]x := rfl

noncomputable def signedMapProduct (f g : UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ) :
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ :=
  (LinearMap.mul' ℚ (SignedGlobalTensor a c η hc θ)).comp (TensorProduct.map f g)

lemma signedMapProduct_tmul (f g : UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ)
    (x y : UnitalShuffle a c η hc θ) :
    signedMapProduct a c η hc θ f g (x⊗ₜ[ℚ]y)=f x*g y := rfl

lemma signedTensor_mul_eq (x y : SignedGlobalTensor a c η hc θ) :
    x*y=globalSignedTensorMultiply a c η hc θ x y := rfl

lemma signedLeft_product (t : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    signedMapProduct a c η hc θ (signedLeft a c η hc θ) (signedLeft a c η hc θ) t=
      signedLeft a c η hc θ (LinearMap.mul' ℚ (UnitalShuffle a c η hc θ) t) := by
  induction t using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht k l x y =>
    rw [signedMapProduct_tmul,signedTensor_mul_eq,LinearMap.mul'_apply,signedLeft_apply,signedLeft_apply,signedLeft_apply]
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a 0 l.1.val) • ((_ * _)⊗ₜ[ℚ]((1:UnitalShuffle a c η hc θ)*1))=(_ * _)⊗ₜ[ℚ]1
    simp only [eulerForm,Pi.zero_apply,Int.natCast_zero,zero_mul,mul_zero,Finset.sum_const_zero,sub_zero,zpow_zero,one_smul]
    exact congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) rfl (one_mul _)

lemma signedRight_product (t : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    signedMapProduct a c η hc θ (signedRight a c η hc θ) (signedRight a c η hc θ) t=
      signedRight a c η hc θ (LinearMap.mul' ℚ (UnitalShuffle a c η hc θ) t) := by
  induction t using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht k l x y =>
    rw [signedMapProduct_tmul,signedTensor_mul_eq,LinearMap.mul'_apply,signedRight_apply,signedRight_apply,signedRight_apply]
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a k.1.val 0) • (((1:UnitalShuffle a c η hc θ)*1)⊗ₜ[ℚ](_ * _))=1⊗ₜ[ℚ](_ * _)
    simp only [eulerForm,Pi.zero_apply,Int.natCast_zero,mul_zero,Finset.sum_const_zero,sub_zero,zpow_zero,one_smul]
    exact congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) (one_mul _) rfl

lemma signedLeftRight_product (t : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    signedMapProduct a c η hc θ (signedLeft a c η hc θ) (signedRight a c η hc θ) t=t := by
  induction t using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero]; rfl
  | ha x y hx hy => simp only [map_add,hx,hy]; rfl
  | ht k l x y =>
    rw [signedMapProduct_tmul,signedTensor_mul_eq,signedLeft_apply,signedRight_apply]
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a 0 0) • ((_ * 1)⊗ₜ[ℚ](1 * _))=_
    simp only [eulerForm,Pi.zero_apply,Int.natCast_zero,mul_zero,Finset.sum_const_zero,sub_zero,zpow_zero,one_smul]
    exact congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) (mul_one _) (one_mul _)

lemma signedRightLeft_product (t : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    signedMapProduct a c η hc θ (signedRight a c η hc θ) (signedLeft a c η hc θ) t=
      globalSignedComm a c η hc θ t := by
  induction t using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero]; rfl
  | ha x y hx hy => simp only [map_add,hx,hy]; rfl
  | ht k l x y =>
    rw [signedMapProduct_tmul,signedTensor_mul_eq,signedRight_apply,signedLeft_apply]
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a k.1.val l.1.val) • ((1 * _)⊗ₜ[ℚ](_ * 1))=_
    rw [globalSignedComm,LinearMap.comp_apply,globalSignOperator_tmul_lof,map_smul]
    simp only [LinearEquiv.coe_coe,TensorProduct.comm_tmul]
    exact congrArg (fun t=>((-1:ℚ)^eulerForm a k.1.val l.1.val) • t)
      (congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) (one_mul _) (mul_one _))

noncomputable def signedLeftAlgHom : UnitalShuffle a c η hc θ →ₐ[ℚ] SignedGlobalTensor a c η hc θ :=
  AlgHom.ofLinearMap (signedLeft a c η hc θ) rfl
    (fun x y=>(signedLeft_product a c η hc θ (x⊗ₜ[ℚ]y)).symm)
noncomputable def signedRightAlgHom : UnitalShuffle a c η hc θ →ₐ[ℚ] SignedGlobalTensor a c η hc θ :=
  AlgHom.ofLinearMap (signedRight a c η hc θ) rfl
    (fun x y=>(signedRight_product a c η hc θ (x⊗ₜ[ℚ]y)).symm)

end ElementaryPositivity.RawShuffle

end

end OAI
