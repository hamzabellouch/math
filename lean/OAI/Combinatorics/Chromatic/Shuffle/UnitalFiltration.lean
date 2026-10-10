import Mathlib
import OAI.Combinatorics.Chromatic.Walls.BraidingFiltration
import OAI.Combinatorics.Chromatic.Shuffle.Restriction

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def unitalSourceFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Submodule ℚ (B a (slope c η) d) := by
  classical
  exact if d=0 then if W≤0 then ⊤ else ⊥ else sourceFiltration a c η hc θ d W

lemma unitalSourceFiltration_nonzero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (hd : d≠0) (W : ℤ) :
    unitalSourceFiltration a c η hc θ d W=sourceFiltration a c η hc θ d W := by
  simp only [unitalSourceFiltration,ite_eq_right hd]

lemma castB_mem_unitalSourceFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ) {f : B a (slope c η) d}
    (hf : f∈unitalSourceFiltration a c η hc θ d W) :
    castB a (slope c η) h f∈unitalSourceFiltration a c η hc θ e W := by
  subst e
  exact hf

lemma unitalSourceFiltration_unit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) : (1 : B a (slope c η) 0)∈unitalSourceFiltration a c η hc θ 0 0 := by
  simp only [unitalSourceFiltration,le_refl,ite_true,Submodule.mem_top]

lemma unitalSourceFiltration_mul_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (x y : B a (slope c η) d)
    (hx : x∈unitalSourceFiltration a c η hc θ d W) :
    x*y∈unitalSourceFiltration a c η hc θ d W := by
  classical
  by_cases hd : d=0
  · by_cases hw : W≤0
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_left hw,Submodule.mem_top]
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_right hw,Submodule.mem_bot] at hx ⊢
      rw [hx,zero_mul]
  · rw [unitalSourceFiltration_nonzero a c η hc θ d hd W] at hx ⊢
    exact sourceFiltration_mul_mem a c η hc θ d W x y hx

lemma unitalSourceFiltration_antitone (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) : Antitone (unitalSourceFiltration a c η hc θ d) := by
  classical
  intro u v huv
  by_cases hd : d=0
  · by_cases hu : u≤0
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_left hu,le_top]
    · have hv : ¬v≤0 := by omega
      simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_right hu,ite_eq_right hv,le_refl]
  · simpa only [unitalSourceFiltration_nonzero a c η hc θ d hd] using
      sourceFiltration_antitone a c η hc θ d huv

noncomputable def unitalSourceTensorFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :=
  additiveTensorFiltration (unitalSourceFiltration a c η hc θ d)
    (unitalSourceFiltration a c η hc θ e) W

lemma unitalSourceTensorFiltration_nonzero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hd : d≠0) (he : e≠0) (W : ℤ) :
    unitalSourceTensorFiltration a c η hc θ d e W=sourceTensorFiltration a c η hc θ d e W := by
  unfold unitalSourceTensorFiltration sourceTensorFiltration
  congr 1 <;> funext w
  · exact unitalSourceFiltration_nonzero a c η hc θ d hd w
  · exact unitalSourceFiltration_nonzero a c η hc θ e he w

lemma restrictionBUnit_independent (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (A C : Cut d e)
    (f : B a (slope c η) (d+e)) :
    restrictionBUnit a c η hc hs A f=restrictionBUnit a c η hc hs C f := by
  induction f using Submodule.Quotient.induction_on with
  | H f => exact congrArg (quotientTensor a (slope c η) d e) (restrictTensor_independent A C f)

lemma restrictionBUnit_unitalSourceTensorFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (A : Cut d e) (W : ℤ) (f : B a (slope c η) (d+e))
    (hf : f∈unitalSourceFiltration a c η hc θ (d+e) W) :
    restrictionBUnit a c η hc hs A f∈unitalSourceTensorFiltration a c η hc θ d e W := by
  by_cases hd : d=0
  · subst d
    have hr : restrictionBUnit a c η hc hs A f=(1 : B a (slope c η) 0)⊗ₜ[ℚ]castB a _ (zero_add e) f := by
      simpa only [castB_trans,castB_rfl] using restrictionBUnit_zero_left a c η hc A (castB a _ (zero_add e) f)
    rw [hr]
    exact tmul_mem_additiveTensorFiltration _ _ (by omega)
      (unitalSourceFiltration_unit a c η hc θ)
      (castB_mem_unitalSourceFiltration a c η hc θ (zero_add e) W hf)
  by_cases he : e=0
  · subst e
    have hr : restrictionBUnit a c η hc hs A f=castB a _ (add_zero d) f⊗ₜ[ℚ](1 : B a (slope c η) 0) := by
      simpa only [castB_trans,castB_rfl] using restrictionBUnit_zero_right a c η hc A (castB a _ (add_zero d) f)
    rw [hr]
    exact tmul_mem_additiveTensorFiltration _ _ (by omega)
      (castB_mem_unitalSourceFiltration a c η hc θ (add_zero d) W hf)
      (unitalSourceFiltration_unit a c η hc θ)
  have hde : d+e≠0 := add_ne_zero_left _ _ hd
  have hs' : slope c η d=slope c η e := hs.resolve_left hd |>.resolve_left he
  rw [unitalSourceFiltration_nonzero a c η hc θ (d+e) hde W] at hf
  rw [unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he W,
    restrictionBUnit_independent a c η hc hs A (firstCut d e),
    show restrictionBUnit a c η hc hs (firstCut d e)=restrictionB a c η hc hs' (firstCut d e) from rfl]
  exact restrictionB_sourceTensorFiltration a c η hc θ d e hs' W f hf

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open HahnSeries SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance braidCoeffTensorS (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance braidCoeffTensorSA (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance braidCoeffTensorB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidCoeffTensorBA (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance

noncomputable local instance braidCoeffTensorBN (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) := (braidCoeffTensorB a μ d e).toNonUnitalNonAssocSemiring
noncomputable local instance braidCoeffTensorBM (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Module (B a μ d⊗[ℚ]B a μ e) (B a μ d⊗[ℚ]B a μ e) := Semiring.toModule

namespace SeparationInfinity
lemma inverseKernelUnit_zero_left (b : I → I → ℕ) (e : I → ℕ) :
    inverseKernelUnit b 0 e=1 := by
  apply Units.ext
  apply mapRing_injective (tensorValueAlg 0 e).toRingHom (tensorValue_injective 0 e)
  rw [realize_inverseKernelUnit,Units.val_one,map_one]
  simp only [rawInverseKernelUnit,Pi.zero_apply,Finset.univ_eq_empty,Finset.prod_empty,
    Finset.prod_const_one,Units.val_one]

lemma inverseKernelUnit_zero_right (b : I → I → ℕ) (d : I → ℕ) :
    inverseKernelUnit b d 0=1 := by
  apply Units.ext
  apply mapRing_injective (tensorValueAlg d 0).toRingHom (tensorValue_injective d 0)
  rw [realize_inverseKernelUnit,Units.val_one,map_one]
  simp only [rawInverseKernelUnit,Pi.zero_apply,Finset.univ_eq_empty,Finset.prod_empty,
    Finset.prod_const_one,Units.val_one]

lemma braidingRatioUnit_zero_left (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (e : I → ℕ) :
    braidingRatioUnit a μ 0 e=1 := by
  simp only [braidingRatioUnit,mixedInverseKernelUnit,inverseKernelUnit_zero_left,map_one,
    inv_one,mul_one]

lemma braidingRatioUnit_zero_right (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    braidingRatioUnit a μ d 0=1 := by
  simp only [braidingRatioUnit,mixedInverseKernelUnit,inverseKernelUnit_zero_right,map_one,
    inv_one,mul_one]
end SeparationInfinity

lemma braidingDifference_coeff_mul_next (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : I → ℕ) (W : ℤ) (x : B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)
    (hx : x∈sourceTensorFiltration a c η hc θ d e W) (k : ℤ) :
    ((braidingRatioUnit a (SlopeArithmetic.slope c η) d e).val-1).coeff k*x∈
      sourceTensorFiltration a c η hc θ d e (W+1) := by
  have H:=braidingRatio_coeff_next a c η hc θ hχ d e W (single (0 : ℤ) x) (fun j=>?_) k
  · have he : ((braidingRatioUnit a (SlopeArithmetic.slope c η) d e).val-1)*single (0 : ℤ) x=
        (braidingRatioUnit a (SlopeArithmetic.slope c η) d e).val*single (0 : ℤ) x-single (0 : ℤ) x := by
      rw [sub_mul,one_mul]
    rw [←he,coeff_mul_single_zero] at H
    exact H
  · by_cases hj : j=0
    · subst j; simpa only [coeff_single_same] using hx
    · rw [coeff_single_of_ne hj]
      exact Submodule.zero_mem _

lemma braidingDifference_coeff_mul_unital_next (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : I → ℕ) (W : ℤ) (x : B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)
    (hx : x∈unitalSourceTensorFiltration a c η hc θ d e W) (k : ℤ) :
    ((braidingRatioUnit a (SlopeArithmetic.slope c η) d e).val-1).coeff k*x∈
      unitalSourceTensorFiltration a c η hc θ d e (W+1) := by
  by_cases hd : d=0
  · subst d
    rw [braidingRatioUnit_zero_left,Units.val_one,sub_self,coeff_zero,zero_mul]
    exact Submodule.zero_mem _
  by_cases he : e=0
  · subst e
    rw [braidingRatioUnit_zero_right,Units.val_one,sub_self,coeff_zero,zero_mul]
    exact Submodule.zero_mem _
  rw [unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he] at hx ⊢
  exact braidingDifference_coeff_mul_next a c η hc θ hχ d e W x hx k

end ElementaryPositivity.RawShuffle

end

end OAI
