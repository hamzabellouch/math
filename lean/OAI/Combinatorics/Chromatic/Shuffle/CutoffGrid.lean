import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNDiagonalConstant
import OAI.Combinatorics.Chromatic.GradedAlgebra.CutoffRow

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
include hc
omit [∀ i, Fintype (A i)] in
lemma clipped_gridShape_nonhead_zero (κ : ℝ)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) (hd : d≠0)
    (hk : κ < slope c η α) (ht : slope c η β ≤ κ)
    (hs : slope c η α ≤ slope c η d)
    (hm : slope c η d=slope c η α → mass c α ≤ mass c d)
    (hne : ¬(shapeComplement u=0 ∧ (fun i=>(v i).val)=0)) :
    quotientTensor a (clippedSlope c η κ) α β (gridShapeTensor a f g p R T u v)=0 := by
  unfold gridShapeTensor
  apply quotientTensor_cast_zero
  by_cases hsum : (fun i=>(u i).val)+(fun i=>(v i).val)=d
  · apply clipped_cell_nonhead_zero a c η hc κ
    · rwa [(shape_add_complement u).trans (realization_card R)]
    · rwa [(shape_add_complement v).trans (realization_card T)]
    · rwa [hsum]
    · rwa [(shape_add_complement u).trans (realization_card R),hsum]
    · rwa [(shape_add_complement u).trans (realization_card R),hsum]
    · exact hne
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hsum,map_zero,map_zero]

omit [∀ i, Fintype (A i)] in
lemma clipped_gridShape_wrong_source (κ : ℝ)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) (hd : d≠0)
    (hk : κ < slope c η α) (ht : slope c η β ≤ κ)
    (hs : slope c η α ≤ slope c η d)
    (hm : slope c η d=slope c η α → mass c α ≤ mass c d) (hne : d≠α) :
    quotientTensor a (clippedSlope c η κ) α β (gridShapeTensor a f g p R T u v)=0 := by
  by_cases hsum : (fun i=>(u i).val)+(fun i=>(v i).val)=d
  · apply clipped_gridShape_nonhead_zero a c η hc κ f g p R T u v hd hk ht hs hm
    rintro ⟨hu,hv⟩
    have he := (shape_add_complement u).trans (realization_card R)
    rw [hu,add_zero] at he
    rw [hv,add_zero,he] at hsum
    exact hne hsum.symm
  · unfold gridShapeTensor
    rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hsum,map_zero,map_zero,map_zero]

omit [∀ i, Fintype (A i)] in
lemma clipped_grid_wrong_source (κ : ℝ)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p)) (hd : d≠0)
    (hk : κ < slope c η α) (ht : slope c η β ≤ κ)
    (hs : slope c η α ≤ slope c η d)
    (hm : slope c η d=slope c η α → mass c α ≤ mass c d) (hne : d≠α) :
    quotientTensor a (clippedSlope c η κ) α β (gridTensor a f g p R T)=0 := by
  simp only [gridTensor,map_sum]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  exact clipped_gridShape_wrong_source a c η hc κ f g p R T u v hd hk ht hs hm hne
omit [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in

theorem clipped_restrict_wrong_head (κ : ℝ)
    {d e α β : I → ℕ} (h : d+e=α+β) (f : S d) (g : S e) (u : Cut α β) (hd : d≠0)
    (hk : κ < slope c η α) (ht : slope c η β ≤ κ)
    (hs : slope c η α ≤ slope c η d)
    (hm : slope c η d=slope c η α → mass c α ≤ mass c d) (hne : d≠α) :
    quotientTensor a (clippedSlope c η κ) α β
      (restrictTensor u (castS h (shufflePolynomial a f g)))=0 := by
  apply quotient_crossTensor_cancel
  let s : Pack (A:=fun i=>Fin ((α+β) i)) := fun _=>Finset.univ
  let R : Realization (α+β) s := defaultRealization (by intro i; simp [s])
  rw [cleared_restrictTensor a h f g R u,map_smul,
    clipped_grid_wrong_source a c η hc κ f g _ _ _ hd hk ht hs hm hne,smul_zero]
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearBTensorB clearBTensorBA

noncomputable def headRestriction (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    S (d+e) →ₗ[ℚ] B a μ d⊗[ℚ]B a μ e :=
  ((coeff.linearMap (R:=ℚ) 0).comp
    ((mulPolynomial (mixedInverseKernelUnit a a μ d e).val).comp
      (relativeTaylorB a μ d e).toLinearMap)).comp
    ((quotientTensor a μ d e).toLinearMap.comp (restrictTensorAlg (firstCut d e)).toLinearMap)

lemma headRestriction_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (f : S (d+e)) :
    headRestriction a μ d e f=
      quotientTensor a μ d e ((tensorSeparationSeries a d e f).coeff 0) := by
  change _=(mapRing (R:=S d⊗[ℚ]S e) (S:=B a μ d⊗[ℚ]B a μ e) (quotientTensor a μ d e).toRingHom (tensorSeparationSeries a d e f)).coeff 0
  rw [tensorSeparationSeries,mapRing_mul_polynomial,relativeTaylor_quotient]
  rfl

lemma headRestriction_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (f : S (d+e)) (hf : quotientTensor a μ d e (restrictTensor (firstCut d e) f)=0) :
    headRestriction a μ d e f=0 := by
  unfold headRestriction
  simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply]
  change (coeff.linearMap (R:=ℚ) 0)
    (mulPolynomial (mixedInverseKernelUnit a a μ d e).val
      (relativeTaylorB a μ d e (quotientTensor a μ d e (restrictTensor (firstCut d e) f))))=0
  rw [hf,map_zero,map_zero,map_zero]

lemma headRestriction_ideal (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (κ θ : ℝ) (d e : I → ℕ) (hμ : slope c η (d+e) ≤ θ)
    (hd : clippedSlope c η κ d ≤ θ) (he : clippedSlope c η κ e ≤ θ)
    (f : S (d+e)) (hf : f∈destabilizingSpace a (clippedSlope c η θ) (d+e)) :
    headRestriction a (clippedSlope c η κ) d e f=0 :=
  headRestriction_zero a _ d e f (clipped_restrict_ideal a c η hc κ θ d e hμ hd he _ f hf)

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
lemma headRestriction_shuffle_grid (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e α β : I → ℕ} (h : d+e=α+β) (f : S d) (g : S e)
    {s : Pack (A:=A)} (R : Realization (α+β) s) :
    headRestriction a μ α β (castS h (shufflePolynomial a f g))=
      clearedConstantB a μ α β (quotientTensor a μ α β
        (gridTensor a f g (cutRealizationEquiv R (firstCut α β)).val
          (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β)))) := by
  rw [headRestriction_mk,clearedConstantB_apply,clearedSeparationB_mk,
    ←separation_shuffle_grid a h f g R,mapRing_coeff]
  rfl

noncomputable def fullShape (s : Pack (A:=A)) : CutShape s := fun i=>Fin.last (s i).card
noncomputable def zeroShape (s : Pack (A:=A)) : CutShape s := fun _=>0
omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma shapeComplement_full (s : Pack (A:=A)) : shapeComplement (fullShape s)=0 := by
  funext i; simp [shapeComplement,fullShape]
omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma zeroShape_val (s : Pack (A:=A)) : (fun i=>(zeroShape s i).val)=0 := rfl
omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma eq_fullShape_of_complement {s : Pack (A:=A)} (u : CutShape s)
    (hu : shapeComplement u=0) : u=fullShape s := by
  funext i; apply Fin.ext
  have h := congrFun hu i
  have hh := (u i).isLt
  change (s i).card-(u i).val=0 at h
  change (u i).val=(s i).card
  omega
omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma eq_zeroShape_of_val {s : Pack (A:=A)} (u : CutShape s)
    (hu : (fun i=>(u i).val)=0) : u=zeroShape s := by
  funext i; apply Fin.ext; exact congrFun hu i

omit [∀ i, Fintype (A i)] in
lemma clipped_grid_constant_head (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (κ : ℝ) {d e : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization d (left p)) (T : Realization e (right p)) (hd : d≠0)
    (hk : κ < slope c η d) (ht : slope c η e ≤ κ) :
    clearedConstantB a (clippedSlope c η κ) d e
      (quotientTensor a (clippedSlope c η κ) d e (gridTensor a f g p R T))=
    quotientTensor a (clippedSlope c η κ) d e (f⊗ₜ[ℚ]g) := by
  classical
  simp only [gridTensor,map_sum]
  rw [Finset.sum_eq_single (fullShape (left p))]
  · rw [Finset.sum_eq_single (zeroShape (right p))]
    · unfold gridShapeTensor
      exact clearedConstantB_cell_head_cast a _ d e _ _ _ _ _ _
        (shapeComplement_full _) (zeroShape_val _) f g
    · intro v _ hv
      rw [clipped_gridShape_nonhead_zero a c η hc κ f g p R T _ v hd hk ht le_rfl (fun _=>le_rfl),map_zero]
      rintro ⟨_,h⟩
      exact hv (eq_zeroShape_of_val v h)
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro u _ hu
    apply Finset.sum_eq_zero
    intro v _
    rw [clipped_gridShape_nonhead_zero a c η hc κ f g p R T u v hd hk ht le_rfl (fun _=>le_rfl),map_zero]
    rintro ⟨h,_⟩
    exact hu (eq_fullShape_of_complement u h)
  · intro h; exact (h (Finset.mem_univ _)).elim

omit [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in

theorem headRestriction_shuffle_head (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (κ : ℝ) {d e : I → ℕ} (f : S d) (g : S e) (hd : d≠0)
    (hk : κ < slope c η d) (ht : slope c η e ≤ κ) :
    headRestriction a (clippedSlope c η κ) d e (shufflePolynomial a f g)=
      quotientTensor a (clippedSlope c η κ) d e (f⊗ₜ[ℚ]g) := by
  let s : Pack (A:=fun i=>Fin ((d+e) i)) := fun _=>Finset.univ
  let R : Realization (d+e) s := defaultRealization (by intro i; simp [s])
  have h := headRestriction_shuffle_grid a (clippedSlope c η κ) rfl f g R
  rw [castS_rfl] at h
  rw [h]
  exact clipped_grid_constant_head a c η hc κ f g _ _ _ hd hk ht
end ElementaryPositivity.RawShuffle

end

end OAI
