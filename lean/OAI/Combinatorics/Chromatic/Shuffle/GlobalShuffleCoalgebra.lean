import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SlopeGridSum
import OAI.Combinatorics.Chromatic.Shuffle.GlobalCoproductCoassociative
import OAI.Combinatorics.Chromatic.Shuffle.GlobalCoproductUnits
import OAI.Combinatorics.Chromatic.Shuffle.GlobalTensorInduction

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable instance globalCoalgebra (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)] :
    Coalgebra ℚ (UnitalShuffle a c η hc θ) where
  comul := globalCoproduct a c η hc θ
  counit := globalCounit a c η hc θ
  coassoc := LinearMap.ext (globalCoproduct_coassociative a c η hc θ hχ.out)
  rTensor_counit_comp_comul := LinearMap.ext (globalCoproduct_counit_left a c η hc θ)
  lTensor_counit_comp_comul := LinearMap.ext (globalCoproduct_counit_right a c η hc θ)

noncomputable def globalCoproductAlgHom (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    UnitalShuffle a c η hc θ →ₐ[ℚ] SignedGlobalTensor a c η hc θ :=
  AlgHom.ofLinearMap (globalCoproduct a c η hc θ)
    (globalCoproduct_unit a c η hc θ) (globalCoproduct_mul a c η hc θ)
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic DimensionSplit WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

def dimensionSize (d : I → ℕ) : ℕ := ∑ i,d i

omit [DecidableEq I] in
lemma dimensionSize_add (d e : I → ℕ) : dimensionSize (d+e)=dimensionSize d+dimensionSize e :=
  Finset.sum_add_distrib

omit [DecidableEq I] in
lemma dimensionSize_eq_zero (d : I → ℕ) : dimensionSize d=0 ↔ d=0 := by
  simp only [dimensionSize,Finset.sum_eq_zero_iff,Finset.mem_univ,true_implies]
  exact ⟨fun h=>funext h,fun h i=>congrFun h i⟩

variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A : Type*} [Ring A] [Algebra ℚ A]

def convVanishes (n : ℕ) (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) : Prop :=
  ∀ k : SlopeWeight c η hc θ, dimensionSize k.1.val < n →
    ∀ x : unitalComponent a c η hc θ k,
      f.ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=0

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convVanishes_zero (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) :
    convVanishes a c η hc θ 0 f := by
  intro k hk
  omega

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convVanishes_mono {n m : ℕ} (h : n ≤ m)
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ m f) : convVanishes a c η hc θ n f :=
  fun k hk=>hf k (lt_of_lt_of_le hk h)

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalTensorGrade_map_vanishes (n m : ℕ)
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A))
    (hf : convVanishes a c η hc θ n f) (hg : convVanishes a c η hc θ m g)
    (d e : slopeDimensions c η hc θ) (h : dimensionSize d.val+dimensionSize e.val < n+m)
    (W : ℤ) (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    TensorProduct.map f.ofConv g.ofConv (globalTensorGradeInclusion a c η hc θ d e W x)=0 := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
  | ht u x y =>
    rw [globalTensorGradeInclusion_part,TensorProduct.map_tmul]
    by_cases hd : dimensionSize d.val < n
    · rw [hf (d,u) hd x,TensorProduct.zero_tmul]
    · have he : dimensionSize e.val < m := by omega
      rw [hg (e,W-u) he y,TensorProduct.tmul_zero]

lemma convVanishes_mul {n m : ℕ}
    {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ n f) (hg : convVanishes a c η hc θ m g) :
    convVanishes a c η hc θ (n+m) (f*g) := by
  intro k hk x
  rw [LinearMap.convMul_apply]
  change LinearMap.mul' ℚ A (TensorProduct.map f.ofConv g.ofConv
    (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)))=0
  rw [globalCoproduct_lof]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro s _
  change LinearMap.mul' ℚ A (TensorProduct.map f.ofConv g.ofConv
    (globalTensorGradeInclusion a c η hc θ ⟨left s.val,s.property.1⟩
      ⟨right s.val,s.property.2⟩ k.2 _))=0
  rw [globalTensorGrade_map_vanishes a c η hc θ n m f g hf hg]
  · exact (LinearMap.mul' ℚ A).map_zero
  · rw [←dimensionSize_add,left_add_right]
    exact hk

lemma convVanishes_pow {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) (n : ℕ) :
    convVanishes a c η hc θ n (f^n) := by
  induction n with
  | zero => exact convVanishes_zero a c η hc θ _
  | succ n ih =>
    rw [pow_succ]
    exact convVanishes_mul a c η hc θ ih hf

noncomputable def convolutionJ : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ) :=
  toConv LinearMap.id - 1

lemma zeroDimension_lof_scalar (k : SlopeWeight c η hc θ) (h : k.1.val=0)
    (x : unitalComponent a c η hc θ k) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x =
      globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x) •
        globalUnit a c η hc θ := by
  rcases k with ⟨⟨d,hd⟩,W⟩
  dsimp at h
  subst d
  by_cases hW : W=0
  · subst W
    change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) 0 x =
      globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) 0 x) •
        globalUnit a c η hc θ
    rw [globalCounit_lof_zero,globalUnit,←map_smul]
    exact congrArg (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) 0)
      (zeroGrade_eq_scalar a c η hc θ x)
  · let := zeroUnitalGrade_subsingleton a c η hc θ W hW
    have hx : x=0 := Subsingleton.elim _ _
    simp only [hx,map_zero,zero_smul]

lemma convolutionJ_vanishes : convVanishes a c η hc θ 1 (convolutionJ a c η hc θ) := by
  intro k hk x
  have hd : k.1.val=0 := (dimensionSize_eq_zero _).mp (by omega)
  change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x -
    algebraMap ℚ (UnitalShuffle a c η hc θ)
      (globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=0
  rw [Algebra.algebraMap_eq_smul_one,sub_eq_zero]
  change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x =
    globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x) •
      globalUnit a c η hc θ
  exact zeroDimension_lof_scalar a c η hc θ k hd x

lemma convolutionJ_pow_eq_zero (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) (r : ℕ) (hr : dimensionSize k.1.val < r) :
    ((convolutionJ a c η hc θ)^r).ofConv
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=0 :=
  convVanishes_pow a c η hc θ (convolutionJ_vanishes a c η hc θ) r k hr x

end ElementaryPositivity.RawShuffle

end

end OAI
