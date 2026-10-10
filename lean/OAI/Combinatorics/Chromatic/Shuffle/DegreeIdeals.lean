import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.ManyBlockPolynomiality

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma componentB_mul_components (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k i j : ℤ) (x y : B a μ d) :
    componentB a μ d k (componentB a μ d i x * componentB a μ d j y)=
      if k=i+j then componentB a μ d i x * componentB a μ d j y else 0 := by
  obtain ⟨f,hf,hqf⟩:=gradeB_homogeneous_representative a μ d i _ ⟨x,rfl⟩
  obtain ⟨g,hg,hqg⟩:=gradeB_homogeneous_representative a μ d j _ ⟨y,rfl⟩
  rw [←hqf,←hqg]
  change componentB a μ d k (quotientAlg a μ d f * quotientAlg a μ d g)=_
  rw [←map_mul]
  change quotientAlg a μ d (componentS d k (f*g))=_
  rw [componentS_of_homogeneous d (f*g) (hf.mul hg)]
  split_ifs
  · exact (quotientAlg a μ d).map_mul f g
  · exact (quotientAlg a μ d).map_zero

namespace SplitTree
@[reducible] def addDegrees : (T : SplitTree I) → T.Degrees → T.Degrees → T.Degrees
  | .leaf _, i,j => i+j
  | .node l r, i,j => (l.addDegrees i.1 j.1,r.addDegrees i.2 j.2)

omit [Fintype I] [DecidableEq I] in
lemma totalDegree_addDegrees (T : SplitTree I) (i j : T.Degrees) :
    T.totalDegree (T.addDegrees i j)=T.totalDegree i+T.totalDegree j := by
  induction T with
  | leaf d => rfl
  | node l r hl hr =>
    simp only [totalDegree,hl,hr]
    omega

lemma componentTensor_mul_components (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (k i j : T.Degrees) (x y : tensor (quotientFamily a μ) T) :
    componentTensor a μ T k (componentTensor a μ T i x * componentTensor a μ T j y)=
      if k=T.addDegrees i j then componentTensor a μ T i x * componentTensor a μ T j y else 0 := by
  induction T with
  | leaf d =>
    change componentB a μ d k (componentB a μ d i x * componentB a μ d j y)=_
    have hb:=componentB_mul_components a μ d k i j x y
    split_ifs with h
    · rw [ite_eq_left h] at hb
      exact hb
    · rw [ite_eq_right h] at hb
      exact hb
  | node l r hl hr =>
    have hp (xl yl : tensor (quotientFamily a μ) l) (xr yr : tensor (quotientFamily a μ) r) :
        componentTensor a μ (.node l r) k
          (componentTensor a μ (.node l r) i (xl ⊗ₜ[ℚ] xr) *
            componentTensor a μ (.node l r) j (yl ⊗ₜ[ℚ] yr))=
        if k=(.node l r : SplitTree I).addDegrees i j then
          componentTensor a μ (.node l r) i (xl ⊗ₜ[ℚ] xr) *
            componentTensor a μ (.node l r) j (yl ⊗ₜ[ℚ] yr) else 0 := by
      simp only [componentTensor,TensorProduct.map_tmul,Algebra.TensorProduct.tmul_mul_tmul,hl,hr]
      rcases k with ⟨kl,kr⟩
      by_cases hL : kl=l.addDegrees i.1 j.1 <;>
        by_cases hR : kr=r.addDegrees i.2 j.2 <;> simp [addDegrees,hL,hR]
    induction x using TensorProduct.inductionOn with
    | tmul xl xr =>
      induction y using TensorProduct.inductionOn with
      | tmul yl yr => simpa only using hp xl yl xr yr
      | add y z hy hz =>
        simp only [map_add,mul_add,hy,hz]
        split_ifs <;> simp
    | add x z hx hz =>
      simp only [map_add,add_mul,hx,hz]
      split_ifs <;> simp

noncomputable def degreeCutSubmodule (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) : Submodule ℚ (tensor (quotientFamily a μ) T) where
  carrier := {x | ∀ k,2*T.totalDegree k+T.doubleShift a<W → componentTensor a μ T k x=0}
  zero_mem' := by intro k hk; exact (componentTensor a μ T k).map_zero
  add_mem' := by intro x y hx hy k hk; simp only [map_add,hx k hk,hy k hk,add_zero]
  smul_mem' := by intro c x hx k hk; simp only [map_smul,hx k hk,smul_zero]

lemma degreeCutSubmodule_mul_mem (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) (x y : tensor (quotientFamily a μ) T)
    (hx : x∈degreeCutSubmodule a μ T W) : x*y∈degreeCutSubmodule a μ T W := by
  classical
  obtain ⟨s,hs,hxs⟩:=componentTensor_finite_decomposition a μ T x
  obtain ⟨t,ht,hyt⟩:=componentTensor_finite_decomposition a μ T y
  intro k hk
  conv_lhs => rw [←hxs,←hyt]
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  rw [componentTensor_mul_components]
  split_ifs with heq
  · by_cases hj0 : T.NonnegativeDegree j
    · have hjnn:=T.totalDegree_nonnegative j hj0
      have hiw : 2*T.totalDegree i+T.doubleShift a<W := by
        rw [heq,T.totalDegree_addDegrees] at hk
        omega
      rw [hx i hiw,zero_mul]
    · simp only [componentTensor_negative a μ T j hj0,LinearMap.zero_apply,mul_zero]
  · rfl

noncomputable def degreeCutIdeal (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) : Ideal (tensor (quotientFamily a μ) T) where
  __ := (degreeCutSubmodule a μ T W).toAddSubmonoid
  smul_mem' c x hx := by
    change c*x∈degreeCutSubmodule a μ T W
    rw [mul_comm]
    exact degreeCutSubmodule_mul_mem a μ T W x c hx

end SplitTree
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma degreeCut_mul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W V : ℤ) (x y : tensor (quotientFamily a μ) T)
    (hx : x∈degreeCutSubmodule a μ T W) (hy : y∈degreeCutSubmodule a μ T V) :
    x*y∈degreeCutSubmodule a μ T (W+V-T.doubleShift a) := by
  classical
  obtain ⟨s,hs,hxs⟩:=componentTensor_finite_decomposition a μ T x
  obtain ⟨t,ht,hyt⟩:=componentTensor_finite_decomposition a μ T y
  intro k hk
  conv_lhs => rw [←hxs,←hyt]
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  rw [componentTensor_mul_components]
  split_ifs with heq
  · by_cases hiw : 2*T.totalDegree i+T.doubleShift a<W
    · rw [hx i hiw,zero_mul]
    · have hjv : 2*T.totalDegree j+T.doubleShift a<V := by
        rw [heq,T.totalDegree_addDegrees] at hk
        omega
      rw [hy j hjv,mul_zero]
  · rfl

lemma degreeCut_weightComponent_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) (x : tensor (quotientFamily a μ) T)
    (hx : x∈degreeCutSubmodule a μ T (W+1)) : weightComponent a μ T W x=0 := by
  classical
  obtain ⟨s,hs,hxs⟩:=componentTensor_finite_decomposition a μ T x
  rw [weightComponent_eq_sum a μ T W x s hs]
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs with hw
  · exact hx i (by omega)
  · rfl

lemma leading_multiplier_congruence (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) (f g g₀ : tensor (quotientFamily a μ) T)
    (hf : f∈degreeCutSubmodule a μ T W)
    (hg : g-g₀∈degreeCutSubmodule a μ T (T.doubleShift a+1)) :
    weightComponent a μ T W (f*g)=weightComponent a μ T W (f*g₀) := by
  apply sub_eq_zero.mp
  rw [←map_sub,←mul_sub]
  apply degreeCut_weightComponent_zero
  have hh:=degreeCut_mul a μ T W (T.doubleShift a+1) f (g-g₀) hf hg
  simpa only [show W+(T.doubleShift a+1)-T.doubleShift a=W+1 by omega] using hh

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
