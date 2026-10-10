import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GradeBInternal
import OAI.Combinatorics.Chromatic.GradedAlgebra.DHomogeneous

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity ElementaryPositivity.CommonTranslation
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma taylorS_coeff_homogeneous (d : I → ℕ) (f : S d) (k : ℤ)
    (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) (n : ℕ) :
    ((taylorS d f).coeff n).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) (k-n) := by
  have h := congrArg (fun p : Polynomial (MvPolynomial (Σi,Fin (d i)) ℚ)=>p.coeff n)
    (map_taylorSValue d f)
  rw [Polynomial.coeff_map] at h
  change ((taylorSValue d f).coeff n).val = (taylor f.val).coeff n at h
  change ((taylorSValue d f).coeff n).val.IsWeightedHomogeneous _ _
  rw [h]
  exact taylor_coeff_homogeneous f.val k hf n

lemma taylorB_coeff_graded (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : B a μ d) (k : ℤ) (hf : f∈gradeB a μ d k) (n : ℕ) :
    (taylorB a μ d f).coeff n ∈ gradeB a μ d (k-n) := by
  obtain ⟨g,hg,rfl⟩ := gradeB_homogeneous_representative a μ d k f hf
  change (taylorB a μ d (quotientAlg a μ d g)).coeff n ∈ _
  rw [taylorB_mk,Polynomial.coeff_map]
  change (destabilizingSpace a μ d).mkQ ((taylorS d g).coeff n) ∈ _
  rw [mem_gradeB_iff,componentB_mk,componentS_of_homogeneous _ _
    (taylorS_coeff_homogeneous d g k hg n),ite_eq_left rfl]

@[simp] lemma taylorB_coeff_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : B a μ d) : (taylorB a μ d f).coeff 0=f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change (taylorB a μ d (quotientAlg a μ d f)).coeff 0=quotientAlg a μ d f
    rw [taylorB_mk,Polynomial.coeff_map]
    apply congrArg (quotientAlg a μ d)
    apply Subtype.ext
    have h := congrArg (fun p : Polynomial (MvPolynomial (Σ i,Fin (d i)) ℚ)=>p.coeff 0)
      (map_taylorSValue d f)
    rw [Polynomial.coeff_map,taylor_coeff_zero] at h
    change ((taylorSValue d f).coeff 0).val=f.val
    exact h

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

@[reducible] def Degrees : SplitTree I → Type
  | .leaf _ => ℤ
  | .node l r => l.Degrees × r.Degrees

noncomputable instance degreesDecidableEq (T : SplitTree I) : DecidableEq T.Degrees := Classical.decEq _

@[reducible] def totalDegree : (T : SplitTree I) → T.Degrees → ℤ
  | .leaf _, k => k
  | .node l r, k => l.totalDegree k.1 + r.totalDegree k.2

@[reducible] def NonnegativeDegree : (T : SplitTree I) → T.Degrees → Prop
  | .leaf _, k => 0≤k
  | .node l r, k => l.NonnegativeDegree k.1 ∧ r.NonnegativeDegree k.2

omit [Fintype I] [DecidableEq I] in
lemma totalDegree_nonnegative (T : SplitTree I) (k : T.Degrees) (h : T.NonnegativeDegree k) :
    0≤T.totalDegree k := by
  induction T with
  | leaf d => exact h
  | node l r ihl ihr => exact add_nonneg (ihl k.1 h.1) (ihr k.2 h.2)

noncomputable def componentTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) :
    (T : SplitTree I) → T.Degrees →
      tensor (quotientFamily a μ) T →ₗ[ℚ] tensor (quotientFamily a μ) T
  | .leaf d, k => componentB a μ d k
  | .node l r, k => TensorProduct.map (componentTensor a μ l k.1) (componentTensor a μ r k.2)

lemma componentTensor_negative (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (k : T.Degrees) (h : ¬T.NonnegativeDegree k) :
    componentTensor a μ T k=0 := by
  classical
  induction T with
  | leaf d =>
    apply LinearMap.ext
    intro f
    exact componentB_negative a μ d k (lt_of_not_ge h) f
  | node l r ihl ihr =>
    change TensorProduct.map (componentTensor a μ l k.1) (componentTensor a μ r k.2)=0
    by_cases hl : l.NonnegativeDegree k.1
    · have hr : ¬r.NonnegativeDegree k.2 := fun hr=>h ⟨hl,hr⟩
      rw [ihr k.2 hr,TensorProduct.map_zero_right]
    · rw [ihl k.1 hl,TensorProduct.map_zero_left]

lemma componentTensor_componentTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (k l : T.Degrees) (f : tensor (quotientFamily a μ) T) :
    componentTensor a μ T k (componentTensor a μ T l f) =
      if k=l then componentTensor a μ T l f else 0 := by
  classical
  induction T with
  | leaf d =>
    split_ifs with h
    · subst l
      change componentB a μ d k (componentB a μ d k f) = componentB a μ d k f
      exact (componentB_componentB a μ d k k f).trans (ite_eq_left rfl)
    · change componentB a μ d k (componentB a μ d l f) = 0
      exact (componentB_componentB a μ d k l f).trans (ite_eq_right h)
  | node A B ihA ihB =>
    induction f using TensorProduct.inductionOn with
    | tmul x y =>
      by_cases hA : k.1=l.1 <;> by_cases hB : k.2=l.2 <;>
        simp [componentTensor,TensorProduct.map_tmul,ihA,ihB,Prod.ext_iff,hA,hB]
    | add x y hx hy =>
      simp only [map_add,hx,hy]
      split_ifs <;> simp

theorem componentTensor_finite_decomposition (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (f : tensor (quotientFamily a μ) T) :
    ∃ s : Finset T.Degrees, (∀ k∉s,componentTensor a μ T k f=0) ∧
      (∑ k ∈ s,componentTensor a μ T k f)=f := by
  classical
  induction T with
  | leaf d => exact componentB_finite_decomposition a μ d f
  | node A B ihA ihB =>
    induction f using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨s,hs,he⟩ := ihA x
      obtain ⟨t,ht,hf⟩ := ihB y
      refine ⟨s×ˢt,?_,?_⟩
      · intro k hk
        change componentTensor a μ A k.1 x ⊗ₜ[ℚ] componentTensor a μ B k.2 y = 0
        by_cases hx : k.1∈s
        · have hy : k.2∉t := fun hy=>hk (Finset.mem_product.mpr ⟨hx,hy⟩)
          rw [ht _ hy,TensorProduct.tmul_zero]
        · rw [hs _ hx,TensorProduct.zero_tmul]
      · change (∑ k ∈ s×ˢt,componentTensor a μ A k.1 x ⊗ₜ[ℚ] componentTensor a μ B k.2 y)=x⊗ₜ[ℚ]y
        rw [Finset.sum_product]
        simp_rw [← TensorProduct.tmul_sum]
        rw [← TensorProduct.sum_tmul,he,hf]
    | add x y hx hy =>
      obtain ⟨s,hs,he⟩ := hx
      obtain ⟨t,ht,hf⟩ := hy
      refine ⟨s∪t,?_,?_⟩
      · intro k hk
        rw [map_add,hs k (fun h=>hk (Finset.mem_union_left t h)),
          ht k (fun h=>hk (Finset.mem_union_right s h)),add_zero]
      · simp only [map_add,Finset.sum_add_distrib]
        have hx : (∑ k ∈ s∪t,componentTensor a μ (.node A B) k x)=x := by
          exact (Finset.sum_subset Finset.subset_union_left
            (fun k hk hks=>hs k hks)).symm.trans he
        have hy : (∑ k ∈ s∪t,componentTensor a μ (.node A B) k y)=y := by
          exact (Finset.sum_subset Finset.subset_union_right
            (fun k hk hkt=>ht k hkt)).symm.trans hf
        rw [hx,hy]

theorem componentTensor_detect (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (f : tensor (quotientFamily a μ) T)
    (h : ∀ k,componentTensor a μ T k f=0) : f=0 := by
  obtain ⟨s,hs,he⟩ := componentTensor_finite_decomposition a μ T f
  rw [← he]
  simp [h]

@[reducible] def IsOrderedList : SplitTree I → Prop
  | .leaf _ => True
  | .node (.leaf _) r => r.IsOrderedList
  | .node (.node _ _) _ => False

@[reducible] def doubleShift (a : I → I → ℕ) : SplitTree I → ℤ
  | .leaf d => eulerForm a d d
  | .node l r => l.doubleShift a + r.doubleShift a

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
