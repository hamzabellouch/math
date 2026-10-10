import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FourCellFactorization
import OAI.Combinatorics.Chromatic.Shuffle.RawGradedAlgebra

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)
noncomputable def HNTensor : List (I → ℕ) → CommAlgCat.{u} ℚ
  | [] => CommAlgCat.of ℚ (S (0 : I → ℕ))
  | d::l => CommAlgCat.of ℚ (B a (slope c η) d⊗[ℚ]HNTensor l)

noncomputable def hnWordMap (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) :
    (l : List (I → ℕ)) → HNTensor a c η l →ₗ[ℚ] RawAlgebra a
  | [] => rawLof a 0
  | d::l => (LinearMap.mul' ℚ (RawAlgebra a)).comp
      (TensorProduct.map ((rawLof a d).comp (σ d)) (hnWordMap σ l))

lemma range_tensor_mul {A M N : Type*} [Ring A] [Algebra ℚ A]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (f : M →ₗ[ℚ] A) (g : N →ₗ[ℚ] A) :
    LinearMap.range ((LinearMap.mul' ℚ A).comp (TensorProduct.map f g))=
      LinearMap.range f*LinearMap.range g := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      exact Submodule.mul_mem_mul (show f x∈LinearMap.range f from ⟨x,rfl⟩)
        (show g y∈LinearMap.range g from ⟨y,rfl⟩)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · apply Submodule.mul_le.mpr
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    exact ⟨x⊗ₜ[ℚ]y,rfl⟩

lemma rawDimensionSpace_zero_eq : rawDimensionSpace a 0=1 := by
  apply le_antisymm (rawDimensionSpace_zero a)
  apply Submodule.one_le.mpr
  exact ⟨(1 : S (0 : I → ℕ)),rfl⟩
lemma hnWordMap_range (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (l : List (I → ℕ)) :
    LinearMap.range (hnWordMap a c η σ l)=hnWordSpace (rawSectionSpace a c η σ) l := by
  induction l with
  | nil => exact rawDimensionSpace_zero_eq a
  | cons d l ih =>
    change LinearMap.range ((LinearMap.mul' ℚ (RawAlgebra a)).comp
      (TensorProduct.map ((rawLof a d).comp (σ d)) (hnWordMap a c η σ l)))=
      rawSectionSpace a c η σ d*hnWordSpace (rawSectionSpace a c η σ) l
    rw [range_tensor_mul,ih]
    rfl
lemma hnWordSpace_raw_le (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (l : List (I → ℕ)) :
    hnWordSpace (rawSectionSpace a c η σ) l ≤ rawDimensionSpace a l.sum := by
  induction l with
  | nil => simp only [hnWordSpace_nil,List.sum_nil,rawDimensionSpace_zero_eq,le_refl]
  | cons d l ih => exact (mul_le_mul' (rawSectionSpace_le a c η σ d) ih).trans (rawDimensionSpace_mul a d l.sum)

abbrev HNIndex (d : I → ℕ) := {l : List (I → ℕ) // l.sum=d ∧ HNOrdered c η l}
noncomputable def hnExpansionRaw (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    (⨁ l : HNIndex c η d,HNTensor a c η l.val) →ₗ[ℚ] RawAlgebra a :=
  DirectSum.toModule ℚ _ _ (fun l=>hnWordMap a c η σ l.val)

lemma hnExpansionRaw_range (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    LinearMap.range (hnExpansionRaw a c η σ d)=hnOrderedSpan c η (rawSectionSpace a c η σ) d := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    induction x using DirectSum.induction_on with
    | zero => simpa only [map_zero] using Submodule.zero_mem (hnOrderedSpan c η (rawSectionSpace a c η σ) d)
    | of l x =>
      have hx : hnWordMap a c η σ l.val x∈hnWordSpace (rawSectionSpace a c η σ) l.val :=
        hnWordMap_range a c η σ l.val ▸ LinearMap.mem_range_self _ x
      change hnExpansionRaw a c η σ d (DirectSum.lof ℚ _ _ l x)∈_
      rw [hnExpansionRaw,DirectSum.toModule_lof]
      exact hnWordSpace_le c η (rawSectionSpace a c η σ) l.val l.property.1 l.property.2 hx
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · refine iSup_le fun l=>iSup_le fun hl=>iSup_le fun ho=>?_
    rw [←hnWordMap_range]
    rintro _ ⟨x,rfl⟩
    exact ⟨DirectSum.lof ℚ _ _ ⟨l,hl,ho⟩ x,DirectSum.toModule_lof ℚ _ _⟩

lemma hnExpansionRaw_mem (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ)
    (x : ⨁ l : HNIndex c η d,HNTensor a c η l.val) :
    hnExpansionRaw a c η σ d x∈rawDimensionSpace a d := by
  have h : hnOrderedSpan c η (rawSectionSpace a c η σ) d ≤ rawDimensionSpace a d := by
    refine iSup_le fun l=>iSup_le fun hl=>iSup_le fun _=>?_
    simpa only [hl] using hnWordSpace_raw_le a c η σ l
  exact h ((hnExpansionRaw_range a c η σ d) ▸ LinearMap.mem_range_self _ x)

noncomputable def hnExpansion (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    (⨁ l : HNIndex c η d,HNTensor a c η l.val) →ₗ[ℚ] rawDimensionSpace a d :=
  (hnExpansionRaw a c η σ d).codRestrict _ (hnExpansionRaw_mem a c η σ d)

theorem hnExpansion_surjective (hc : ∀ i,0 < c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ) (d : I → ℕ) :
    Function.Surjective (hnExpansion a c η σ d) := by
  intro x
  obtain ⟨y,hy⟩ : x.val∈LinearMap.range (hnExpansionRaw a c η σ d) := by
    rw [hnExpansionRaw_range]
    exact raw_hn_spanning a c η σ hσ hc d x.property
  exact ⟨y,Subtype.ext hy⟩
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance tensorSCommRing (d e : I → ℕ) : CommRing (S d ⊗[ℚ] S e) := inferInstance
noncomputable local instance tensorSAlgebra (d e : I → ℕ) : Algebra ℚ (S d ⊗[ℚ] S e) := inferInstance
noncomputable local instance fourSCommRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) := inferInstance
noncomputable local instance fourSAlgebra (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) := inferInstance

noncomputable def fourValueAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) →ₐ[ℚ]
      MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ :=
  (tensorEquivSum ℚ _ _ ℚ).toAlgHom.comp
    (Algebra.TensorProduct.map (tensorValueAlg d₁ e₁) (tensorValueAlg d₂ e₂))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma fourValueAlg_apply (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) :
    fourValueAlg d₁ e₁ d₂ e₂ x=fourValue d₁ e₁ d₂ e₂ x := rfl

noncomputable def fourInterchange (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁ ⊗[ℚ] S d₂) ⊗[ℚ] (S e₁ ⊗[ℚ] S e₂) ≃ₗ[ℚ]
      (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) :=
  TensorProduct.tensorTensorTensorComm ℚ _ _ _ _

omit [Fintype I] [DecidableEq I] in
lemma fourValue_interchange (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S d₁ ⊗[ℚ] S d₂) (g : S e₁ ⊗[ℚ] S e₂) :
    fourValue d₁ e₁ d₂ e₂ (fourInterchange d₁ e₁ d₂ e₂ (f⊗ₜ[ℚ]g))=
      rename (firstColumnVars d₁ e₁ d₂ e₂) (tensorValue d₁ d₂ f) *
      rename (secondColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ e₂ g) := by
  induction f using TensorProduct.inductionOn with
  | add f h hf hh =>
    rw [TensorProduct.add_tmul, (fourInterchange d₁ e₁ d₂ e₂).map_add,
      (fourValue d₁ e₁ d₂ e₂).map_add, (tensorValue d₁ d₂).map_add, map_add, hf, hh, add_mul]
  | tmul x y =>
    induction g using TensorProduct.inductionOn with
    | add g h hg hh =>
      rw [TensorProduct.tmul_add, (fourInterchange d₁ e₁ d₂ e₂).map_add,
        (fourValue d₁ e₁ d₂ e₂).map_add, (tensorValue e₁ e₂).map_add, map_add, hg, hh, mul_add]
    | tmul z w =>
      simp only [fourInterchange,TensorProduct.tensorTensorTensorComm_tmul,
        fourValue_tmul,tensorValue_tmul,map_mul,rename_rename]
      have h₁ : Sum.inl ∘ Sum.inl = firstColumnVars d₁ e₁ d₂ e₂ ∘ Sum.inl := rfl
      have h₂ : Sum.inl ∘ Sum.inr = secondColumnVars d₁ e₁ d₂ e₂ ∘ Sum.inl := rfl
      have h₃ : Sum.inr ∘ Sum.inl = firstColumnVars d₁ e₁ d₂ e₂ ∘ Sum.inr := rfl
      have h₄ : Sum.inr ∘ Sum.inr = secondColumnVars d₁ e₁ d₂ e₂ ∘ Sum.inr := rfl
      rw [h₁,h₂,h₃,h₄]
      ring

noncomputable def fourCrossPolynomial (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :=
  rename (fourPackEquiv d₁ e₁ d₂ e₂)
    (crossKernelPolynomial a (canonicalGridCut d₁ e₁ d₂ e₂)
      (canonicalLeftCut d₁ e₁ d₂ e₂) (canonicalRightCut d₁ e₁ d₂ e₂))

lemma fourGridPolynomial_one (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourGridPolynomial a (1 : S (d₁+d₂)) (1 : S (e₁+e₂)) d₁ e₁ d₂ e₂=
      fourCrossPolynomial a d₁ e₁ d₂ e₂ := by
  rw [fourGridPolynomial_factor a d₁ e₁ d₂ e₂ (firstCut d₁ d₂) (firstCut e₁ e₂)]
  simp only [tensorValue_restrictTensor,OneMemClass.coe_one,map_one,one_mul,fourCrossPolynomial]

lemma fourCrossPolynomial_invariant (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (σ : CellGroup d₁ e₁ × CellGroup d₂ e₂) :
    rename (sumAction (cellAction d₁ e₁) (cellAction d₂ e₂) σ)
      (fourCrossPolynomial a d₁ e₁ d₂ e₂)=fourCrossPolynomial a d₁ e₁ d₂ e₂ := by
  rw [←fourGridPolynomial_one]
  exact fourGridPolynomial_invariant _ _ _ _ _ _ _ _

noncomputable def fourCrossTensor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) :=
  separateFour d₁ e₁ d₂ e₂ (fourCrossPolynomial a d₁ e₁ d₂ e₂)

lemma fourValue_fourCrossTensor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourValue d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)=
      fourCrossPolynomial a d₁ e₁ d₂ e₂ :=
  fourValue_separateFour _ _ _ _ _ (fourCrossPolynomial_invariant _ _ _ _ _)

lemma separateFour_grid_factor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ d₂) (B : Cut e₁ e₂) (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)=
      fourInterchange d₁ e₁ d₂ e₂ (restrictTensor A f⊗ₜ[ℚ]restrictTensor B g)*
        fourCrossTensor a d₁ e₁ d₂ e₂ := by
  apply fourValue_injective
  rw [fourValue_separateFour _ _ _ _ _ (fourGridPolynomial_invariant _ _ _ _ _ _ _)]
  change _=fourValueAlg d₁ e₁ d₂ e₂ (_*_)
  rw [map_mul,fourValueAlg_apply,fourValueAlg_apply,fourValue_interchange,fourValue_fourCrossTensor]
  exact fourGridPolynomial_factor _ _ _ _ _ A B f g

end ElementaryPositivity.RawShuffle

end

end OAI
