import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.PrimitiveOperators
import OAI.Combinatorics.Chromatic.Shuffle.OriginalDegree
import OAI.Combinatorics.Chromatic.Shuffle.GlobalTensorDetection
import OAI.Combinatorics.Chromatic.Walls.UnitalGradeComparison

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open DimensionSplit ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

lemma globalPrimitive_iff_local (d : slopeDimensions c η hc θ) (hd : d.val≠0) (W : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val W) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,W) x ∈ globalPrimitives a c η hc θ ↔
      unitalGradeNonzeroEquiv a c η hc θ d.val hd W x ∈
        primitiveSpace a c η hc θ Fact.out d.val W := by
  rw [globalPrimitive_iff_split_zero a c η hc θ (d,W) hd x,
    primitiveSpace_iff_coproducts_zero]
  constructor
  · intro hx L R hL hR hde
    have hls : OnSlopeOrZero c η θ L.dim := Or.inr (SplitTree.slope_dim c η hc hL)
    have hrs : OnSlopeOrZero c η θ R.dim := Or.inr (SplitTree.slope_dim c η hc hR)
    let s : SlopeSplit c η hc θ d.val := ⟨ofPair L.dim R.dim hde,by
      constructor
      · exact hls
      · simpa only [right_ofPair] using hrs⟩
    have hz := hx s (SplitTree.dim_ne_zero hL) (by simpa only [s,right_ofPair] using SplitTree.dim_ne_zero hR)
    rw [globalSplitCoproduct_dimensions a c η hc θ (d,W) s L.dim R.dim rfl
      (right_ofPair _ _ hde) hls hrs hde x] at hz
    have hz' := (globalTensorGradeInclusion_injective a c η hc θ ⟨L.dim,hls⟩ ⟨R.dim,hrs⟩ W)
      (hz.trans (map_zero _).symm)
    have hcomp := unitalGradeCoproduct_nonzero a c η hc θ L.dim R.dim
      (SplitTree.dim_ne_zero hL) (SplitTree.dim_ne_zero hR) (hls.compatible hrs)
      ((SplitTree.slope_dim c η hc hL).trans (SplitTree.slope_dim c η hc hR).symm) W
      (unitalGradeCast a c η hc θ hde.symm rfl x)
    rw [hz',map_zero,unitalGradeNonzeroEquiv_cast a c η hc θ hde.symm hd] at hcomp
    exact hcomp.symm
  · intro hx s hl hr
    have hL : (SplitTree.leaf (left s.val)).OnSlope c η θ := ⟨hl,s.property.1.resolve_left hl⟩
    have hR : (SplitTree.leaf (right s.val)).OnSlope c η θ := ⟨hr,s.property.2.resolve_left hr⟩
    have hz := hx (.leaf (left s.val)) (.leaf (right s.val)) hL hR (left_add_right s.val)
    have hcomp := unitalGradeCoproduct_nonzero a c η hc θ (left s.val) (right s.val)
      hl hr (s.property.1.compatible s.property.2) (hL.2.trans hR.2.symm) W
      (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl x)
    rw [unitalGradeNonzeroEquiv_cast a c η hc θ (left_add_right s.val).symm hd,hz] at hcomp
    have hz' := (unitalTensorGradeNonzeroEquiv a c η hc θ (left s.val) (right s.val) hl hr W).injective
      (hcomp.trans (map_zero _).symm)
    change globalTensorGradeInclusion a c η hc θ _ _ _
      (unitalGradeCoproduct a c η hc θ _ _ _ _ (unitalGradeCast a c η hc θ _ _ x))=0
    rw [hz',map_zero]

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial CommonTranslation
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma derivativeS_component (d : I → ℕ) (ℓ : ℤ) (f : S d) :
    derivativeS d (componentS d ℓ f)=componentS d (ℓ-1) (derivativeS d f) := by
  classical
  rw [←sum_componentS d f]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hh : (derivativeS d (componentS d m f)).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) (m-1) := by
    rw [derivativeS_val]
    exact D_homogeneous _ _ (componentS_homogeneous d m f)
  rw [componentS_componentS,componentS_of_homogeneous d _ hh]
  by_cases h : ℓ=m
  · subst m
    simp
  · simp only [ite_eq_right h,ite_eq_right (by omega : ℓ-1≠m-1),map_zero]

lemma derivativeB_component (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (ℓ : ℤ) (f : B a μ d) :
    derivativeB a μ d (componentB a μ d ℓ f)=componentB a μ d (ℓ-1) (derivativeB a μ d f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change derivativeB a μ d (quotientAlg a μ d (componentS d ℓ f))=
      componentB a μ d (ℓ-1) (derivativeB a μ d (quotientAlg a μ d f))
    rw [derivativeB_mk,derivativeB_mk]
    change quotientAlg a μ d (derivativeS d (componentS d ℓ f))=
      quotientAlg a μ d (componentS d (ℓ-1) (derivativeS d f))
    rw [derivativeS_component]

omit [DecidableEq I] in
lemma meanS_homogeneous (d : I → ℕ) :
    (meanS d).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) 1 := by
  classical
  apply (weightedHomogeneousSubmodule ℚ (fun _ : (Σ i,Fin (d i))=>(1:ℤ)) 1).smul_mem
  exact IsWeightedHomogeneous.sum _ _ 1 (fun v _=>isWeightedHomogeneous_X ℚ (fun _=>(1:ℤ)) v)

omit [DecidableEq I] in
lemma componentS_mean (d : I → ℕ) (ℓ : ℤ) (f : S d) :
    componentS d (ℓ+1) (meanS d*f)=meanS d*componentS d ℓ f := by
  apply Subtype.ext
  change weightedHomogeneousComponent (fun _=>(1:ℤ)) (ℓ+1) ((meanS d).val*f.val)=_
  rw [add_comm ℓ 1,Homogeneity.component_mul _ _ (meanS_homogeneous d) ℓ]
  rfl

lemma meanMultiplyB_component (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (ℓ : ℤ) (f : B a μ d) :
    componentB a μ d (ℓ+1) (meanMultiplyB a μ d f)=meanMultiplyB a μ d (componentB a μ d ℓ f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change componentB a μ d (ℓ+1) (quotientAlg a μ d (meanS d)*quotientAlg a μ d f)=
      quotientAlg a μ d (meanS d)*quotientAlg a μ d (componentS d ℓ f)
    rw [←map_mul,←map_mul]
    change quotientAlg a μ d (componentS d (ℓ+1) (meanS d*f))=_
    rw [componentS_mean]

variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
lemma gradeDerivative_component (d : I → ℕ) (W ℓ : ℤ) (f : SourceAssociatedGrade a c η hc θ d W) :
    gradeDerivative a c η hc θ d W (associatedComponent a c η hc θ d W ℓ f)=
      associatedComponent a c η hc θ d W (ℓ-1) (gradeDerivative a c η hc θ d W f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    apply congrArg (LinearFiltration.mk (sourceFiltration a c η hc θ d W) (sourceFiltration a c η hc θ d (W+1)))
    apply Subtype.ext
    exact derivativeB_component a (SlopeArithmetic.slope c η) d ℓ f.val

lemma gradeMeanMultiply_component (d : I → ℕ) (W ℓ : ℤ) (f : SourceAssociatedGrade a c η hc θ d W) :
    associatedComponent a c η hc θ d W (ℓ+1) (gradeMeanMultiply a c η hc θ d W f)=
      gradeMeanMultiply a c η hc θ d W (associatedComponent a c η hc θ d W ℓ f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    apply congrArg (LinearFiltration.mk (sourceFiltration a c η hc θ d W) (sourceFiltration a c η hc θ d (W+1)))
    apply Subtype.ext
    exact meanMultiplyB_component a (SlopeArithmetic.slope c η) d ℓ f.val

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)

noncomputable local instance : AddCommGroup (primitiveSpace a c η hc θ hχ d W) := Submodule.addCommGroup _
noncomputable local instance : Module ℚ (primitiveSpace a c η hc θ hχ d W) := Submodule.module _
noncomputable local instance : AddCommGroup (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) := Submodule.addCommGroup _
noncomputable local instance : Module ℚ (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) := Submodule.module _

noncomputable def primitiveComponent (ℓ : ℤ) :
    Module.End ℚ (primitiveSpace a c η hc θ hχ d W) :=
  LinearFiltration.restrict _ _ (associatedComponent a c η hc θ d W ℓ)
    (associatedComponent_primitive a c η hc θ hχ d W ℓ)

lemma primitiveDerivative_component (ℓ : ℤ) (x : primitiveSpace a c η hc θ hχ d W) :
    primitiveDerivative a c η hc θ hχ d W (primitiveComponent a c η hc θ hχ d W ℓ x)=
      primitiveComponent a c η hc θ hχ d W (ℓ-1) (primitiveDerivative a c η hc θ hχ d W x) :=
  Subtype.ext (gradeDerivative_component a c η hc θ d W ℓ x.val)

lemma primitiveMeanMultiply_component (ℓ : ℤ) (x : primitiveSpace a c η hc θ hχ d W) :
    primitiveComponent a c η hc θ hχ d W (ℓ+1) (primitiveMeanMultiply a c η hc θ hχ d W x)=
      primitiveMeanMultiply a c η hc θ hχ d W (primitiveComponent a c η hc θ hχ d W ℓ x) :=
  Subtype.ext (gradeMeanMultiply_component a c η hc θ d W ℓ x.val)

lemma primitiveComponent_ker (ℓ : ℤ) (x : primitiveSpace a c η hc θ hχ d W)
    (hx : x∈LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) :
    primitiveComponent a c η hc θ hχ d W ℓ x∈LinearMap.ker (primitiveDerivative a c η hc θ hχ d W) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [primitiveDerivative_component,hx,map_zero]

noncomputable def stringBaseComponent (ℓ : ℤ) :
    Module.End ℚ (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) :=
  LinearFiltration.restrict _ _ (primitiveComponent a c η hc θ hχ d W ℓ)
    (primitiveComponent_ker a c η hc θ hχ d W ℓ)

lemma stringBaseComponent_twice (ℓ m : ℤ)
    (x : LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) :
    stringBaseComponent a c η hc θ hχ d W ℓ (stringBaseComponent a c η hc θ hχ d W m x)=
      if ℓ=m then stringBaseComponent a c η hc θ hχ d W m x else 0 := by
  split_ifs with h
  · apply Subtype.ext; apply Subtype.ext
    exact (associatedComponent_twice a c η hc θ d W ℓ m x.val.val).trans (ite_eq_left h)
  · apply Subtype.ext; apply Subtype.ext
    exact (associatedComponent_twice a c η hc θ d W ℓ m x.val.val).trans (ite_eq_right h)

noncomputable def homogeneousStringBases : Set (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) :=
  {x | ∃ ℓ,stringBaseComponent a c η hc θ hχ d W ℓ x=x}

lemma homogeneousStringBases_span :
    ⊤ ≤ Submodule.span ℚ (homogeneousStringBases a c η hc θ hχ d W) := by
  intro x hx
  obtain ⟨s,hs,he⟩:=associatedComponent_finite_decomposition a c η hc θ d W x.val.val
  have he' : (∑ ℓ∈s,stringBaseComponent a c η hc θ hχ d W ℓ x)=x := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Submodule.coe_sum]
    exact he
  rw [←he']
  apply Submodule.sum_mem
  intro ℓ hℓ
  apply Submodule.subset_span
  exact ⟨ℓ,(stringBaseComponent_twice a c η hc θ hχ d W ℓ ℓ x).trans (ite_eq_left rfl)⟩

noncomputable def StringBaseIndex : Type _ :=
  (linearIndepOn_empty ℚ (id : LinearMap.ker (primitiveDerivative a c η hc θ hχ d W) → _)).extend
    (Set.empty_subset (homogeneousStringBases a c η hc θ hχ d W))

noncomputable def homogeneousStringBaseBasis :
    Module.Basis (StringBaseIndex a c η hc θ hχ d W) ℚ
      (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) :=
  Module.Basis.ofSpan (homogeneousStringBases_span a c η hc θ hχ d W)

lemma homogeneousStringBaseBasis_exists_degree (i : StringBaseIndex a c η hc θ hχ d W) :
    ∃ ℓ,stringBaseComponent a c η hc θ hχ d W ℓ (homogeneousStringBaseBasis a c η hc θ hχ d W i)=
      homogeneousStringBaseBasis a c η hc θ hχ d W i :=
  Module.Basis.ofSpan_subset (homogeneousStringBases_span a c η hc θ hχ d W) (Set.mem_range_self i)

noncomputable def stringBaseDegree (i : StringBaseIndex a c η hc θ hχ d W) : ℤ :=
  (homogeneousStringBaseBasis_exists_degree a c η hc θ hχ d W i).choose

lemma stringBaseDegree_spec (i : StringBaseIndex a c η hc θ hχ d W) :
    primitiveComponent a c η hc θ hχ d W (stringBaseDegree a c η hc θ hχ d W i)
      (homogeneousStringBaseBasis a c η hc θ hχ d W i).val=
      (homogeneousStringBaseBasis a c η hc θ hχ d W i).val :=
  congrArg Subtype.val (homogeneousStringBaseBasis_exists_degree a c η hc θ hχ d W i).choose_spec

lemma stringBaseDegree_nonneg (i : StringBaseIndex a c η hc θ hχ d W) :
    0 ≤ stringBaseDegree a c η hc θ hχ d W i := by
  by_contra h
  have hs:=congrArg Subtype.val (stringBaseDegree_spec a c η hc θ hχ d W i)
  change associatedComponent a c η hc θ d W _ _=_ at hs
  rw [associatedComponent_negative a c η hc θ d W _ (lt_of_not_ge h),LinearMap.zero_apply] at hs
  exact (homogeneousStringBaseBasis a c η hc θ hχ d W).ne_zero i
    (Subtype.ext (Subtype.ext hs.symm))

lemma primitiveMeanMultiply_pow_component (ℓ : ℤ) (n : ℕ) (x : primitiveSpace a c η hc θ hχ d W)
    (hx : primitiveComponent a c η hc θ hχ d W ℓ x=x) :
    primitiveComponent a c η hc θ hχ d W (ℓ+n) ((primitiveMeanMultiply a c η hc θ hχ d W^n) x)=
      ((primitiveMeanMultiply a c η hc θ hχ d W^n) x) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,add_zero,pow_zero,Module.End.one_apply] using hx
  | succ n ih =>
    rw [Nat.cast_succ,←add_assoc,pow_succ',Module.End.mul_apply,primitiveMeanMultiply_component,ih]

noncomputable def homogeneousPrimitiveStringBasis (hd : d≠0) :
    Module.Basis (Σ _ : ℕ,StringBaseIndex a c η hc θ hχ d W) ℚ
      (primitiveSpace a c η hc θ hχ d W) :=
  (Finsupp.basis (fun _ : ℕ=>homogeneousStringBaseBasis a c η hc θ hχ d W)).map
    (primitiveStringDecomposition a c η hc θ hχ d hd W)

lemma homogeneousPrimitiveStringBasis_apply (hd : d≠0)
    (i : Σ _ : ℕ,StringBaseIndex a c η hc θ hχ d W) :
    homogeneousPrimitiveStringBasis a c η hc θ hχ d W hd i=
      (primitiveMeanMultiply a c η hc θ hχ d W^i.1) (homogeneousStringBaseBasis a c η hc θ hχ d W i.2).val := by
  rw [homogeneousPrimitiveStringBasis,Module.Basis.map_apply,Finsupp.coe_basis]
  exact PrimitiveStrings.evaluate_single _ _ _ _

lemma homogeneousPrimitiveStringBasis_degree (hd : d≠0)
    (i : Σ _ : ℕ,StringBaseIndex a c η hc θ hχ d W) :
    primitiveComponent a c η hc θ hχ d W (stringBaseDegree a c η hc θ hχ d W i.2+i.1)
      (homogeneousPrimitiveStringBasis a c η hc θ hχ d W hd i)=
      homogeneousPrimitiveStringBasis a c η hc θ hχ d W hd i := by
  rw [homogeneousPrimitiveStringBasis_apply]
  exact primitiveMeanMultiply_pow_component a c η hc θ hχ d W _ _ _
    (stringBaseDegree_spec a c η hc θ hχ d W i.2)

end ElementaryPositivity.RawShuffle

end

end OAI
