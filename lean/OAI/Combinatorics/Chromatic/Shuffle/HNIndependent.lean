import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNDetectorBasics
import OAI.Combinatorics.Chromatic.Walls.TriangularDirectSum

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

noncomputable def hnPolynomialExpansion (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    (⨁ l : HNIndex c η d,HNTensor a c η l.val) →ₗ[ℚ] S d :=
  DirectSum.toModule ℚ _ _ (fun l=>(dimensionCast l.property.1).comp (hnPolynomial a c η σ l.val))

lemma hnExpansionRaw_polynomial (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    hnExpansionRaw a c η σ d=(rawLof a d).comp (hnPolynomialExpansion a c η σ d) := by
  apply DirectSum.linearMap_ext
  intro l
  apply LinearMap.ext
  intro x
  simp only [hnExpansionRaw,hnPolynomialExpansion,LinearMap.comp_apply,DirectSum.toModule_lof]
  rw [hnWordMap_polynomial,LinearMap.comp_apply,dimensionCast_eq_castS,rawLof_cast]

instance hnIndex_strict (d : I → ℕ) :
    IsStrictOrder (HNIndex c η d) (fun l r=>List.Lex (hnKeyLT c η) l.val r.val) where
  irrefl := fun l=>List.lex_irrefl (hnKeyLT_irrefl c η) l.val
  trans := fun _ _ _=>List.lex_trans (hnKeyLT_trans c η)

theorem hnPolynomialExpansion_injective (hc : ∀ i,0<c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ) (d : I → ℕ) :
    Function.Injective (hnPolynomialExpansion a c η σ d) := by
  classical
  choose D hD using fun l : HNIndex c η d=>hn_detector_exists a c η hc σ hσ l.val l.property.2
  let F := fun l : HNIndex c η d=>(dimensionCast l.property.1).comp (hnPolynomial a c η σ l.val)
  let T := fun l : HNIndex c η d=>(D l).comp (dimensionCast l.property.1.symm)
  apply triangular_directSum_injective (fun l r : HNIndex c η d=>List.Lex (hnKeyLT c η) l.val r.val) F T
  · intro l x
    change D l (dimensionCast l.property.1.symm (dimensionCast l.property.1 (hnPolynomial a c η σ l.val x)))=x
    rw [dimensionCast_trans]
    exact LinearMap.congr_fun (hD l).diagonal x
  · intro l r hne hn x
    change D l (dimensionCast l.property.1.symm (dimensionCast r.property.1 (hnPolynomial a c η σ r.val x)))=0
    rw [dimensionCast_trans,dimensionCast_eq_castS]
    exact (hD l).off r.val r.property.2 (r.property.1.trans l.property.1.symm) hn
      (fun h=>hne (Subtype.ext h)) x

lemma hnPolynomialExpansion_surjective (hc : ∀ i,0<c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ) (d : I → ℕ) :
    Function.Surjective (hnPolynomialExpansion a c η σ d) := by
  intro x
  obtain ⟨y,hy⟩:=hnExpansion_surjective a c η hc σ hσ d ⟨rawLof a d x,⟨x,rfl⟩⟩
  have H : hnExpansionRaw a c η σ d y=rawLof a d x := congrArg Subtype.val hy
  rw [hnExpansionRaw_polynomial,LinearMap.comp_apply] at H
  exact ⟨y,DirectSum.of_injective d H⟩

noncomputable def hnOrderedEquiv (hc : ∀ i,0<c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ) (d : I → ℕ) :
    (⨁ l : HNIndex c η d,HNTensor a c η l.val) ≃ₗ[ℚ] S d :=
  LinearEquiv.ofBijective (hnPolynomialExpansion a c η σ d)
    ⟨hnPolynomialExpansion_injective a c η hc σ hσ d,hnPolynomialExpansion_surjective a c η hc σ hσ d⟩
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)

noncomputable def degreeQuotient (k : ℤ) :
    LinearMap.range (componentS d k) →ₗ[ℚ] gradeB a μ d k :=
  ((destabilizingSpace a μ d).mkQ.comp (LinearMap.range (componentS d k)).subtype).codRestrict _ (by
    rintro ⟨f,⟨g,rfl⟩⟩
    exact ⟨(destabilizingSpace a μ d).mkQ g,rfl⟩)
lemma degreeQuotient_surjective (k : ℤ) : Function.Surjective (degreeQuotient a μ d k) := by
  rintro ⟨f,x,rfl⟩
  obtain ⟨g,rfl⟩:=(destabilizingSpace a μ d).mkQ_surjective x
  exact ⟨⟨componentS d k g,⟨g,rfl⟩⟩,rfl⟩

local instance degreeFree (k : ℤ) : Module.Free ℚ (gradeB a μ d k) :=
  Module.Free.of_divisionRing ℚ _
local instance degreeProjective (k : ℤ) : Module.Projective ℚ (gradeB a μ d k) :=
  Module.Projective.of_free

noncomputable def degreeSection (k : ℤ) :
    gradeB a μ d k →ₗ[ℚ] LinearMap.range (componentS d k) :=
  (LinearMap.exists_rightInverse_of_surjective (degreeQuotient a μ d k)
    (LinearMap.range_eq_top.mpr (degreeQuotient_surjective a μ d k))).choose
lemma degreeSection_rightInverse (k : ℤ) (x : gradeB a μ d k) :
    degreeQuotient a μ d k (degreeSection a μ d k x)=x :=
  LinearMap.congr_fun (LinearMap.exists_rightInverse_of_surjective (degreeQuotient a μ d k)
    (LinearMap.range_eq_top.mpr (degreeQuotient_surjective a μ d k))).choose_spec x

noncomputable def gradeBEquiv : (⨁ k : ℤ,gradeB a μ d k) ≃ₗ[ℚ] B a μ d :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (gradeB a μ d)) (gradeB_internal a μ d)
lemma gradeBEquiv_of (k : ℤ) (x : gradeB a μ d k) :
    gradeBEquiv a μ d (DirectSum.lof ℚ ℤ (fun k => ↥(gradeB a μ d k)) k x)=x.val :=
  DirectSum.coeLinearMap_of _ _ _
lemma gradeBEquiv_symm_homogeneous (k : ℤ) (x : gradeB a μ d k) :
    (gradeBEquiv a μ d).symm x.val=DirectSum.lof ℚ ℤ (fun k => ↥(gradeB a μ d k)) k x := by
  apply (gradeBEquiv a μ d).injective
  rw [LinearEquiv.apply_symm_apply,gradeBEquiv_of]

noncomputable def homogeneousSection : B a μ d →ₗ[ℚ] S d :=
  (DirectSum.toModule ℚ _ _ (fun k=>(LinearMap.range (componentS d k)).subtype.comp
    (degreeSection a μ d k))).comp (gradeBEquiv a μ d).symm.toLinearMap
lemma homogeneousSection_on_grade (k : ℤ) (x : gradeB a μ d k) :
    homogeneousSection a μ d x.val=(degreeSection a μ d k x).val := by
  unfold homogeneousSection
  rw [LinearMap.comp_apply,LinearEquiv.coe_coe,gradeBEquiv_symm_homogeneous,DirectSum.toModule_lof]
  rfl
lemma homogeneousSection_rightInverse :
    Function.RightInverse (homogeneousSection a μ d) (destabilizingSpace a μ d).mkQ := by
  have H : (destabilizingSpace a μ d).mkQ.comp
      (DirectSum.toModule ℚ ℤ (S d) (fun k=>(LinearMap.range (componentS d k)).subtype.comp
        (degreeSection a μ d k)))=(gradeBEquiv a μ d).toLinearMap := by
    apply DirectSum.linearMap_ext
    intro k
    apply LinearMap.ext
    intro x
    change (destabilizingSpace a μ d).mkQ
      ((DirectSum.toModule ℚ ℤ (S d) (fun k=>(LinearMap.range (componentS d k)).subtype.comp
        (degreeSection a μ d k))) (DirectSum.lof ℚ ℤ (fun k => ↥(gradeB a μ d k)) k x))=_
    rw [DirectSum.toModule_lof]
    exact (congrArg Subtype.val (degreeSection_rightInverse a μ d k x)).trans (gradeBEquiv_of a μ d k x).symm
  intro x
  exact (LinearMap.congr_fun H ((gradeBEquiv a μ d).symm x)).trans (LinearEquiv.apply_symm_apply _ x)
lemma homogeneousSection_graded (k : ℤ) (x : B a μ d) (hx : x∈gradeB a μ d k) :
    (homogeneousSection a μ d x).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k := by
  rw [homogeneousSection_on_grade a μ d k ⟨x,hx⟩]
  obtain ⟨g,hg⟩:=(degreeSection a μ d k ⟨x,hx⟩).property
  rw [←hg]
  exact componentS_homogeneous d k g
end ElementaryPositivity.RawShuffle

end

end OAI
