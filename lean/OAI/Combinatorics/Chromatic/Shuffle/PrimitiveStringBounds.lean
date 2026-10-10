import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalHilbertGrading

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
noncomputable local instance : AddCommGroup (primitiveSpace a c η hc θ hχ d W) := Submodule.addCommGroup _
noncomputable local instance : Module ℚ (primitiveSpace a c η hc θ hχ d W) := Submodule.module _
noncomputable local instance : AddCommGroup (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) := Submodule.addCommGroup _
noncomputable local instance : Module ℚ (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) := Submodule.module _

lemma stringBaseComponent_basis (ℓ : ℤ) (i : StringBaseIndex a c η hc θ hχ d W) :
    stringBaseComponent a c η hc θ hχ d W ℓ (homogeneousStringBaseBasis a c η hc θ hχ d W i)=
      if stringBaseDegree a c η hc θ hχ d W i=ℓ then homogeneousStringBaseBasis a c η hc θ hχ d W i else 0 := by
  have hs : stringBaseComponent a c η hc θ hχ d W (stringBaseDegree a c η hc θ hχ d W i)
      (homogeneousStringBaseBasis a c η hc θ hχ d W i)=homogeneousStringBaseBasis a c η hc θ hχ d W i :=
    Subtype.ext (stringBaseDegree_spec a c η hc θ hχ d W i)
  calc
    _ = stringBaseComponent a c η hc θ hχ d W ℓ
        (stringBaseComponent a c η hc θ hχ d W (stringBaseDegree a c η hc θ hχ d W i)
          (homogeneousStringBaseBasis a c η hc θ hχ d W i)) := congrArg _ hs.symm
    _ = _ := by
      rw [stringBaseComponent_twice]
      by_cases h : stringBaseDegree a c η hc θ hχ d W i=ℓ
      · subst ℓ
        simpa using hs
      · simp [h,Ne.symm h]

noncomputable def stringBaseComponentEmbedding (ℓ : ℤ) :
    LinearMap.range (stringBaseComponent a c η hc θ hχ d W ℓ) →ₗ[ℚ]
      LinearMap.range (associatedComponent a c η hc θ d W ℓ) :=
  LinearMap.codRestrict _
    ((primitiveSpace a c η hc θ hχ d W).subtype.comp
      ((LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)).subtype.comp
        (LinearMap.range (stringBaseComponent a c η hc θ hχ d W ℓ)).subtype)) (by
      rintro ⟨x,y,rfl⟩
      exact ⟨y.val.val,rfl⟩)

lemma stringBaseComponentEmbedding_injective (ℓ : ℤ) :
    Function.Injective (stringBaseComponentEmbedding a c η hc θ hχ d W ℓ) := by
  intro x y h
  have H:=congrArg Subtype.val h
  change x.val.val.val=y.val.val.val at H
  exact Subtype.ext (Subtype.ext (Subtype.ext H))

lemma stringBaseComponent_finite (ℓ : ℤ) :
    Module.Finite ℚ (LinearMap.range (stringBaseComponent a c η hc θ hχ d W ℓ)) := by
  let := associatedComponent_finite a c η hc θ d W ℓ
  exact FiniteDimensional.of_injective (stringBaseComponentEmbedding a c η hc θ hχ d W ℓ)
    (stringBaseComponentEmbedding_injective a c η hc θ hχ d W ℓ)

lemma stringBaseDegree_finite (ℓ : ℤ) :
    Finite {i : StringBaseIndex a c η hc θ hχ d W // stringBaseDegree a c η hc θ hχ d W i=ℓ} := by
  let := stringBaseComponent_finite a c η hc θ hχ d W ℓ
  exact ElementaryPositivity.homogeneousBasis_finite (homogeneousStringBaseBasis a c η hc θ hχ d W)
    (stringBaseDegree a c η hc θ hχ d W) (stringBaseComponent a c η hc θ hχ d W)
    (stringBaseComponent_basis a c η hc θ hχ d W) ℓ

lemma stringBase_auxiliary_upper (hd : d≠0) (hs : slope c η d=θ)
    (i : StringBaseIndex a c η hc θ hχ d W) :
    W≤2*stringBaseDegree a c η hc θ hχ d W i+eulerForm a d d := by
  by_contra h
  have H:=congrArg Subtype.val (stringBaseDegree_spec a c η hc θ hχ d W i)
  change associatedComponent a c η hc θ d W _ _=_ at H
  rw [associatedComponent_upper a c η hc θ d hd hs W _ (lt_of_not_ge h),LinearMap.zero_apply] at H
  exact (homogeneousStringBaseBasis a c η hc θ hχ d W).ne_zero i
    (Subtype.ext (Subtype.ext H.symm))

lemma associatedGrade_eq_zero_below (hW : W < -interaction a d d)
    (x : SourceAssociatedGrade a c η hc θ d W) : x=0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change x.val∈sourceFiltration a c η hc θ d (W+1)
    exact sourceFiltration_antitone a c η hc θ d (show W+1≤-interaction a d d by omega)
      (by rw [sourceFiltration_lower]; trivial)

lemma stringBase_auxiliary_lower (i : StringBaseIndex a c η hc θ hχ d W) :
    -interaction a d d≤W := by
  by_contra h
  have H:=associatedGrade_eq_zero_below a c η hc θ d W (lt_of_not_ge h)
    (homogeneousStringBaseBasis a c η hc θ hχ d W i).val.val
  exact (homogeneousStringBaseBasis a c η hc θ hχ d W).ne_zero i (Subtype.ext (Subtype.ext H))

theorem stringStarts_bounded_finite (hd : d≠0) (hs : slope c η d=θ) (m : ℤ) :
    Finite {i : (Σ W : ℤ,StringBaseIndex a c η hc θ hχ d W) //
      stringBaseDegree a c η hc θ hχ d i.1 i.2 ≤ m} := by
  let f : {i : (Σ W : ℤ,StringBaseIndex a c η hc θ hχ d W) //
      stringBaseDegree a c η hc θ hχ d i.1 i.2 ≤ m} →
      (Σ w : {w : ℤ // w∈Set.Icc (-interaction a d d) (2*m+eulerForm a d d)},
        Σ ℓ : {ℓ : ℤ // ℓ∈Set.Icc 0 m},
          {j : StringBaseIndex a c η hc θ hχ d w.val // stringBaseDegree a c η hc θ hχ d w.val j=ℓ.val}) := fun i=>
    ⟨⟨i.val.1,stringBase_auxiliary_lower a c η hc θ hχ d _ i.val.2,
        (stringBase_auxiliary_upper a c η hc θ hχ d _ hd hs i.val.2).trans (by omega)⟩,
      ⟨stringBaseDegree a c η hc θ hχ d i.val.1 i.val.2,
        stringBaseDegree_nonneg a c η hc θ hχ d _ i.val.2,i.property⟩,⟨i.val.2,rfl⟩⟩
  let (w : {w : ℤ // w∈Set.Icc (-interaction a d d) (2*m+eulerForm a d d)})
    (ℓ : {ℓ : ℤ // ℓ∈Set.Icc 0 m}) := stringBaseDegree_finite a c η hc θ hχ d w.val ℓ.val
  apply Finite.of_injective f
  intro x y h
  have H:=congrArg (fun i=> (⟨i.1.val,i.2.2.val⟩ : Σ W : ℤ,StringBaseIndex a c η hc θ hχ d W)) h
  exact Subtype.ext H
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

lemma globalOriginal_nonzero_bounds (d : slopeDimensions c η hc θ) (hd : d.val≠0)
    (W k : ℤ) (x : UnitalShuffle a c η hc θ)
    (hx : x∈globalOriginalHomogeneous a c η hc θ (d,W) k) (hne : x≠0) :
    -interaction a d.val d.val≤W ∧ W≤2*k+eulerForm a d.val d.val := by
  obtain ⟨y,hy,rfl⟩:=hx
  have hyne : y≠0 := fun h=>hne (by rw [h,map_zero])
  let e := unitalGradeNonzeroEquiv a c η hc θ d.val hd W
  have he : e y≠0 := fun h=>hyne (e.injective (h.trans e.map_zero.symm))
  have H:=congrArg e (mem_unitalOriginalHomogeneous a c η hc θ d.val W k y |>.mp hy)
  rw [unitalAssociatedComponent_nonzero] at H
  constructor
  · by_contra h
    exact he (associatedGrade_eq_zero_below a c η hc θ d.val W (lt_of_not_ge h) (e y))
  · by_contra h
    rw [associatedComponent_upper a c η hc θ d.val hd (d.property.resolve_left hd) W k
      (lt_of_not_ge h),LinearMap.zero_apply] at H
    exact he H.symm

abbrev SlopeStringCoefficient (d : I → ℕ) (hs : slope c η d=θ) (k : ℤ) :=
  Σ W : ℤ,StringPBWGradedIndex a c η hc θ (⟨d,Or.inr hs⟩,W) k

lemma slopeStringCoefficient_bounds (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (k : ℤ) (i : SlopeStringCoefficient a c η hc θ d hs k) :
    -interaction a d d ≤ i.1 ∧ i.1 ≤ 2*k+eulerForm a d d := by
  exact globalOriginal_nonzero_bounds a c η hc θ ⟨d,Or.inr hs⟩ hd i.1 k
    (globalStringPBWBasis a c η hc θ i.2.val)
    ((congrArg (fun z : SlopeWeight c η hc θ × ℤ=>
      globalStringPBWBasis a c η hc θ i.2.val ∈ globalOriginalHomogeneous a c η hc θ z.1 z.2)
      i.2.property).mp (globalStringPBWBasis_original a c η hc θ i.2.val))
    ((globalStringPBWBasis a c η hc θ).ne_zero i.2.val)

def slopeStringCutoff (d : I → ℕ) (k : ℤ) : ℕ :=
  (2*k+eulerForm a d d+interaction a d d+1).toNat

omit [DecidableEq I] in
lemma slopeStringCutoff_bound (d : I → ℕ) (k : ℤ) :
    2*k+eulerForm a d d < -interaction a d d+slopeStringCutoff a d k := by
  unfold slopeStringCutoff
  omega

lemma sigmaSubtype_ext {A B : Type*} {p : A → B → Prop} {x y : Σ a,{b // p a b}}
    (h : x.1=y.1) (hval : x.2.val=y.2.val) : x=y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨a',b'⟩
  dsimp at h hval
  subst a'
  exact congrArg (Sigma.mk a) (Subtype.ext hval)

noncomputable def slopeStringCutoffEquiv (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) (k : ℤ) :
    SlopeStringCoefficient a c η hc θ d hs k ≃
      Σ j : Fin (slopeStringCutoff a d k),StringPBWGradedIndex a c η hc θ
        (⟨d,Or.inr hs⟩,-interaction a d d+j.val) k where
  toFun i := by
    have H:=slopeStringCoefficient_bounds a c η hc θ d hd hs k i
    have Hn:=slopeStringCutoff_bound a d k
    let j : Fin (slopeStringCutoff a d k):=⟨(i.1+interaction a d d).toNat,by omega⟩
    refine ⟨j,⟨i.2.val,?_⟩⟩
    have E : -interaction a d d+(j.val:ℤ)=i.1 := by dsimp [j]; omega
    rw [E]
    exact i.2.property
  invFun i := ⟨-interaction a d d+i.1.val,i.2⟩
  left_inv i := by
    apply sigmaSubtype_ext
    · dsimp; have H:=slopeStringCoefficient_bounds a c η hc θ d hd hs k i; omega
    · rfl
  right_inv i := by
    apply sigmaSubtype_ext
    · apply Fin.ext
      dsimp
      omega
    · rfl

lemma slopeStringCoefficient_finite (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) (k : ℤ) :
    Finite (SlopeStringCoefficient a c η hc θ d hs k) := by
  let (j : Fin (slopeStringCutoff a d k)) := stringPBWGradedIndex_finite a c η hc θ
    (⟨d,Or.inr hs⟩,-interaction a d d+j.val) k
  exact Finite.of_equiv _ (slopeStringCutoffEquiv a c η hc θ d hd hs k).symm

theorem slopeStringHilbert_coefficient (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) (k : ℤ) :
    Module.finrank ℚ (gradeB a (slope c η) d k)=
      Nat.card (SlopeStringCoefficient a c η hc θ d hs k) := by
  rw [Nat.card_congr (slopeStringCutoffEquiv a c η hc θ d hd hs k)]
  let (j : Fin (slopeStringCutoff a d k)) := stringPBWGradedIndex_finite a c η hc θ
    (⟨d,Or.inr hs⟩,-interaction a d d+j.val) k
  rw [Nat.card_sigma]
  exact (sourcePBWHilbert_coefficient a c η hc θ d hd hs k _ (slopeStringCutoff_bound a d k)).trans
    (Fin.sum_univ_eq_sum_range (fun j=>Nat.card (StringPBWGradedIndex a c η hc θ
      (⟨d,Or.inr hs⟩,-interaction a d d+j) k)) (slopeStringCutoff a d k)).symm
end ElementaryPositivity.RawShuffle

end

end OAI
