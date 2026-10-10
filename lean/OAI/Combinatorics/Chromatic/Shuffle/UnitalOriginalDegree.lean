import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalPrimitiveStrings

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)

lemma unitalSourceFiltration_component_mem (d : I → ℕ) (W ℓ : ℤ)
    (f : B a (slope c η) d) (hf : f∈unitalSourceFiltration a c η hc θ d W) :
    componentB a (slope c η) d ℓ f∈unitalSourceFiltration a c η hc θ d W := by
  classical
  by_cases hd : d=0
  · by_cases hw : W≤0
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_left hw,Submodule.mem_top]
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_right hw,Submodule.mem_bot] at hf ⊢
      rw [hf,map_zero]
  · rw [unitalSourceFiltration_nonzero a c η hc θ d hd W] at hf ⊢
    exact sourceFiltration_component_mem a c η hc θ d W ℓ f hf

noncomputable def unitalAssociatedComponent (d : I → ℕ) (W ℓ : ℤ) :
    Module.End ℚ (UnitalSourceGrade a c η hc θ d W) :=
  LinearFiltration.map _ _ _ _ (componentB a (slope c η) d ℓ)
    (unitalSourceFiltration_component_mem a c η hc θ d W ℓ)
    (unitalSourceFiltration_component_mem a c η hc θ d (W+1) ℓ)

lemma unitalAssociatedComponent_mk (d : I → ℕ) (W ℓ : ℤ)
    (f : unitalSourceFiltration a c η hc θ d W) :
    unitalAssociatedComponent a c η hc θ d W ℓ (Submodule.Quotient.mk f)=
      (Submodule.Quotient.mk ⟨componentB a (slope c η) d ℓ f.val,
        unitalSourceFiltration_component_mem a c η hc θ d W ℓ f.val f.property⟩ :
      UnitalSourceGrade a c η hc θ d W) := rfl

lemma unitalAssociatedComponent_twice (d : I → ℕ) (W ℓ m : ℤ)
    (f : UnitalSourceGrade a c η hc θ d W) :
    unitalAssociatedComponent a c η hc θ d W ℓ (unitalAssociatedComponent a c η hc θ d W m f)=
      if ℓ=m then unitalAssociatedComponent a c η hc θ d W m f else 0 := by
  classical
  by_cases h : ℓ=m
  · rw [ite_eq_left h]
    induction f using Submodule.Quotient.induction_on with
    | H f =>
      simp only [unitalAssociatedComponent_mk]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact (componentB_componentB a _ d ℓ m f.val).trans (ite_eq_left h)
  · rw [ite_eq_right h]
    induction f using Submodule.Quotient.induction_on with
    | H f =>
      rw [unitalAssociatedComponent_mk,unitalAssociatedComponent_mk]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change componentB a _ d ℓ (componentB a _ d m f.val)∈unitalSourceFiltration a c η hc θ d (W+1)
      rw [componentB_componentB,ite_eq_right h]
      exact Submodule.zero_mem _

lemma unitalAssociatedComponent_nonzero (d : I → ℕ) (hd : d≠0) (W ℓ : ℤ)
    (x : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeNonzeroEquiv a c η hc θ d hd W (unitalAssociatedComponent a c η hc θ d W ℓ x)=
      associatedComponent a c η hc θ d W ℓ (unitalGradeNonzeroEquiv a c η hc θ d hd W x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [unitalAssociatedComponent_mk,unitalGradeNonzeroEquiv_mk,unitalGradeNonzeroEquiv_mk,associatedComponent_mk]

noncomputable def unitalOriginalHomogeneous (d : I → ℕ) (W ℓ : ℤ) :
    Submodule ℚ (UnitalSourceGrade a c η hc θ d W) :=
  LinearMap.ker (unitalAssociatedComponent a c η hc θ d W ℓ-LinearMap.id)

lemma mem_unitalOriginalHomogeneous (d : I → ℕ) (W ℓ : ℤ) (x : UnitalSourceGrade a c η hc θ d W) :
    x∈unitalOriginalHomogeneous a c η hc θ d W ℓ ↔ unitalAssociatedComponent a c η hc θ d W ℓ x=x := by
  simp only [unitalOriginalHomogeneous,LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]

lemma unitalOriginalHomogeneous_representative (d : I → ℕ) (W ℓ : ℤ)
    (x : UnitalSourceGrade a c η hc θ d W) (hx : x∈unitalOriginalHomogeneous a c η hc θ d W ℓ) :
    ∃ f : unitalSourceFiltration a c η hc θ d W,
      f.val∈gradeB a (slope c η) d ℓ ∧ Submodule.Quotient.mk f=x := by
  obtain ⟨f,rfl⟩:=(LinearFiltration.next _ _).mkQ_surjective x
  refine ⟨⟨componentB a (slope c η) d ℓ f.val,
    unitalSourceFiltration_component_mem a c η hc θ d W ℓ f.val f.property⟩,⟨f.val,rfl⟩,?_⟩
  exact (mem_unitalOriginalHomogeneous a c η hc θ d W ℓ _).mp hx

lemma unitalOriginalHomogeneous_mk (d : I → ℕ) (W ℓ : ℤ)
    (f : unitalSourceFiltration a c η hc θ d W) (hf : f.val∈gradeB a (slope c η) d ℓ) :
    (Submodule.Quotient.mk f : UnitalSourceGrade a c η hc θ d W)∈
      unitalOriginalHomogeneous a c η hc θ d W ℓ := by
  apply (mem_unitalOriginalHomogeneous a c η hc θ d W ℓ _).mpr
  rw [unitalAssociatedComponent_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact (mem_gradeB_iff a (slope c η) d ℓ f.val).mp hf

lemma shuffleBUnit_graded (d e : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (m n : ℤ)
    (f : B a (slope c η) d) (g : B a (slope c η) e)
    (hf : f∈gradeB a (slope c η) d m) (hg : g∈gradeB a (slope c η) e n) :
    shuffleBUnit a c η hc d e hs f g∈gradeB a (slope c η) (d+e) (m+n-eulerForm a d e) := by
  obtain ⟨f,hfp,rfl⟩:=gradeB_homogeneous_representative a _ d m f hf
  obtain ⟨g,hgp,rfl⟩:=gradeB_homogeneous_representative a _ e n g hg
  rw [shuffleBUnit_mk,mem_gradeB_iff,componentB_mk,
    componentS_of_homogeneous _ _ (shufflePolynomial_homogeneous a f g hfp hgp),ite_eq_left rfl]

lemma unitalGradeShuffle_original (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (U V m n : ℤ)
    (x : UnitalSourceGrade a c η hc θ d U) (y : UnitalSourceGrade a c η hc θ e V)
    (hx : x∈unitalOriginalHomogeneous a c η hc θ d U m)
    (hy : y∈unitalOriginalHomogeneous a c η hc θ e V n) :
    unitalGradeShuffle a c η hc θ hχ d e hd he U V x y∈
      unitalOriginalHomogeneous a c η hc θ (d+e) (U+V) (m+n-eulerForm a d e) := by
  obtain ⟨x,hfx,rfl⟩:=unitalOriginalHomogeneous_representative a c η hc θ d U m x hx
  obtain ⟨y,hgy,rfl⟩:=unitalOriginalHomogeneous_representative a c η hc θ e V n y hy
  rw [unitalGradeShuffle_mk]
  exact unitalOriginalHomogeneous_mk a c η hc θ _ _ _ _
    (shuffleBUnit_graded a c η hc d e (hd.compatible he) m n x.val y.val hfx hgy)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [hχ : Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def globalOriginalHomogeneous (k : SlopeWeight c η hc θ) (ℓ : ℤ) :
    Submodule ℚ (UnitalShuffle a c η hc θ) :=
  (unitalOriginalHomogeneous a c η hc θ k.1.val k.2 ℓ).map
    (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k)

lemma globalOriginalHomogeneous_mul {k l : SlopeWeight c η hc θ} {m n : ℤ}
    {x y : UnitalShuffle a c η hc θ}
    (hx : x∈globalOriginalHomogeneous a c η hc θ k m)
    (hy : y∈globalOriginalHomogeneous a c η hc θ l n) :
    x*y∈globalOriginalHomogeneous a c η hc θ (k+l) (m+n-eulerForm a k.1.val l.1.val) := by
  obtain ⟨x,hx,rfl⟩:=hx
  obtain ⟨y,hy,rfl⟩:=hy
  exact ⟨GradedMonoid.GMul.mul x y,
    unitalGradeShuffle_original a c η hc θ hχ.out k.1.val l.1.val k.1.property l.1.property k.2 l.2 m n x y hx hy,
    (globalLof_mul a c η hc θ k l x y).symm⟩

lemma gradeB_one (d : I → ℕ) : (1 : B a (slope c η) d)∈gradeB a (slope c η) d 0 := by
  change (destabilizingSpace a (slope c η) d).mkQ (1 : S d)∈_
  rw [mem_gradeB_iff,componentB_mk,componentS_of_homogeneous _ _ (MvPolynomial.isWeightedHomogeneous_one ℚ (fun _=>(1:ℤ))),ite_eq_left rfl]

omit hχ in
lemma globalOriginalHomogeneous_one : (1 : UnitalShuffle a c η hc θ)∈globalOriginalHomogeneous a c η hc θ 0 0 := by
  refine ⟨unitalGradeOne a c η hc θ,?_,rfl⟩
  exact unitalOriginalHomogeneous_mk a c η hc θ 0 0 0 _ (gradeB_one a c η 0)

lemma localPrimitiveGlobal_original (k : NonzeroSlopeWeight c η hc θ) (ℓ : ℤ)
    (x : primitiveSpace a c η hc θ hχ.out k.val.1.val k.val.2)
    (hx : associatedComponent a c η hc θ k.val.1.val k.val.2 ℓ x.val=x.val) :
    localPrimitiveGlobal a c η hc θ k x∈globalOriginalHomogeneous a c η hc θ k.val ℓ := by
  refine ⟨localPrimitiveInclusion a c η hc θ k x,?_,rfl⟩
  apply (mem_unitalOriginalHomogeneous a c η hc θ _ _ _ _).mpr
  apply (unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2).injective
  rw [unitalAssociatedComponent_nonzero]
  change associatedComponent a c η hc θ k.val.1.val k.val.2 ℓ
    ((unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2)
    ((unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2).symm x.val))=_
  rw [LinearEquiv.apply_symm_apply]
  simpa only [localPrimitiveInclusion,LinearMap.comp_apply,Submodule.subtype_apply,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using hx

noncomputable def globalStringPolynomialDegree (i : GlobalStringIndex a c η hc θ) : ℤ :=
  stringBaseDegree a c η hc θ hχ.out i.1.val.1.val i.1.val.2 i.2.2+i.2.1

lemma globalStringFamily_original (i : GlobalStringIndex a c η hc θ) :
    globalStringFamily a c η hc θ i∈globalOriginalHomogeneous a c η hc θ i.1.val
      (globalStringPolynomialDegree a c η hc θ i) := by
  apply localPrimitiveGlobal_original a c η hc θ
  exact congrArg Subtype.val (homogeneousPrimitiveStringBasis_degree a c η hc θ hχ.out
    i.1.val.1.val i.1.val.2 i.1.property i.2)

omit [DecidableEq I] in
lemma eulerForm_slopeDimensions_symm (d e : slopeDimensions c η hc θ) :
    eulerForm a d.val e.val=eulerForm a e.val d.val := by
  by_cases hd : d.val=0
  · rw [hd]; simp [eulerForm]
  by_cases he : e.val=0
  · rw [he]; simp [eulerForm]
  exact hχ.out _ _ hd he (d.property.resolve_left hd) (e.property.resolve_left he)

omit [DecidableEq I] in
lemma doubleShift_product (d e : slopeDimensions c η hc θ) (m n : ℤ) :
    2*(m+n-eulerForm a d.val e.val)+eulerForm a (d+e).val (d+e).val=
      (2*m+eulerForm a d.val d.val)+(2*n+eulerForm a e.val e.val) := by
  change 2*(m+n-eulerForm a d.val e.val)+eulerForm a (d.val+e.val) (d.val+e.val)=_
  rw [eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,eulerForm_slopeDimensions_symm a c η hc θ e d]
  ring

variable {J : Type*}
noncomputable def wordPolynomialDegree (w : J → SlopeWeight c η hc θ) (p : J → ℤ) : List J → ℤ
  | [] => 0
  | i::l => p i + wordPolynomialDegree w p l-eulerForm a (w i).1.val (wordWeight c η hc θ w l).1.val

lemma primitiveWord_original (w : J → SlopeWeight c η hc θ) (p : J → ℤ)
    (b : J → UnitalShuffle a c η hc θ)
    (hb : ∀ i,b i∈globalOriginalHomogeneous a c η hc θ (w i) (p i)) (l : List J) :
    primitiveWord a c η hc θ b l∈globalOriginalHomogeneous a c η hc θ
      (wordWeight c η hc θ w l) (wordPolynomialDegree a c η hc θ w p l) := by
  induction l with
  | nil => exact globalOriginalHomogeneous_one a c η hc θ
  | cons i l ih => exact globalOriginalHomogeneous_mul a c η hc θ (hb i) ih

omit [DecidableEq I] in
lemma wordPolynomialDegree_shift (w : J → SlopeWeight c η hc θ) (p : J → ℤ) (l : List J) :
    2*wordPolynomialDegree a c η hc θ w p l+
      eulerForm a (wordWeight c η hc θ w l).1.val (wordWeight c η hc θ w l).1.val=
    (l.map (fun i=>2*p i+eulerForm a (w i).1.val (w i).1.val)).sum := by
  induction l with
  | nil => simp [wordPolynomialDegree,wordWeight,eulerForm]
  | cons i l ih =>
    change 2*(p i+wordPolynomialDegree a c η hc θ w p l-
      eulerForm a (w i).1.val (wordWeight c η hc θ w l).1.val)+
      eulerForm a ((w i).1+(wordWeight c η hc θ w l).1).val
        ((w i).1+(wordWeight c η hc θ w l).1).val=_
    rw [doubleShift_product,ih]
    rfl

lemma globalStringPBWBasis_original
    (l : PBWWord a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)) :
    globalStringPBWBasis a c η hc θ l∈globalOriginalHomogeneous a c η hc θ
      (wordWeight c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val) l.val)
      (wordPolynomialDegree a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)
        (globalStringPolynomialDegree a c η hc θ) l.val) := by
  rw [globalStringPBWBasis_apply]
  exact primitiveWord_original a c η hc θ _ _ _ (globalStringFamily_original a c η hc θ) l.val

end ElementaryPositivity.RawShuffle

end

end OAI
