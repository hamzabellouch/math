import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalTensorGradeProduct

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

abbrev SlopeColumnGrid (c η : I → ℝ) (θ : ℝ) (d e α β : I → ℕ) :=
  {s : ColumnDimensionGrid d e α β //
    CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2)}

noncomputable def slopeColumnEquiv (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
    (d e : I → ℕ) :
    (Σ t : SlopeSplit c η hc θ (d+e),
      SlopeColumnGrid c η θ d e (left t.val) (right t.val)) ≃
      SlopeSplit c η hc θ d × SlopeSplit c η hc θ e :=
  Equiv.ofBijective
    (fun z=>(⟨z.2.val.val.1,⟨z.2.property.1,z.2.property.2.2.1⟩⟩,
      ⟨z.2.val.val.2,⟨z.2.property.2.1,z.2.property.2.2.2⟩⟩)) (by
    constructor
    · rintro ⟨t,s⟩ ⟨t',s'⟩ h
      have h₁ : s.val.val.1=s'.val.val.1 := congrArg (fun z=>z.1.val) h
      have h₂ : s.val.val.2=s'.val.val.2 := congrArg (fun z=>z.2.val) h
      have ht : t=t' := by
        apply Subtype.ext
        apply DimensionSplit.ext
        exact s.val.property.1.symm.trans ((congrArg₂ (fun p q=>left p+left q) h₁ h₂).trans s'.val.property.1)
      subst t'
      have hs : s=s' := Subtype.ext (Subtype.ext (Prod.ext h₁ h₂))
      exact congrArg (fun z=>Sigma.mk t z) hs
    · rintro ⟨p,q⟩
      have hsum : (left p.val+left q.val)+(right p.val+right q.val)=d+e := by
        calc
          _=(left p.val+right p.val)+(left q.val+right q.val) := by abel
          _=_ := by rw [left_add_right,left_add_right]
      let t : SlopeSplit c η hc θ (d+e) :=
        ⟨ofPair (left p.val+left q.val) (right p.val+right q.val) hsum,by
          simpa only [left_ofPair,right_ofPair] using
            And.intro (p.property.1.add hc q.property.1) (p.property.2.add hc q.property.2)⟩
      let s : SlopeColumnGrid c η θ d e (left t.val) (right t.val) :=
        ⟨⟨(p.val,q.val),by simp [t]⟩,p.property.1,q.property.1,p.property.2,q.property.2⟩
      exact ⟨⟨t,s⟩,rfl⟩)

lemma sum_dite_zero_subtype {A M : Type*} [Fintype A] [AddCommMonoid M]
    (p : A → Prop) [DecidablePred p] (F : ∀ x,p x → M) :
    (∑ x,if h : p x then F x h else 0)=∑ x : {x // p x},F x.val x.property := by
  have h := (Fintype.sum_subtype_add_sum_subtype p (fun x=>if h:p x then F x h else 0)).symm
  refine h.trans ?_
  have hn : (∑ x : {x // ¬p x},if hx:p x.val then F x.val hx else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact dite_eq_right x.property
  rw [hn,add_zero]
  exact Finset.sum_congr rfl (fun x _=>dite_eq_left x.property)

lemma sum_slope_column (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ)
    {M : Type*} [AddCommMonoid M]
    (F : SlopeSplit c η hc θ d → SlopeSplit c η hc θ e → M) :
    (∑ t : SlopeSplit c η hc θ (d+e),
      ∑ s : ColumnDimensionGrid d e (left t.val) (right t.val),
        if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
          F ⟨s.val.1,hon.1,hon.2.2.1⟩ ⟨s.val.2,hon.2.1,hon.2.2.2⟩
        else 0)=∑ p : SlopeSplit c η hc θ d,∑ q : SlopeSplit c η hc θ e,F p q := by
  calc
    _=∑ z : (Σ t : SlopeSplit c η hc θ (d+e),
        SlopeColumnGrid c η θ d e (left t.val) (right t.val)),
        F (slopeColumnEquiv c η hc θ d e z).1 (slopeColumnEquiv c η hc θ d e z).2 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro t _
      exact sum_dite_zero_subtype _ _
    _=∑ z : SlopeSplit c η hc θ d × SlopeSplit c η hc θ e,F z.1 z.2 :=
      Equiv.sum_comp (slopeColumnEquiv c η hc θ d e) (fun z=>F z.1 z.2)
    _=_ := Fintype.sum_prod_type _

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma globalSplitCoproduct_eq (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d : slopeDimensions c η hc θ) (W : ℤ)
    (s : SlopeSplit c η hc θ d.val) (x : UnitalSourceGrade a c η hc θ d.val W) :
    globalSplitCoproduct a c η hc θ (d,W) s x=
      globalTensorGradeInclusion a c η hc θ ⟨left s.val,s.property.1⟩ ⟨right s.val,s.property.2⟩ W
        (splitCoproductGrade a c η hc θ s.val s.property W x) := rfl

lemma globalColumnGradeTerm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d e : slopeDimensions c η hc θ) (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val U) (y : UnitalSourceGrade a c η hc θ e.val V)
    (t : SlopeSplit c η hc θ (d.val+e.val))
    (s : ColumnDimensionGrid d.val e.val (left t.val) (right t.val)) :
    globalTensorGradeInclusion a c η hc θ ⟨left t.val,t.property.1⟩ ⟨right t.val,t.property.2⟩ (U+V)
      (columnGradeTerm a c η hc θ hχ.out U V x y s)=
    if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
      globalSignedTensorMultiply a c η hc θ
        (globalSplitCoproduct a c η hc θ (d,U) ⟨s.val.1,hon.1,hon.2.2.1⟩ x)
        (globalSplitCoproduct a c η hc θ (e,V) ⟨s.val.2,hon.2.1,hon.2.2.2⟩ y)
    else 0 := by
  unfold columnGradeTerm
  split_ifs with hon
  · rw [globalSplitCoproduct_eq,globalSplitCoproduct_eq]
    have h := globalRawColumnProduct a c η hc θ
      (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2)
      (left t.val) (right t.val) hon s.property.1 s.property.2 t.property.1 t.property.2 U V
      (splitCoproductGrade a c η hc θ s.val.1 ⟨hon.1,hon.2.2.1⟩ U x)
      (splitCoproductGrade a c η hc θ s.val.2 ⟨hon.2.1,hon.2.2.2⟩ V y)
    simpa only [Subtype.coe_mk] using h
  · exact map_zero _

lemma globalSplitCoproduct_shuffle (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d e : slopeDimensions c η hc θ) (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val U) (y : UnitalSourceGrade a c η hc θ e.val V)
    (t : SlopeSplit c η hc θ (d.val+e.val)) :
    globalSplitCoproduct a c η hc θ (d+e,U+V) t
      (unitalGradeShuffle a c η hc θ hχ.out d.val e.val d.property e.property U V x y)=
      ∑ s : ColumnDimensionGrid d.val e.val (left t.val) (right t.val),
        if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
          globalSignedTensorMultiply a c η hc θ
            (globalSplitCoproduct a c η hc θ (d,U) ⟨s.val.1,hon.1,hon.2.2.1⟩ x)
            (globalSplitCoproduct a c η hc θ (e,V) ⟨s.val.2,hon.2.1,hon.2.2.2⟩ y)
        else 0 := by
  have h := congrArg (globalTensorGradeInclusion a c η hc θ
      ⟨left t.val,t.property.1⟩ ⟨right t.val,t.property.2⟩ (U+V))
    (unitalGradeCoproduct_shuffle_column a c η hc θ hχ.out (left_add_right t.val).symm
      d.property e.property t.property.1 t.property.2 U V x y)
  refine h.trans ?_
  rw [map_sum]
  exact Finset.sum_congr rfl (fun s _=>globalColumnGradeTerm a c η hc θ d e U V x y t s)

lemma globalCoproduct_mul_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d e : slopeDimensions c η hc θ) (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val U) (y : UnitalSourceGrade a c η hc θ e.val V) :
    globalCoproduct a c η hc θ
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,U) x *
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,V) y)=
      globalSignedTensorMultiply a c η hc θ
        (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,U) x))
        (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,V) y)) := by
  rw [←unitalLof_shuffle,globalCoproduct_lof,globalCoproduct_lof,globalCoproduct_lof]
  simp only [map_sum,LinearMap.sum_apply]
  calc
    _=∑ t : SlopeSplit c η hc θ (d.val+e.val),
      ∑ s : ColumnDimensionGrid d.val e.val (left t.val) (right t.val),
        if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
          globalSignedTensorMultiply a c η hc θ
            (globalSplitCoproduct a c η hc θ (d,U) ⟨s.val.1,hon.1,hon.2.2.1⟩ x)
            (globalSplitCoproduct a c η hc θ (e,V) ⟨s.val.2,hon.2.1,hon.2.2.2⟩ y)
        else 0 := by
      exact Finset.sum_congr rfl (fun t _=>globalSplitCoproduct_shuffle a c η hc θ d e U V x y t)
    _=_ := by
      have h := sum_slope_column c η hc θ d.val e.val
        (fun p q=>globalSignedTensorMultiply a c η hc θ
          (globalSplitCoproduct a c η hc θ (d,U) p x)
          (globalSplitCoproduct a c η hc θ (e,V) q y))
      exact h.trans (Finset.sum_comm)

theorem globalCoproduct_mul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (x y : UnitalShuffle a c η hc θ) :
    globalCoproduct a c η hc θ (x*y)=
      globalSignedTensorMultiply a c η hc θ
        (globalCoproduct a c η hc θ x) (globalCoproduct a c η hc θ y) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [zero_mul,map_zero,LinearMap.zero_apply]
  | add x x' hx hx' => simp only [add_mul,map_add,LinearMap.add_apply,hx,hx']
  | of k x =>
    induction y using DirectSum.induction_on with
    | zero => simp only [mul_zero,map_zero]
    | add y y' hy hy' => simp only [mul_add,map_add,hy,hy']
    | of l y => exact globalCoproduct_mul_lof a c η hc θ k.1 l.1 k.2 l.2 x y

end ElementaryPositivity.RawShuffle

end

end OAI
