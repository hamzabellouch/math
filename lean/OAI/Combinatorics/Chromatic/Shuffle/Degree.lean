import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.DegreeIdeals
import OAI.Combinatorics.Chromatic.GradedAlgebra.IntegerHomogeneous

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma componentS_zero (d : I → ℕ) (f : S d) :
    componentS d 0 f=algebraMap ℚ (S d) (constantCoeff f.val) := by
  apply Subtype.ext
  exact constantWeight_component_zero f.val

omit [Fintype I] [DecidableEq I] in
lemma componentS_zero_mul (d : I → ℕ) (f g : S d) :
    componentS d 0 (f*g)=componentS d 0 f*componentS d 0 g := by
  rw [componentS_zero,componentS_zero,componentS_zero]
  change algebraMap ℚ (S d) (constantCoeff (f.val*g.val))=_
  rw [map_mul,map_mul]

noncomputable def degreeZeroB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    B a μ d →ₐ[ℚ] B a μ d where
  toFun := componentB a μ d 0
  map_zero' := (componentB a μ d 0).map_zero
  map_add' := (componentB a μ d 0).map_add
  map_one' := by
    change componentB a μ d 0 (quotientAlg a μ d 1)=quotientAlg a μ d 1
    change quotientAlg a μ d (componentS d 0 1)=_
    rw [componentS_zero]
    change quotientAlg a μ d (algebraMap ℚ (S d) (constantCoeff 1))=_
    simp only [map_one]
  map_mul' x y := by
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      induction y using Submodule.Quotient.induction_on with
      | H g =>
        change componentB a μ d 0 (quotientAlg a μ d f*quotientAlg a μ d g)=_
        rw [←map_mul]
        change quotientAlg a μ d (componentS d 0 (f*g))=
          quotientAlg a μ d (componentS d 0 f)*quotientAlg a μ d (componentS d 0 g)
        rw [componentS_zero_mul,map_mul]
  commutes' q := by
    change componentB a μ d 0 (quotientAlg a μ d (algebraMap ℚ (S d) q))=
      quotientAlg a μ d (algebraMap ℚ (S d) q)
    change quotientAlg a μ d (componentS d 0 (algebraMap ℚ (S d) q))=_
    rw [componentS_zero]
    change quotientAlg a μ d (algebraMap ℚ (S d) (constantCoeff (C q)))=_
    rw [constantCoeff_C]

@[simp] lemma degreeZeroB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (f : S d) :
    degreeZeroB a μ d (quotientAlg a μ d f)=algebraMap ℚ (B a μ d) (constantCoeff f.val) := by
  change quotientAlg a μ d (componentS d 0 f)=_
  rw [componentS_zero,AlgHom.commutes]

namespace SplitTree
@[reducible] def zeroDegrees : (T : SplitTree I) → T.Degrees
  | .leaf _ => 0
  | .node l r => (l.zeroDegrees,r.zeroDegrees)

omit [Fintype I] [DecidableEq I] in
lemma totalDegree_zeroDegrees (T : SplitTree I) : T.totalDegree T.zeroDegrees=0 := by
  induction T with
  | leaf d => rfl
  | node l r hl hr => simp only [totalDegree,hl,hr,add_zero]

omit [Fintype I] [DecidableEq I] in
lemma nonnegativeDegree_zeroDegrees (T : SplitTree I) : T.NonnegativeDegree T.zeroDegrees := by
  induction T with
  | leaf d => exact le_rfl
  | node l r hl hr => exact ⟨hl,hr⟩

omit [Fintype I] [DecidableEq I] in
lemma nonnegative_totalDegree_zero (T : SplitTree I) (k : T.Degrees)
    (hn : T.NonnegativeDegree k) (hk : T.totalDegree k=0) : k=T.zeroDegrees := by
  induction T with
  | leaf d => exact hk
  | node l r hl hr =>
    have hL:=l.totalDegree_nonnegative k.1 hn.1
    have hR:=r.totalDegree_nonnegative k.2 hn.2
    change l.totalDegree k.1+r.totalDegree k.2=0 at hk
    exact Prod.ext (hl k.1 hn.1 (by omega)) (hr k.2 hn.2 (by omega))

noncomputable def degreeZeroTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) : tensor (quotientFamily a μ) T →ₐ[ℚ] tensor (quotientFamily a μ) T :=
  tensorMap (quotientFamily a μ) (quotientFamily a μ) (degreeZeroB a μ) T

lemma degreeZeroTensor_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (x : tensor (quotientFamily a μ) T) :
    degreeZeroTensor a μ T x=componentTensor a μ T T.zeroDegrees x := by
  induction T with
  | leaf d => rfl
  | node l r hl hr =>
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      change degreeZeroTensor a μ l x⊗ₜ[ℚ]degreeZeroTensor a μ r y=_
      rw [hl,hr]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

lemma sub_degreeZero_mem (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (x : tensor (quotientFamily a μ) T) :
    x-degreeZeroTensor a μ T x∈degreeCutSubmodule a μ T (T.doubleShift a+1) := by
  intro k hk
  rw [degreeZeroTensor_apply,map_sub,componentTensor_componentTensor]
  by_cases hn : T.NonnegativeDegree k
  · have hnn:=T.totalDegree_nonnegative k hn
    have hz : k=T.zeroDegrees := nonnegative_totalDegree_zero T k hn (by omega)
    simp only [hz,ite_true,sub_self]
  · have hne : k≠T.zeroDegrees := by
      intro h
      apply hn
      simpa only [h] using T.nonnegativeDegree_zeroDegrees
    simp only [ite_eq_right hne,componentTensor_negative a μ T k hn,LinearMap.zero_apply,sub_zero]
end SplitTree
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
namespace SplitTree

lemma translationAtB_add (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (v w : T.Centers → ℚ) (x : tensor (quotientFamily a μ) T) :
    translationAtB a μ T v (translationAtB a μ T w x)=
      translationAtB a μ T (fun s=>v s+w s) x := by
  induction T with
  | leaf d => exact translationB_add a μ d (v ()) (w ()) x
  | node l r hl hr =>
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      change translationAtB a μ l (v ∘ Sum.inl) (translationAtB a μ l (w ∘ Sum.inl) x) ⊗ₜ[ℚ]
        translationAtB a μ r (v ∘ Sum.inr) (translationAtB a μ r (w ∘ Sum.inr) y)=_
      rw [hl,hr]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

lemma restrictionB_translationAt (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ) (t : ℚ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) :
    restrictionB a c η hc θ T hT (translationB a (SlopeArithmetic.slope c η) T.dim t f)=
      translationAtB a (SlopeArithmetic.slope c η) T (fun _=>t) (restrictionB a c η hc θ T hT f) := by
  induction T with
  | leaf d => rfl
  | node l r hl hr =>
    change (Algebra.TensorProduct.map (restrictionB a c η hc θ l hT.1)
      (restrictionB a c η hc θ r hT.2))
      (RawShuffle.restrictionB a c η hc ((slope_dim c η hc hT.1).trans (slope_dim c η hc hT.2).symm) (firstCut l.dim r.dim)
        (translationB a (SlopeArithmetic.slope c η) (l.dim+r.dim) t f))=_
    rw [RawShuffle.restrictionB_translation]
    simp only [restrictionB,AlgHom.comp_apply]
    generalize RawShuffle.restrictionB a c η hc ((slope_dim c η hc hT.1).trans (slope_dim c η hc hT.2).symm) (firstCut l.dim r.dim) f=x
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      change restrictionB a c η hc θ l hT.1 (translationB a (SlopeArithmetic.slope c η) l.dim t x) ⊗ₜ[ℚ]
        restrictionB a c η hc θ r hT.2 (translationB a (SlopeArithmetic.slope c η) r.dim t y)=_
      rw [hl,hr]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

lemma centeredRestrictionB_translate_eval (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ) (t : ℚ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) (v : T.Centers → ℚ) :
    evalRat v (centeredRestrictionB a c η hc θ T hT
      (translationB a (SlopeArithmetic.slope c η) T.dim t f))=
    evalRat (fun s=>v s+t) (centeredRestrictionB a c η hc θ T hT f) := by
  change evalRat v (centerTranslation _ _ T
    (restrictionB a c η hc θ T hT (translationB a (SlopeArithmetic.slope c η) T.dim t f)))=_
  rw [centerTranslation_evalRat,restrictionB_translationAt,translationAtB_add]
  exact (centerTranslation_evalRat _ _ _ _ _).symm
end SplitTree

lemma sourceFiltration_translation_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) (t : ℚ) :
    translationB a (SlopeArithmetic.slope c η) d t f∈sourceFiltration a c η hc θ d W := by
  intro T hT hs hd k z hw
  subst d
  let P:=SplitTree.componentTensor a (SlopeArithmetic.slope c η) T k
  have h0 : mapLinear P (SplitTree.centeredRestrictionB a c η hc θ T hs f)=0 := by
    ext s
    rw [coeff_mapLinear,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
    exact hf T hT hs rfl k s hw
  have h1 : mapLinear P (SplitTree.centeredRestrictionB a c η hc θ T hs
      (translationB a (SlopeArithmetic.slope c η) T.dim t f))=0 := by
    apply eq_of_evalRat
    intro v
    rw [map_zero,evalRat_mapLinear,SplitTree.centeredRestrictionB_translate_eval,
      ←evalRat_mapLinear,h0,map_zero]
  have he:=congrArg (fun polynomial => AddMonoidAlgebra.coeff polynomial z) h1
  change P ((SplitTree.centeredRestrictionB a c η hc θ T hs
    (translationB a (SlopeArithmetic.slope c η) T.dim t f)).coeff z)=0
  simpa only [coeff_mapLinear,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using he

end ElementaryPositivity.RawShuffle

end

end OAI
