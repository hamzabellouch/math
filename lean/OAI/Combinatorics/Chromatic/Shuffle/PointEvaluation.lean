import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Degree

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma constantCoeff_translation {α : Type*} (t : ℚ) (f : MvPolynomial α ℚ) :
    constantCoeff (translation t f)=eval (fun _=>t) f := by
  induction f using MvPolynomial.induction_on with
  | C q => simp only [translation_C,constantCoeff_C,eval_C]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => simp only [map_mul,translation_X,map_add,constantCoeff_X,
      constantCoeff_C,zero_add,hf,eval_X]

noncomputable def translationAlgB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (t : ℚ) : B a μ d →ₐ[ℚ] B a μ d :=
  (Polynomial.eval₂AlgHom (AlgHom.id ℚ (B a μ d)) (algebraMap ℚ (B a μ d) t)
    (fun _=>Commute.all _ _)).comp
    (taylorB a μ d)

lemma translationAlgB_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (t : ℚ) (f : B a μ d) :
    translationAlgB a μ d t f=translationB a μ d t f := by
  change Polynomial.eval₂ (RingHom.id _) (algebraMap ℚ (B a μ d) t) (taylorB a μ d f)=_
  rw [Polynomial.eval₂_id,taylorB_eval]

namespace SplitTree
@[reducible] def centerOfVar : (T : SplitTree I) → T.Vars → T.Centers
  | .leaf _, _ => ()
  | .node l _, .inl x => .inl (l.centerOfVar x)
  | .node _ r, .inr x => .inr (r.centerOfVar x)

noncomputable def translationAtAlgB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) :
    (T : SplitTree I) → (T.Centers → ℚ) →
      tensor (quotientFamily a μ) T →ₐ[ℚ] tensor (quotientFamily a μ) T
  | .leaf d, v => translationAlgB a μ d (v ())
  | .node l r, v => Algebra.TensorProduct.map
      (translationAtAlgB a μ l (v ∘ Sum.inl)) (translationAtAlgB a μ r (v ∘ Sum.inr))

lemma translationAtAlgB_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (v : T.Centers → ℚ) (x : tensor (quotientFamily a μ) T) :
    translationAtAlgB a μ T v x=translationAtB a μ T v x := by
  induction T with
  | leaf d => exact translationAlgB_apply a μ d (v ()) x
  | node l r hl hr =>
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      change translationAtAlgB a μ l (v ∘ Sum.inl) x⊗ₜ[ℚ]
        translationAtAlgB a μ r (v ∘ Sum.inr) y=_
      rw [hl,hr]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

lemma degreeZero_translate_quotient (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (v : T.Centers → ℚ) (x : tensor rawFamily T) :
    degreeZeroTensor a μ T (translationAtAlgB a μ T v (quotientMap a μ T x))=
      algebraMap ℚ (tensor (quotientFamily a μ) T)
        (eval (v ∘ T.centerOfVar) (tensorValue T x)) := by
  induction T with
  | leaf d =>
    change degreeZeroB a μ d (translationAlgB a μ d (v ()) (quotientAlg a μ d x))=_
    rw [translationAlgB_apply]
    change degreeZeroB a μ d (quotientAlg a μ d (translationS d (v ()) x))=_
    rw [degreeZeroB_mk]
    congr 1
    exact constantCoeff_translation (v ()) x.val
  | node l r hl hr =>
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      change degreeZeroTensor a μ l (translationAtAlgB a μ l (v ∘ Sum.inl) (quotientMap a μ l x))⊗ₜ[ℚ]
        degreeZeroTensor a μ r (translationAtAlgB a μ r (v ∘ Sum.inr) (quotientMap a μ r y))=_
      rw [hl,hr,tensorValue_tmul,map_mul,eval_rename,eval_rename]
      simp only [Function.comp_def,centerOfVar]
      simp only [Algebra.algebraMap_eq_smul_one,TensorProduct.smul_tmul,
        TensorProduct.tmul_smul,smul_smul,Algebra.TensorProduct.one_def,mul_comm]
    | add x y hx hy => simp only [map_add,hx,hy]

noncomputable def pointedRestrictionB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ) (v : T.Centers → ℚ) :
    B a (SlopeArithmetic.slope c η) T.dim →ₐ[ℚ] tensor (quotientFamily a (SlopeArithmetic.slope c η)) T :=
  (degreeZeroTensor a (SlopeArithmetic.slope c η) T).comp
    ((translationAtAlgB a (SlopeArithmetic.slope c η) T v).comp
      (restrictionB a c η hc θ T hT))

lemma pointedRestrictionB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ) (v : T.Centers → ℚ) (f : S T.dim) :
    pointedRestrictionB a c η hc θ T hT v (quotientAlg a (SlopeArithmetic.slope c η) T.dim f)=
      algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T)
        (eval (v ∘ T.centerOfVar ∘ T.varEquiv.symm) f.val) := by
  simp only [pointedRestrictionB,AlgHom.comp_apply,restrictionB_mk,
    degreeZero_translate_quotient,tensorValue_rawRestriction,eval_rename]
  rfl
end SplitTree
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

instance centersFintype : (T : SplitTree I) → Fintype T.Centers
  | .leaf _ => inferInstanceAs (Fintype Unit)
  | .node l r => by
    letI := centersFintype l
    letI := centersFintype r
    exact inferInstanceAs (Fintype (l.Centers ⊕ r.Centers))

instance centersLinearOrder : (T : SplitTree I) → LinearOrder T.Centers
  | .leaf _ => inferInstanceAs (LinearOrder Unit)
  | .node l r => by
    letI := centersLinearOrder l
    letI := centersLinearOrder r
    exact Sum.Lex.linearOrder

def centerPairs (T : SplitTree I) : Finset (T.Centers × T.Centers) :=
  Finset.univ.filter (fun ij=>ij.1 < ij.2)

omit [Fintype I] [DecidableEq I] in
lemma centerPairs_ne (T : SplitTree I) (ij : T.Centers×T.Centers) (h : ij∈T.centerPairs) :
    ij.1≠ij.2 := (Finset.mem_filter.mp h).2.ne

omit [Fintype I] [DecidableEq I] in
lemma centerPairs_norev (T : SplitTree I) (ij : T.Centers×T.Centers) (h : ij∈T.centerPairs) :
    (ij.2,ij.1)∉T.centerPairs := by
  intro hr
  exact lt_asymm (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp hr).2

noncomputable def centerNumerator (a : I → I → ℕ) (T : SplitTree I)
    (s : Finset (T.Centers×T.Centers)) : MvPolynomial T.Centers ℚ :=
  ∏ ij∈s,diagonal ij.1 ij.2 ^ (eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2)).toNat

omit [DecidableEq I] in
lemma centerDenominator_ne_zero (a : I → I → ℕ) (T : SplitTree I) :
    centerDenominator a T T.centerPairs≠0 := by
  exact Finset.prod_ne_zero_iff.mpr fun ij hij=>
    pow_ne_zero _ (diagonal_ne_zero (T.centerPairs_ne ij hij))

omit [DecidableEq I] in
lemma centerNumerator_ne_zero (a : I → I → ℕ) (T : SplitTree I) :
    centerNumerator a T T.centerPairs≠0 := by
  exact Finset.prod_ne_zero_iff.mpr fun ij hij=>
    pow_ne_zero _ (diagonal_ne_zero (T.centerPairs_ne ij hij))

def PairSymmetric (a : I → I → ℕ) (T : SplitTree I) : Prop :=
  ∀ ij∈T.centerPairs,eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2) =
    eulerForm a (T.leafDimension ij.2) (T.leafDimension ij.1)

noncomputable def clearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W : ℤ)
    (f : sourceFiltration a c η hc θ T.dim W) :
    MvPolynomial T.Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) :=
  Classical.choose (totalLeadingPolynomial_denominator_divisible a c η hc θ T hT W f.val f.property
    T.centerPairs T.centerPairs_ne T.centerPairs_norev hχ)

lemma denominator_clearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W : ℤ) (f : sourceFiltration a c η hc θ T.dim W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T))
      (centerDenominator a T T.centerPairs) * clearedLeading a c η hc θ T hT hχ W f =
      totalLeadingPolynomial a c η hc θ T hT W f.val :=
  (Classical.choose_spec (totalLeadingPolynomial_denominator_divisible a c η hc θ T hT W f.val f.property
    T.centerPairs T.centerPairs_ne T.centerPairs_norev hχ)).symm

noncomputable def clearedLeadingMap (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W : ℤ) :
    sourceFiltration a c η hc θ T.dim W →ₗ[ℚ]
      MvPolynomial T.Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) where
  toFun := clearedLeading a c η hc θ T hT hχ W
  map_add' f g := by
    apply scalar_mul_injective _ (centerDenominator_ne_zero a T)
    dsimp only
    rw [mul_add,denominator_clearedLeading,denominator_clearedLeading,denominator_clearedLeading]
    simp only [totalLeadingPolynomial,Submodule.coe_add,map_add]
  map_smul' r f := by
    apply scalar_mul_injective _ (centerDenominator_ne_zero a T)
    dsimp only
    rw [mul_smul_comm,denominator_clearedLeading,denominator_clearedLeading]
    simp only [totalLeadingPolynomial,Submodule.coe_smul,map_smul,RingHom.id_apply]

noncomputable def normalizedSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W : ℤ) :
    sourceFiltration a c η hc θ T.dim W →ₗ[ℚ]
      MvPolynomial T.Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) :=
  (LinearMap.mulLeft ℚ (map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T))
    (centerNumerator a T T.centerPairs))).comp (clearedLeadingMap a c η hc θ T hT hχ W)

lemma normalizedSymbol_eq_zero_iff (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W : ℤ) (f : sourceFiltration a c η hc θ T.dim W) :
    normalizedSymbol a c η hc θ T hT hχ W f=0 ↔
      totalLeadingPolynomial a c η hc θ T hT W f.val=0 := by
  change map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T))
      (centerNumerator a T T.centerPairs) * clearedLeading a c η hc θ T hT hχ W f=0 ↔ _
  rw [SymbolCoordinates.scalar_mul_eq_zero_iff _ (centerNumerator_ne_zero a T)]
  rw [← denominator_clearedLeading a c η hc θ T hT hχ W f,
    SymbolCoordinates.scalar_mul_eq_zero_iff _ (centerDenominator_ne_zero a T)]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
