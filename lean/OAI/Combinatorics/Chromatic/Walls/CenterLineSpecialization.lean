import Mathlib
import OAI.Combinatorics.Chromatic.Histories.KernelEvaluation

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {A B σ : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

noncomputable def lineSpecialization (v h : σ → ℚ) : MvPolynomial σ A →+* Polynomial A :=
  eval₂Hom Polynomial.C (fun i=>Polynomial.C (algebraMap ℚ A (v i))+
    Polynomial.C (algebraMap ℚ A (h i))*Polynomial.X)

@[simp] lemma lineSpecialization_C (v h : σ → ℚ) (a : A) :
    lineSpecialization v h (C a)=Polynomial.C a := by
  simp only [lineSpecialization,eval₂Hom_C]
@[simp] lemma lineSpecialization_X (v h : σ → ℚ) (i : σ) :
    lineSpecialization (A:=A) v h (X i)=Polynomial.C (algebraMap ℚ A (v i))+
      Polynomial.C (algebraMap ℚ A (h i))*Polynomial.X := by
  simp only [lineSpecialization,coe_eval₂Hom,eval₂_X]

lemma lineSpecialization_eval (v h : σ → ℚ) (p : MvPolynomial σ A) (t : ℚ) :
    (lineSpecialization v h p).eval (algebraMap ℚ A t)=
      evalRat (fun i=>v i+h i*t) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [lineSpecialization_C,Polynomial.eval_C,evalRat_C]
  | add p q hp hq => simp only [map_add,Polynomial.eval_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,Polynomial.eval_mul,hp,lineSpecialization_X,evalRat_X,
      Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,map_add,map_mul]

lemma lineSpecialization_mapLinear (v h : σ → ℚ) (l : A →ₗ[ℚ] B)
    (p : MvPolynomial σ A) :
    lineSpecialization v h (mapLinear l p)=
      RawShuffle.polynomialMapLinear l (lineSpecialization v h p) := by
  apply RawShuffle.polynomial_eq_of_rat_evals
  intro t
  rw [lineSpecialization_eval,RawShuffle.polynomialMapLinear_eval_rat,
    lineSpecialization_eval,evalRat_mapLinear]
end ElementaryPositivity.CenterCalculus

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def refinedAtB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim →ₐ[ℚ]
      tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R) :=
  (translationAtAlgB a (SlopeArithmetic.slope c η) (.node L R) (Sum.elim v w)).comp
    (Algebra.TensorProduct.map (restrictionB a c η hc θ L hL) (restrictionB a c η hc θ R hR))

lemma degreeZero_refinedAtB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim) :
    degreeZeroTensor a (SlopeArithmetic.slope c η) (.node L R)
      (refinedAtB a c η hc θ L R hL hR v w x)=
      pointedTensorRestriction a c η hc θ L R hL hR v w x := by
  induction x using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]

lemma refinedAtB_relative_eval (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (t : ℚ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim)) :
    refinedAtB a c η hc θ L R hL hR v w
      ((restrictionRelativeB a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm)
        (firstCut L.dim R.dim) f).eval (algebraMap ℚ _ t))=
    evalRat (Sum.elim (fun z=>v z+t) w)
      (centeredRestrictionB a c η hc θ (.node L R) ⟨hL,hR⟩ f) := by
  change refinedAtB a c η hc θ L R hL hR v w
    ((relativeTaylorB a (SlopeArithmetic.slope c η) L.dim R.dim
      (RawShuffle.restrictionB a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) (firstCut L.dim R.dim) f)).eval _) = _
  rw [relativeTaylorB_eval]
  trans translationAtB a (SlopeArithmetic.slope c η) (.node L R)
    (Sum.elim (fun z=>v z+t) w) (restrictionB a c η hc θ (.node L R) ⟨hL,hR⟩ f)
  · simp only [restrictionB,AlgHom.comp_apply]
    generalize RawShuffle.restrictionB a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm)
      (firstCut L.dim R.dim) f=x
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      change translationAtAlgB a (SlopeArithmetic.slope c η) L v
        (restrictionB a c η hc θ L hL (translationB a (SlopeArithmetic.slope c η) L.dim t x)) ⊗ₜ[ℚ]
        translationAtAlgB a (SlopeArithmetic.slope c η) R w (restrictionB a c η hc θ R hR y)=_
      rw [translationAtAlgB_apply,translationAtAlgB_apply,restrictionB_translationAt,translationAtB_add]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  · exact (centerTranslation_evalRat a (SlopeArithmetic.slope c η) (.node L R)
      (restrictionB a c η hc θ (.node L R) ⟨hL,hR⟩ f) _).symm

lemma refinedAtB_relative_polynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim)) :
    (restrictionRelativeB a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm)
      (firstCut L.dim R.dim) f).map (refinedAtB a c η hc θ L R hL hR v w).toRingHom=
    lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0))
      (centeredRestrictionB a c η hc θ (.node L R) ⟨hL,hR⟩ f) := by
  apply polynomial_eq_of_rat_evals
  intro t
  rw [eval_map_rat,lineSpecialization_eval,refinedAtB_relative_eval]
  have he : Sum.elim (fun z=>v z+t) w =
      (fun i=>Sum.elim v w i+Sum.elim (fun _=>1) (fun _=>0) i*t) := by
    funext z
    cases z <;> simp
  rw [he]

lemma centeredRestrictionB_eval_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim W) (v : T.Centers → ℚ) :
    evalRat v (centeredRestrictionB a c η hc θ T hT f)∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) T W := by
  intro k hk
  have hz : mapLinear (componentTensor a (SlopeArithmetic.slope c η) T k)
      (centeredRestrictionB a c η hc θ T hT f)=0 := by
    ext m
    rw [coeff_mapLinear,AddMonoidAlgebra.coeff_zero]
    exact sourceFiltration_allTrees a c η hc θ W f hf T hT rfl k m hk
  rw [←evalRat_mapLinear,hz,map_zero]

lemma refinedAtB_relative_coeff_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) (n : ℕ) :
    ((restrictionRelativeB a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm)
      (firstCut L.dim R.dim) f).map (refinedAtB a c η hc θ L R hL hR v w).toRingHom).coeff n∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W := by
  apply ElementaryPositivity.CommonTranslation.polynomial_coeff_mem
  intro t
  rw [eval_map_rat,refinedAtB_relative_eval]
  exact centeredRestrictionB_eval_degreeCut a c η hc θ (.node L R) ⟨hL,hR⟩ W f hf _
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
