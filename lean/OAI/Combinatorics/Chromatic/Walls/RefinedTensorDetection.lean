import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RefinedLaurent
import OAI.Combinatorics.Chromatic.Shuffle.CrossCancellation

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def refinedCenterPolynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim) :
    MvPolynomial (L.node R).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)) :=
  centerTranslation (quotientFamily a (SlopeArithmetic.slope c η)) (taylorB a (SlopeArithmetic.slope c η))
    (.node L R) (Algebra.TensorProduct.map (restrictionB a c η hc θ L hL)
      (restrictionB a c η hc θ R hR) x)

lemma refinedCenterPolynomial_eval (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : (L.node R).Centers → ℚ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim) :
    evalRat v (refinedCenterPolynomial a c η hc θ L R hL hR x)=
      refinedAtB a c η hc θ L R hL hR (v ∘ Sum.inl) (v ∘ Sum.inr) x := by
  have he : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr)=v := by funext z; cases z <;> rfl
  have ht:=centerTranslation_evalRat a (SlopeArithmetic.slope c η) (.node L R)
    (Algebra.TensorProduct.map (restrictionB a c η hc θ L hL) (restrictionB a c η hc θ R hR) x) v
  change _=translationAtAlgB a (SlopeArithmetic.slope c η) (.node L R) _ _
  rw [translationAtAlgB_apply,he]
  exact ht

lemma refinedCenterPolynomial_coeff_test (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (k : L.Degrees) (l : R.Degrees) (z : L.Centers →₀ ℕ) (w : R.Centers →₀ ℕ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim) :
    componentTensor a (SlopeArithmetic.slope c η) (.node L R) (k,l)
      ((refinedCenterPolynomial a c η hc θ L R hL hR x).coeff (z.sumElim w))=
      TensorProduct.map (restrictionTest a c η hc θ L hL rfl k z)
        (restrictionTest a c η hc θ R hR rfl l w) x := by
  unfold refinedCenterPolynomial
  rw [centerTranslation_node_coeff]
  induction x using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]

lemma refinedAtB_weight_zero_test (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim)
    (hx : ∀ v w,weightComponent a (SlopeArithmetic.slope c η) (.node L R) W
      (refinedAtB a c η hc θ L R hL hR v w x)=0)
    (k : L.Degrees) (l : R.Degrees) (z : L.Centers →₀ ℕ) (w : R.Centers →₀ ℕ)
    (hw : 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=W) :
    TensorProduct.map (restrictionTest a c η hc θ L hL rfl k z)
      (restrictionTest a c η hc θ R hR rfl l w) x=0 := by
  have hp : mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
      (refinedCenterPolynomial a c η hc θ L R hL hR x)=0 := by
    apply eq_of_evalRat
    intro v
    rw [evalRat_mapLinear,map_zero,refinedCenterPolynomial_eval]
    exact hx _ _
  have h:=congrArg (fun p=>componentTensor a (SlopeArithmetic.slope c η) (.node L R) (k,l)
    (AddMonoidAlgebra.coeff p (z.sumElim w))) hp
  rw [coeff_mapLinear,componentTensor_weightComponent,ite_eq_left hw,AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply,map_zero,refinedCenterPolynomial_coeff_test] at h
  exact h
end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity
open SplitTree SeparationInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma refined_negative_separation_weight_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W j : ℤ) (hj : j<0)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) :
    weightComponent a (SlopeArithmetic.slope c η) (.node L R) W
      (refinedAtB a c η hc θ L R hL hR v w
        (separationCoefficient a c η hc
          ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) j f))=0 := by
  obtain ⟨p,hp⟩:=crossKernel_leading_polynomial a c η hc θ hχ L R hL hR v w W f hf
  have h:=refined_leading_separation_formula a c η hc θ L R hL hR v w W f hf
  rw [hp] at h
  have hh:=congrArg (fun x : LaurentSeries (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R))=>x.coeff (-j)) h
  rw [mapLinear_coeff,mapRing_coeff,polynomial_coeff_positive p (-j) (by omega)] at hh
  exact hh

theorem separationCoefficient_negative_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (W j : ℤ) (hj : j<0) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    separationCoefficient a c η hc hs j f∈sourceTensorFiltration a c η hc θ d e (W+1) := by
  apply tensor_leading_restrictions_detect a c η hc θ d e W _
    (separationCoefficient_filtration a c η hc θ d e hs W j f hf)
  rintro ⟨L,hoL,hL,hd,k,z⟩ ⟨R,hoR,hR,he,l,w⟩ hw
  subst d
  subst e
  apply refinedAtB_weight_zero_test a c η hc θ L R hL hR W _
    (fun v w=>refined_negative_separation_weight_zero a c η hc θ hχ L R hL hR v w W j hj f hf)
  change (2*L.totalDegree k+L.doubleShift a)+(2*R.totalDegree l+R.doubleShift a)=W at hw
  change 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=W
  omega

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {A σ : Type*} [CommRing A] [Algebra ℚ A]
lemma lineSpecialization_coeff_zero (v h : σ → ℚ) (p : MvPolynomial σ A) :
    (lineSpecialization v h p).coeff 0=evalRat v p := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have he:=lineSpecialization_eval v h p 0
  simpa only [map_zero,mul_zero,add_zero] using he
lemma evalRat_map_algebra_eq (v : σ → ℚ) (p : MvPolynomial σ ℚ) :
    evalRat (A:=A) v (map (algebraMap ℚ A) p)=algebraMap ℚ A (evalRat v p) := by
  rw [← lineSpecialization_coeff_zero v (fun _=>0),lineSpecialization_map_algebra,
    Polynomial.coeff_map,lineSpecialization_coeff_zero]
end ElementaryPositivity.CenterCalculus

end

end OAI
