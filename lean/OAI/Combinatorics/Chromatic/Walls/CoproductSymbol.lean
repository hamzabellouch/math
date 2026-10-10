import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RefinedTensorDetection

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma centerNumerator_crossPairs_line (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0))
      (centerNumerator a (L.node R) (crossPairs L R))=
      crossPolynomial a L R v w Int.toNat := by
  classical
  unfold centerNumerator crossPairs
  rw [Finset.prod_image (fun p _ q _ h=>crossPairs_injective L R h)]
  simp only [map_prod,map_pow]
  rw [Fintype.prod_prod_type]
  unfold crossPolynomial
  apply Finset.prod_congr rfl
  intro z hz
  apply Finset.prod_congr rfl
  intro t ht
  congr 1
  simp only [diagonal,map_sub,lineSpecialization_X,Sum.elim_inl,Sum.elim_inr,
    _root_.map_zero,_root_.map_one,zero_mul,one_mul,add_zero,Algebra.algebraMap_self_apply,
    affinePolynomial]
  ring

lemma refined_leading_zero_factor (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W)
    (q : MvPolynomial (L.node R).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
    (hq : totalLeadingPolynomial a c η hc θ (.node L R) ⟨hL,hR⟩ W f=
      map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (centerDenominator a (L.node R) (crossPairs L R))*q) :
    CenterCalculus.mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
      (refinedCenterPolynomial a c η hc θ L R hL hR
        (separationCoefficient a c η hc
          ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) 0 f))=
      map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (centerNumerator a (L.node R) (crossPairs L R))*q := by
  apply eq_of_evalRat
  intro v
  have hv : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr)=v := by
    funext z
    cases z <;> rfl
  have h:=refined_leading_separation_formula a c η hc θ L R hL hR
    (v ∘ Sum.inl) (v ∘ Sum.inr) W f hf
  rw [hq,map_mul,lineSpecialization_map_algebra,centerDenominator_crossPairs_line,
    map_mul,←polynomial_map,←mul_assoc,←map_mul,scalarCrossKernel_denominator,
    polynomial_map] at h
  have hh:=congrArg (fun x : LaurentSeries (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R))=>x.coeff (-(0:ℤ))) h
  rw [LaurentAtInfinity.mapLinear_coeff,mapRing_coeff,←map_mul] at hh
  simp only [neg_zero] at hh
  rw [show ∀ p : Polynomial (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)),
    (polynomial p).coeff 0=p.coeff 0 from fun p=>by simpa using polynomial_coeff p 0,
    Polynomial.mul_coeff_zero,Polynomial.coeff_map,
    ←centerNumerator_crossPairs_line,lineSpecialization_coeff_zero,
    lineSpecialization_coeff_zero,hv] at hh
  rw [evalRat_mapLinear,refinedCenterPolynomial_eval,map_mul,evalRat_map_algebra_eq]
  exact hh

theorem coproductSymbol_cross_cleared (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (centerDenominator a (L.node R) (crossPairs L R))*
      CenterCalculus.mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
        (refinedCenterPolynomial a c η hc θ L R hL hR
          (separationCoefficient a c η hc
            ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) 0 f))=
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (centerNumerator a (L.node R) (crossPairs L R))*
      totalLeadingPolynomial a c η hc θ (.node L R) ⟨hL,hR⟩ W f := by
  obtain ⟨q,hq⟩:=totalLeadingPolynomial_denominator_divisible a c η hc θ (.node L R) ⟨hL,hR⟩
    W f hf (crossPairs L R) (crossPairs_ne L R) (crossPairs_norev L R)
      (crossPairs_symmetric a c η θ hχ L R hL hR)
  rw [refined_leading_zero_factor a c η hc θ L R hL hR W f hf q hq,hq]
  ring

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
