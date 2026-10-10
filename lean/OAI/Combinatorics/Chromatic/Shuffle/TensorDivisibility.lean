import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TensorPolynomialBox
import OAI.Combinatorics.Chromatic.Walls.RefinedTensorDetection

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma refinedCenterPolynomial_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (x : B a (SlopeArithmetic.slope c η) L.dim)
    (y : B a (SlopeArithmetic.slope c η) R.dim) :
    refinedCenterPolynomial a c η hc θ L R hL hR (x⊗ₜ[ℚ]y)=
      box (centeredRestrictionB a c η hc θ L hL x)
        (centeredRestrictionB a c η hc θ R hR y) := by
  unfold refinedCenterPolynomial
  rw [Algebra.TensorProduct.map_tmul]
  erw [centerTranslation_tmul]
  rfl

lemma mapLinear_weight_box (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (L R : SplitTree I) (U V : ℤ)
    (p : MvPolynomial L.Centers (tensor (quotientFamily a μ) L))
    (q : MvPolynomial R.Centers (tensor (quotientFamily a μ) R))
    (hp : ∀ z,p.coeff z∈degreeCutSubmodule a μ L U)
    (hq : ∀ z,q.coeff z∈degreeCutSubmodule a μ R V) :
    mapLinear (weightComponent a μ (.node L R) (U+V)) (box p q)=
      box (mapLinear (weightComponent a μ L U) p) (mapLinear (weightComponent a μ R V) q) := by
  ext z
  rw [←Finsupp.comapDomain_sumElim_comapDomain z]
  simp only [coeff_mapLinear,coeff_box]
  exact weightComponent_node_tmul a μ L R U V _ _ (hp _) (hq _)

lemma refinedLeadingPolynomial_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (U V : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim)
    (y : B a (SlopeArithmetic.slope c η) R.dim)
    (hx : x∈sourceFiltration a c η hc θ L.dim U)
    (hy : y∈sourceFiltration a c η hc θ R.dim V) :
    mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) (U+V))
      (refinedCenterPolynomial a c η hc θ L R hL hR (x⊗ₜ[ℚ]y))=
      box (totalLeadingPolynomial a c η hc θ L hL U x)
        (totalLeadingPolynomial a c η hc θ R hR V y) := by
  rw [refinedCenterPolynomial_tmul]
  exact mapLinear_weight_box a _ L R U V _ _
    (centeredRestrictionB_coeff_degreeCut a c η hc θ L hL U x hx)
    (centeredRestrictionB_coeff_degreeCut a c η hc θ R hR V y hy)

noncomputable def internalDenominator (a : I → I → ℕ) (L R : SplitTree I) :
    MvPolynomial (L.node R).Centers ℚ :=
  rename Sum.inl (centerDenominator a L L.centerPairs)*
  rename Sum.inr (centerDenominator a R R.centerPairs)

noncomputable def internalNumerator (a : I → I → ℕ) (L R : SplitTree I) :
    MvPolynomial (L.node R).Centers ℚ :=
  rename Sum.inl (centerNumerator a L L.centerPairs)*
  rename Sum.inr (centerNumerator a R R.centerPairs)

lemma refinedLeadingPolynomial_denominator_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim)
    (hx : x∈sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (internalDenominator a L R) ∣
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
        (refinedCenterPolynomial a c η hc θ L R hL hR x) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨U,V,x,y,hw,hx,hy,rfl⟩:=hz
    have hy' := sourceFiltration_antitone a c η hc θ R.dim (show W-U≤V by omega) hy
    have he : W=U+(W-U) := by omega
    rw [he,refinedLeadingPolynomial_tmul a c η hc θ L R hL hR U (W-U) x y hx hy']
    obtain ⟨p,hp⟩:=totalLeadingPolynomial_denominator_divisible a c η hc θ L hL U x hx
      L.centerPairs L.centerPairs_ne L.centerPairs_norev hχL
    obtain ⟨q,hq⟩:=totalLeadingPolynomial_denominator_divisible a c η hc θ R hR (W-U) y hy'
      R.centerPairs R.centerPairs_ne R.centerPairs_norev hχR
    refine ⟨box p q,?_⟩
    rw [hp,hq,box_scalar_left]
    rfl
  | zero =>
    simp only [refinedCenterPolynomial,map_zero]
    exact dvd_zero _
  | add x y hx hy ihx ihy =>
    simp only [refinedCenterPolynomial,map_add] at ihx ihy ⊢
    exact dvd_add ihx ihy
  | smul r x hx ih =>
    obtain ⟨q,hq⟩:=ih
    refine ⟨r • q,?_⟩
    simp only [refinedCenterPolynomial,map_smul] at hq ⊢
    rw [hq,mul_smul_comm]
end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma centerPairs_prod_node {A : Type*} [CommMonoid A] (L R : SplitTree I)
    (f : (L.node R).Centers × (L.node R).Centers → A) :
    (∏ ij∈(L.node R).centerPairs,f ij)=
      (∏ ij∈L.centerPairs,f (Sum.inl ij.1,Sum.inl ij.2))*
      (∏ ij∈R.centerPairs,f (Sum.inr ij.1,Sum.inr ij.2))*
      (∏ ij∈crossPairs L R,f ij) := by
  classical
  have hLL (x y : L.Centers) :
      @LT.lt (L.node R).Centers (centersLinearOrder (L.node R)).toLT
        (Sum.inl x) (Sum.inl y) ↔ x<y := Sum.lex_inl_inl
  have hRR (x y : R.Centers) :
      @LT.lt (L.node R).Centers (centersLinearOrder (L.node R)).toLT
        (Sum.inr x) (Sum.inr y) ↔ x<y := Sum.lex_inr_inr
  have hLR (x : L.Centers) (y : R.Centers) :
      @LT.lt (L.node R).Centers (centersLinearOrder (L.node R)).toLT
        (Sum.inl x) (Sum.inr y) := Sum.Lex.sep _ _
  have hRL (x : R.Centers) (y : L.Centers) :
      ¬ @LT.lt (L.node R).Centers (centersLinearOrder (L.node R)).toLT
        (Sum.inr x) (Sum.inl y) := Sum.lex_inr_inl
  simp only [centerPairs,Finset.prod_filter,Fintype.prod_prod_type,
    Fintype.prod_sum_type]
  simp only [crossPairs,Finset.prod_image (fun p _ q _ h=>crossPairs_injective L R h),
    Fintype.prod_prod_type]
  simp only [hLL,hRR,hLR,hRL,ite_true,ite_false,Finset.prod_const_one,one_mul,
    Finset.prod_mul_distrib]
  ac_rfl

omit [DecidableEq I] in
lemma centerNumerator_node (a : I → I → ℕ) (L R : SplitTree I) :
    centerNumerator a (.node L R) (L.node R).centerPairs =
      rename Sum.inl (centerNumerator a L L.centerPairs)*
      rename Sum.inr (centerNumerator a R R.centerPairs)*
      centerNumerator a (.node L R) (crossPairs L R) := by
  unfold centerNumerator
  rw [centerPairs_prod_node]
  simp only [map_prod,map_pow,diagonal,map_sub,rename_X,leafDimension]

omit [DecidableEq I] in
lemma centerDenominator_node (a : I → I → ℕ) (L R : SplitTree I) :
    centerDenominator a (.node L R) (L.node R).centerPairs =
      rename Sum.inl (centerDenominator a L L.centerPairs)*
      rename Sum.inr (centerDenominator a R R.centerPairs)*
      centerDenominator a (.node L R) (crossPairs L R) := by
  unfold centerDenominator
  rw [centerPairs_prod_node]
  simp only [map_prod,map_pow,diagonal,map_sub,rename_X,leafDimension]
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
