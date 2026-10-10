import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.NormalizedTensorSymbol
import OAI.Combinatorics.Chromatic.Shuffle.TripleFiltration

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma refinedCenterPolynomial_coeff_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) R.dim)
    (hx : x∈sourceTensorFiltration a c η hc θ L.dim R.dim W) (z : (L.node R).Centers →₀ ℕ) :
    (refinedCenterPolynomial a c η hc θ L R hL hR x).coeff z∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨U,V,x,y,hUV,hx,hy,rfl⟩:=hx
    rw [refinedCenterPolynomial_tmul,←Finsupp.comapDomain_sumElim_comapDomain z,coeff_box]
    rintro ⟨k,l⟩ hkl
    change componentTensor a (SlopeArithmetic.slope c η) L k _⊗ₜ[ℚ]
      componentTensor a (SlopeArithmetic.slope c η) R l _=0
    change 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)<W at hkl
    by_cases hk : 2*L.totalDegree k+L.doubleShift a<U
    · rw [centeredRestrictionB_coeff_degreeCut a c η hc θ L hL U x hx _ k hk,
        TensorProduct.zero_tmul]
    · rw [centeredRestrictionB_coeff_degreeCut a c η hc θ R hR V y hy _ l (by omega),
        TensorProduct.tmul_zero]
  | zero =>
    simp only [refinedCenterPolynomial,map_zero,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
    exact (degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W).zero_mem
  | add x y hx hy ihx ihy =>
    simp only [refinedCenterPolynomial,map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply] at ihx ihy ⊢
    exact (degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W).add_mem ihx ihy
  | smul r x hx ih =>
    simp only [refinedCenterPolynomial,map_smul,coeff_smul] at ih ⊢
    exact (degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W).smul_mem r ih

noncomputable def refinedTripleCenterPolynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ) :
    ((B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) M.dim)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) N.dim) →ₗ[ℚ]
    MvPolynomial ((L.node M).node N).Centers
      (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)) :=
  ((centerTranslation (quotientFamily a (SlopeArithmetic.slope c η)) (taylorB a (SlopeArithmetic.slope c η))
    ((L.node M).node N)).comp
    (Algebra.TensorProduct.map (Algebra.TensorProduct.map (restrictionB a c η hc θ L hL)
      (restrictionB a c η hc θ M hM)) (restrictionB a c η hc θ N hN))).toLinearMap

lemma refinedTripleCenterPolynomial_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (x : B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) M.dim)
    (y : B a (SlopeArithmetic.slope c η) N.dim) :
    refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN (x⊗ₜ[ℚ]y)=
      box (refinedCenterPolynomial a c η hc θ L M hL hM x)
        (centeredRestrictionB a c η hc θ N hN y) := by
  unfold refinedTripleCenterPolynomial
  rw [AlgHom.toLinearMap_apply,AlgHom.comp_apply,Algebra.TensorProduct.map_tmul]
  erw [centerTranslation_tmul]
  rfl

lemma refinedTripleCenterPolynomial_coeff_test (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (k : L.Degrees) (l : M.Degrees) (m : N.Degrees)
    (z : L.Centers →₀ ℕ) (w : M.Centers →₀ ℕ) (t : N.Centers →₀ ℕ)
    (x : (B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) M.dim)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) N.dim) :
    componentTensor a (SlopeArithmetic.slope c η) ((L.node M).node N) ((k,l),m)
      ((refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN x).coeff ((z.sumElim w).sumElim t))=
      TensorProduct.map (TensorProduct.map (restrictionTest a c η hc θ L hL rfl k z)
        (restrictionTest a c η hc θ M hM rfl l w)) (restrictionTest a c η hc θ N hN rfl m t) x := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    rw [refinedTripleCenterPolynomial_tmul,coeff_box,TensorProduct.map_tmul]
    change componentTensor a (SlopeArithmetic.slope c η) (.node L M) (k,l) _⊗ₜ[ℚ]
      componentTensor a (SlopeArithmetic.slope c η) N m _=_
    rw [refinedCenterPolynomial_coeff_test]
    rfl
  | add x y hx hy =>
    rw [(refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN).map_add,
      AddMonoidAlgebra.coeff_add,Finsupp.add_apply]
    simp only [LinearMap.map_add,hx,hy]

noncomputable def tripleInternalDenominator (a : I → I → ℕ) (L M N : SplitTree I) :
    MvPolynomial ((L.node M).node N).Centers ℚ :=
  rename Sum.inl (internalDenominator a L M)*rename Sum.inr (centerDenominator a N N.centerPairs)

noncomputable def tripleInternalNumerator (a : I → I → ℕ) (L M N : SplitTree I) :
    MvPolynomial ((L.node M).node N).Centers ℚ :=
  rename Sum.inl (internalNumerator a L M)*rename Sum.inr (centerNumerator a N N.centerPairs)

omit [DecidableEq I] in
lemma tripleInternalDenominator_ne_zero (a : I → I → ℕ) (L M N : SplitTree I) :
    tripleInternalDenominator a L M N≠0 := by
  apply mul_ne_zero
  · exact fun h=>internalDenominator_ne_zero a L M ((rename_eq_zero_iff_of_injective _ Sum.inl_injective).mp h)
  · exact fun h=>centerDenominator_ne_zero a N ((rename_eq_zero_iff_of_injective _ Sum.inr_injective).mp h)

omit [DecidableEq I] in
lemma tripleInternalNumerator_ne_zero (a : I → I → ℕ) (L M N : SplitTree I) :
    tripleInternalNumerator a L M N≠0 := by
  apply mul_ne_zero
  · exact fun h=>internalNumerator_ne_zero a L M ((rename_eq_zero_iff_of_injective _ Sum.inl_injective).mp h)
  · exact fun h=>centerNumerator_ne_zero a N ((rename_eq_zero_iff_of_injective _ Sum.inr_injective).mp h)

lemma refinedTripleLeadingPolynomial_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ) (U V : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) M.dim)
    (y : B a (SlopeArithmetic.slope c η) N.dim)
    (hx : x∈sourceTensorFiltration a c η hc θ L.dim M.dim U)
    (hy : y∈sourceFiltration a c η hc θ N.dim V) :
    mapLinear (weightComponent a (SlopeArithmetic.slope c η) ((L.node M).node N) (U+V))
      (refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN (x⊗ₜ[ℚ]y))=
      box (mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L M) U)
        (refinedCenterPolynomial a c η hc θ L M hL hM x))
        (totalLeadingPolynomial a c η hc θ N hN V y) := by
  rw [refinedTripleCenterPolynomial_tmul]
  exact mapLinear_weight_box a _ (.node L M) N U V _ _
    (refinedCenterPolynomial_coeff_degreeCut a c η hc θ L M hL hM U x hx)
    (centeredRestrictionB_coeff_degreeCut a c η hc θ N hN V y hy)

lemma refinedTripleLeadingPolynomial_denominator_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ)
    (x : (B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) M.dim)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) N.dim)
    (hx : x∈sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)))
      (tripleInternalDenominator a L M N) ∣
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) ((L.node M).node N) W)
        (refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN x) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨U,V,x,y,hw,hx,hy,rfl⟩:=hz
    have hy' := sourceFiltration_antitone a c η hc θ N.dim (show W-U≤V by omega) hy
    have he : W=U+(W-U) := by omega
    rw [he,refinedTripleLeadingPolynomial_tmul a c η hc θ L M N hL hM hN U (W-U) x y hx hy']
    obtain ⟨p,hp⟩:=refinedLeadingPolynomial_denominator_divisible a c η hc θ L M hL hM hχL hχM U x hx
    obtain ⟨q,hq⟩:=totalLeadingPolynomial_denominator_divisible a c η hc θ N hN (W-U) y hy'
      N.centerPairs N.centerPairs_ne N.centerPairs_norev hχN
    refine ⟨box p q,?_⟩
    rw [hp,hq,box_scalar_left]
    rfl
  | zero =>
    rw [(refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN).map_zero,LinearMap.map_zero]
    exact dvd_zero _
  | add x y hx hy ihx ihy =>
    rw [(refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN).map_add,LinearMap.map_add]
    exact dvd_add ihx ihy
  | smul r x hx ih =>
    obtain ⟨q,hq⟩:=ih
    refine ⟨r • q,?_⟩
    rw [(refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN).map_smul r x,
      LinearMap.map_smul,hq,mul_smul_comm]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
