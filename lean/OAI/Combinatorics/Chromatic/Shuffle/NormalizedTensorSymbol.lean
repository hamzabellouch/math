import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CoproductSymbol
import OAI.Combinatorics.Chromatic.Shuffle.TensorDivisibility

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open SeparationInfinity
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma internalDenominator_ne_zero (a : I → I → ℕ) (L R : SplitTree I) :
    internalDenominator a L R≠0 := by
  apply mul_ne_zero
  · exact fun h=>centerDenominator_ne_zero a L ((rename_eq_zero_iff_of_injective _ Sum.inl_injective).mp h)
  · exact fun h=>centerDenominator_ne_zero a R ((rename_eq_zero_iff_of_injective _ Sum.inr_injective).mp h)

noncomputable def tensorClearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (f : sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    MvPolynomial (L.node R).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)) :=
  Classical.choose (refinedLeadingPolynomial_denominator_divisible a c η hc θ L R hL hR hχL hχR W f.val f.property)

lemma denominator_tensorClearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (f : sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (internalDenominator a L R)*tensorClearedLeading a c η hc θ L R hL hR hχL hχR W f=
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
        (refinedCenterPolynomial a c η hc θ L R hL hR f.val) :=
  (Classical.choose_spec (refinedLeadingPolynomial_denominator_divisible a c η hc θ L R hL hR hχL hχR W f.val f.property)).symm

noncomputable def tensorClearedLeadingMap (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ) :
    sourceTensorFiltration a c η hc θ L.dim R.dim W →ₗ[ℚ]
      MvPolynomial (L.node R).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)) :=
  { toFun := tensorClearedLeading a c η hc θ L R hL hR hχL hχR W
    map_add' := by
      intro f g
      apply scalar_mul_injective _ (internalDenominator_ne_zero a L R)
      dsimp only
      rw [mul_add,denominator_tensorClearedLeading,denominator_tensorClearedLeading,denominator_tensorClearedLeading]
      simp only [refinedCenterPolynomial,Submodule.coe_add,map_add]
    map_smul' := by
      intro r f
      apply scalar_mul_injective _ (internalDenominator_ne_zero a L R)
      dsimp only
      rw [mul_smul_comm,denominator_tensorClearedLeading,denominator_tensorClearedLeading]
      simp only [refinedCenterPolynomial,Submodule.coe_smul,map_smul,RingHom.id_apply] }

noncomputable def normalizedTensorSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ) :
    sourceTensorFiltration a c η hc θ L.dim R.dim W →ₗ[ℚ]
      MvPolynomial (L.node R).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)) :=
  (LinearMap.mulLeft ℚ (map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
    (internalNumerator a L R))).comp (tensorClearedLeadingMap a c η hc θ L R hL hR hχL hχR W)

theorem coproduct_normalized_symbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (f : sourceFiltration a c η hc θ (L.dim+R.dim) W) :
    normalizedTensorSymbol a c η hc θ L R hL hR
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ R hR) W
      ⟨separationCoefficient a c η hc
        ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) 0 f.val,
        separationCoefficient_filtration a c η hc θ L.dim R.dim _ W 0 f.val f.property⟩ =
    normalizedSymbol a c η hc θ (.node L R) ⟨hL,hR⟩
      (pairSymmetric_of_slope a c η θ hχ (.node L R) ⟨hL,hR⟩) W f := by
  let χL := pairSymmetric_of_slope a c η θ hχ L hL
  let χR := pairSymmetric_of_slope a c η θ hχ R hR
  let χT := pairSymmetric_of_slope a c η θ hχ (.node L R) ⟨hL,hR⟩
  let f0 : sourceTensorFiltration a c η hc θ L.dim R.dim W :=
    ⟨separationCoefficient a c η hc
      ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) 0 f.val,
      separationCoefficient_filtration a c η hc θ L.dim R.dim _ W 0 f.val f.property⟩
  have hd := denominator_tensorClearedLeading a c η hc θ L R hL hR χL χR W f0
  have hf := denominator_clearedLeading a c η hc θ (.node L R) ⟨hL,hR⟩ χT W f
  have hx := coproductSymbol_cross_cleared a c η hc θ hχ L R hL hR W f.val f.property
  rw [←hd,←hf,centerDenominator_node] at hx
  have he : tensorClearedLeading a c η hc θ L R hL hR χL χR W f0=
      map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (centerNumerator a (.node L R) (crossPairs L R))*
      clearedLeading a c η hc θ (.node L R) ⟨hL,hR⟩ χT W f := by
    apply scalar_mul_injective _ (centerDenominator_ne_zero a (.node L R))
    rw [centerDenominator_node]
    change map _ (internalDenominator a L R*centerDenominator a (.node L R) (crossPairs L R))*_=
      map _ (internalDenominator a L R*centerDenominator a (.node L R) (crossPairs L R))*_
    unfold internalDenominator at hx ⊢
    simp only [map_mul] at hx ⊢
    linear_combination hx
  change map _ (internalNumerator a L R)*tensorClearedLeading a c η hc θ L R hL hR χL χR W f0=
    map _ (centerNumerator a (.node L R) (L.node R).centerPairs)*
      clearedLeading a c η hc θ (.node L R) ⟨hL,hR⟩ χT W f
  rw [he,centerNumerator_node]
  simp only [internalNumerator,map_mul]
  ring

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma internalNumerator_ne_zero (a : I → I → ℕ) (L R : SplitTree I) :
    internalNumerator a L R≠0 := by
  apply mul_ne_zero
  · exact fun h=>centerNumerator_ne_zero a L ((rename_eq_zero_iff_of_injective _ Sum.inl_injective).mp h)
  · exact fun h=>centerNumerator_ne_zero a R ((rename_eq_zero_iff_of_injective _ Sum.inr_injective).mp h)

lemma normalizedTensorSymbol_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (U V : ℤ)
    (x : sourceFiltration a c η hc θ L.dim U)
    (y : sourceFiltration a c η hc θ R.dim V) :
    normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR (U+V)
      ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,le_refl _,x.property,y.property,rfl⟩⟩=
      box (normalizedSymbol a c η hc θ L hL hχL U x)
        (normalizedSymbol a c η hc θ R hR hχR V y) := by
  let xy : sourceTensorFiltration a c η hc θ L.dim R.dim (U+V) :=
    ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,le_refl _,x.property,y.property,rfl⟩⟩
  have h : tensorClearedLeading a c η hc θ L R hL hR hχL hχR (U+V) xy=
      box (clearedLeading a c η hc θ L hL hχL U x) (clearedLeading a c η hc θ R hR hχR V y) := by
    apply scalar_mul_injective _ (internalDenominator_ne_zero a L R)
    dsimp only
    rw [denominator_tensorClearedLeading]
    change mapLinear _ (refinedCenterPolynomial a c η hc θ L R hL hR (x.val⊗ₜ[ℚ]y.val))=_
    rw [refinedLeadingPolynomial_tmul a c η hc θ L R hL hR U V x.val y.val x.property y.property,
      ←denominator_clearedLeading a c η hc θ L hL hχL U x,
      ←denominator_clearedLeading a c η hc θ R hR hχR V y,box_scalar_left]
    rfl
  change map _ (internalNumerator a L R)*tensorClearedLeading a c η hc θ L R hL hR hχL hχR (U+V) xy=
    box (map _ (centerNumerator a L L.centerPairs)*clearedLeading a c η hc θ L hL hχL U x)
      (map _ (centerNumerator a R R.centerPairs)*clearedLeading a c η hc θ R hR hχR V y)
  rw [h,box_scalar_left]
  rfl

lemma normalizedTensorSymbol_eq_zero_iff (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (f : sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W f=0 ↔
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
        (refinedCenterPolynomial a c η hc θ L R hL hR f.val)=0 := by
  change map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
    (internalNumerator a L R)*tensorClearedLeading a c η hc θ L R hL hR hχL hχR W f=0 ↔ _
  rw [SymbolCoordinates.scalar_mul_eq_zero_iff _ (internalNumerator_ne_zero a L R)]
  rw [←denominator_tensorClearedLeading a c η hc θ L R hL hR hχL hχR W f,
    SymbolCoordinates.scalar_mul_eq_zero_iff _ (internalDenominator_ne_zero a L R)]

theorem normalizedTensorSymbol_detect (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : I → ℕ) (W : ℤ) (x : sourceTensorFiltration a c η hc θ d e W)
    (h : ∀ (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
      (hd : L.dim=d) (he : R.dim=e),
      normalizedTensorSymbol a c η hc θ L R hL hR
        (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ R hR) W
        (hd ▸ he ▸ x)=0) :
    x.val∈sourceTensorFiltration a c η hc θ d e (W+1) := by
  apply tensor_leading_restrictions_detect a c η hc θ d e W x.val x.property
  rintro ⟨L,hoL,hL,hd,k,z⟩ ⟨R,hoR,hR,he,l,w⟩ hw
  subst d
  subst e
  have hp:=(normalizedTensorSymbol_eq_zero_iff a c η hc θ L R hL hR _ _ W x).mp (h L R hL hR rfl rfl)
  have ht:=congrArg (fun p=>componentTensor a (SlopeArithmetic.slope c η) (.node L R) (k,l)
    (AddMonoidAlgebra.coeff p (z.sumElim w))) hp
  have heq : 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=W := by
    change (2*L.totalDegree k+L.doubleShift a)+(2*R.totalDegree l+R.doubleShift a)=W at hw
    omega
  rw [coeff_mapLinear,componentTensor_weightComponent,ite_eq_left heq,
    AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,map_zero,
    refinedCenterPolynomial_coeff_test] at ht
  exact ht

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
