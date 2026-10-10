import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.NormalizedTensorSymbol
import OAI.Combinatorics.Chromatic.Walls.CenterCoefficientScalarLinear

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma weightComponent_weightComponent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (U W : ℤ) (x : tensor (quotientFamily a μ) T) :
    weightComponent a μ T U (weightComponent a μ T W x)=
      if U=W then weightComponent a μ T W x else 0 := by
  classical
  apply sub_eq_zero.mp
  apply componentTensor_detect a μ T
  intro k
  rw [map_sub,componentTensor_weightComponent,componentTensor_weightComponent]
  by_cases h : U=W <;> by_cases hw : 2*T.totalDegree k+T.doubleShift a=W <;>
    by_cases hu : 2*T.totalDegree k+T.doubleShift a=U <;>
    simp_all [componentTensor_weightComponent]

lemma mapLinear_weight_weight (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (U W : ℤ) (p : MvPolynomial T.Centers (tensor (quotientFamily a μ) T)) :
    mapLinear (weightComponent a μ T U) (mapLinear (weightComponent a μ T W) p)=
      if U=W then mapLinear (weightComponent a μ T W) p else 0 := by
  ext z
  by_cases h : U=W <;>
    simp only [coeff_mapLinear,weightComponent_weightComponent,h,ite_true,ite_false,
      AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]

lemma clearedLeading_internal_weight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W U : ℤ) (f : sourceFiltration a c η hc θ T.dim W) :
    mapLinear (weightComponent a (SlopeArithmetic.slope c η) T U)
      (clearedLeading a c η hc θ T hT hχ W f)=
      if U=W then clearedLeading a c η hc θ T hT hχ W f else 0 := by
  classical
  apply scalar_mul_injective _ (centerDenominator_ne_zero a T)
  dsimp only
  rw [←mapLinear_scalar_mul,denominator_clearedLeading]
  by_cases h : U=W
  · rw [ite_eq_left h,denominator_clearedLeading]
    exact (mapLinear_weight_weight a _ T U W _).trans (ite_eq_left h)
  · rw [ite_eq_right h,mul_zero]
    exact (mapLinear_weight_weight a _ T U W _).trans (ite_eq_right h)

lemma normalizedSymbol_internal_weight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W U : ℤ) (f : sourceFiltration a c η hc θ T.dim W) :
    mapLinear (weightComponent a (SlopeArithmetic.slope c η) T U)
      (normalizedSymbol a c η hc θ T hT hχ W f)=
      if U=W then normalizedSymbol a c η hc θ T hT hχ W f else 0 := by
  classical
  change mapLinear _ (map _ (centerNumerator a T T.centerPairs)*
    clearedLeading a c η hc θ T hT hχ W f)=_
  rw [mapLinear_scalar_mul,clearedLeading_internal_weight]
  split_ifs
  · rfl
  · exact mul_zero _

lemma tensorClearedLeading_internal_weight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W U : ℤ)
    (f : sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) U)
      (tensorClearedLeading a c η hc θ L R hL hR hχL hχR W f)=
      if U=W then tensorClearedLeading a c η hc θ L R hL hR hχL hχR W f else 0 := by
  classical
  apply scalar_mul_injective _ (internalDenominator_ne_zero a L R)
  dsimp only
  rw [←mapLinear_scalar_mul,denominator_tensorClearedLeading,mapLinear_weight_weight]
  split_ifs
  · exact (denominator_tensorClearedLeading a c η hc θ L R hL hR hχL hχR W f).symm
  · exact (mul_zero _).symm

lemma normalizedTensorSymbol_internal_weight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W U : ℤ)
    (f : sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) U)
      (normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W f)=
      if U=W then normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W f else 0 := by
  classical
  change mapLinear _ (map _ (internalNumerator a L R)*
    tensorClearedLeading a c η hc θ L R hL hR hχL hχR W f)=_
  rw [mapLinear_scalar_mul,tensorClearedLeading_internal_weight]
  split_ifs
  · rfl
  · exact mul_zero _

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
