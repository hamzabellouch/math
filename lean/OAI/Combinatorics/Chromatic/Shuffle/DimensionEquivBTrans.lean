import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Centers

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree.Regroup
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma dimensionEquivB_trans (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e f : I → ℕ} (h : d=e) (g : e=f) (x : B a μ d) :
    dimensionEquivB a μ g (dimensionEquivB a μ h x)=dimensionEquivB a μ (h.trans g) x := by
  subst e
  subst f
  rfl

lemma restrictionTest_natural (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d : I → ℕ} {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ) (hd : T.dim=d)
    (k : T.Degrees) (z : T.Centers →₀ ℕ) (f : B a (SlopeArithmetic.slope c η) d) :
    e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
        (restrictionTest a c η hc θ T hT hd k z f)=
      restrictionTest a c η hc θ U hU (e.dimension.symm.trans hd)
        (e.degrees k) (z.mapDomain e.centers) f := by
  change e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
    (componentTensor a (SlopeArithmetic.slope c η) T k
      ((centeredRestrictionB a c η hc θ T hT
        (dimensionEquivB a (SlopeArithmetic.slope c η) hd.symm f)).coeff z))=_
  rw [componentTensor_natural,← centeredRestrictionB_coeff a c η hc θ e hT hU]
  rw [dimensionEquivB_trans]
  rfl

end ElementaryPositivity.RawShuffle.SplitTree.Regroup

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem sourceFiltration_allTrees (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d : I → ℕ} (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) (T : SplitTree I)
    (hs : T.OnSlope c η θ) (hd : T.dim=d) (k : T.Degrees) (z : T.Centers →₀ ℕ)
    (hw : 2*T.totalDegree k+T.doubleShift a<W) :
    restrictionTest a c η hc θ T hs hd k z f=0 := by
  obtain ⟨U,hU,⟨e⟩⟩ := SplitTree.Regroup.ordered_normalization T
  apply (e.equivalence (SplitTree.quotientFamily a (SlopeArithmetic.slope c η))).injective
  rw [map_zero,SplitTree.Regroup.restrictionTest_natural a c η hc θ e hs (e.onSlope c η θ hs)]
  apply hf U hU
  rw [e.totalDegree,e.doubleShift]
  exact hw

end ElementaryPositivity.RawShuffle

end

end OAI
