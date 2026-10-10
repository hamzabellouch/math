import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Interaction

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

structure LeadingIndex (c η : I → ℝ) (θ : ℝ) (a : I → I → ℕ)
    (d : I → ℕ) (W : ℤ) where
  tree : SplitTree I
  ordered : tree.IsOrderedList
  onSlope : tree.OnSlope c η θ
  dimension : tree.dim=d
  degree : tree.Degrees
  center : tree.Centers →₀ ℕ
  weight : 2*tree.totalDegree degree+tree.doubleShift a=W

noncomputable def leadingRawMap (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :
    sourceFiltration a c η hc θ d W →ₗ[ℚ]
      (∀ j : LeadingIndex c η θ a d W,
        SplitTree.tensor (SplitTree.quotientFamily a (SlopeArithmetic.slope c η)) j.tree) :=
  LinearMap.pi fun j => (restrictionTest a c η hc θ j.tree j.onSlope j.dimension j.degree j.center).comp
    (sourceFiltration a c η hc θ d W).subtype

noncomputable def nextFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :
    Submodule ℚ (sourceFiltration a c η hc θ d W) :=
  (sourceFiltration a c η hc θ d (W+1)).comap (sourceFiltration a c η hc θ d W).subtype

abbrev SourceAssociatedGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :=
  (sourceFiltration a c η hc θ d W) ⧸ nextFiltration a c η hc θ d W

lemma leadingRawMap_ker (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :
    LinearMap.ker (leadingRawMap a c η hc θ d W)=nextFiltration a c η hc θ d W := by
  ext f
  change (leadingRawMap a c η hc θ d W f=0) ↔
    f.val∈sourceFiltration a c η hc θ d (W+1)
  constructor
  · intro h
    apply leading_restrictions_detect a c η hc θ d W f.val f.property
    intro T hT hs hd k z hw
    exact congrFun h (⟨T,hT,hs,hd,k,z,hw⟩ : LeadingIndex c η θ a d W)
  · intro h
    funext j
    exact h j.tree j.ordered j.onSlope j.dimension j.degree j.center (by rw [j.weight]; omega)

noncomputable def leadingGradeMap (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :
    SourceAssociatedGrade a c η hc θ d W →ₗ[ℚ]
      (∀ j : LeadingIndex c η θ a d W,
        SplitTree.tensor (SplitTree.quotientFamily a (SlopeArithmetic.slope c η)) j.tree) :=
  (nextFiltration a c η hc θ d W).liftQ (leadingRawMap a c η hc θ d W)
    (le_of_eq (leadingRawMap_ker a c η hc θ d W).symm)

theorem leadingGradeMap_injective (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :
    Function.Injective (leadingGradeMap a c η hc θ d W) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [← leadingRawMap_ker]
    exact hf

end ElementaryPositivity.RawShuffle

end

end OAI
