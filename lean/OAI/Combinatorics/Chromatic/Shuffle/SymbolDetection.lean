import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.LeadingIndex
import OAI.Combinatorics.Chromatic.Shuffle.PointEvaluation

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

def SlopeEulerSymmetric (a : I → I → ℕ) (c η : I → ℝ) (θ : ℝ) : Prop :=
  ∀ d e : I → ℕ, d≠0 → e≠0 → SlopeArithmetic.slope c η d=θ →
    SlopeArithmetic.slope c η e=θ → eulerForm a d e=eulerForm a e d

namespace SplitTree
omit [DecidableEq I] in
lemma leafDimension_onSlope (T : SplitTree I) (c η : I → ℝ) (θ : ℝ)
    (hT : T.OnSlope c η θ) (i : T.Centers) :
    T.leafDimension i≠0 ∧ SlopeArithmetic.slope c η (T.leafDimension i)=θ := by
  induction T with
  | leaf d => exact hT
  | node l r hl hr =>
    cases i with
    | inl i => exact hl hT.1 i
    | inr i => exact hr hT.2 i

omit [DecidableEq I] in
lemma pairSymmetric_of_slope (a : I → I → ℕ) (c η : I → ℝ) (θ : ℝ)
    (hχ : SlopeEulerSymmetric a c η θ) (T : SplitTree I) (hT : T.OnSlope c η θ) :
    T.PairSymmetric a := by
  intro ij _
  obtain ⟨hi,hsi⟩:=T.leafDimension_onSlope c η θ hT ij.1
  obtain ⟨hj,hsj⟩:=T.leafDimension_onSlope c η θ hT ij.2
  exact hχ _ _ hi hj hsi hsj

lemma totalLeadingPolynomial_next_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim (W+1)) :
    totalLeadingPolynomial a c η hc θ T hT W f=0 := by
  ext z
  simp only [totalLeadingPolynomial,coeff_mapLinear,AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply]
  apply componentTensor_detect a (SlopeArithmetic.slope c η) T
  intro k
  rw [componentTensor_weightComponent]
  split_ifs with hw
  · exact sourceFiltration_allTrees a c η hc θ (W+1) f hf T hT rfl k z (by omega)
  · rfl

lemma totalLeadingPolynomial_zero_test (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : totalLeadingPolynomial a c η hc θ T hT W f=0)
    (k : T.Degrees) (z : T.Centers →₀ ℕ) (hw : 2*T.totalDegree k+T.doubleShift a=W) :
    restrictionTest a c η hc θ T hT rfl k z f=0 := by
  have h:=congrArg (fun polynomial=>componentTensor a (SlopeArithmetic.slope c η) T k
    (AddMonoidAlgebra.coeff polynomial z)) hf
  simpa [totalLeadingPolynomial,coeff_mapLinear,componentTensor_weightComponent,hw,
    restrictionTest,dimensionEquivB] using h
end SplitTree

structure SymbolIndex (c η : I → ℝ) (θ : ℝ) (d : I → ℕ) where
  tree : SplitTree I
  ordered : tree.IsOrderedList
  onSlope : tree.OnSlope c η θ
  dimension : tree.dim=d

noncomputable def filtrationDimensionEquiv (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ) :
    sourceFiltration a c η hc θ d W ≃ₗ[ℚ] sourceFiltration a c η hc θ e W := by
  subst e
  exact LinearEquiv.refl ℚ _

noncomputable def indexedSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d : I → ℕ) (W : ℤ) (j : SymbolIndex c η θ d) :
    sourceFiltration a c η hc θ d W →ₗ[ℚ]
      MvPolynomial j.tree.Centers (SplitTree.tensor (SplitTree.quotientFamily a (SlopeArithmetic.slope c η)) j.tree) :=
  (SplitTree.normalizedSymbol a c η hc θ j.tree j.onSlope
    (j.tree.pairSymmetric_of_slope a c η θ hχ j.onSlope) W).comp
      (filtrationDimensionEquiv a c η hc θ j.dimension.symm W).toLinearMap

noncomputable def symbolFamily (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    sourceFiltration a c η hc θ d W →ₗ[ℚ]
      (∀ j : SymbolIndex c η θ d,
        MvPolynomial j.tree.Centers (SplitTree.tensor (SplitTree.quotientFamily a (SlopeArithmetic.slope c η)) j.tree)) :=
  LinearMap.pi (indexedSymbol a c η hc θ hχ d W)

lemma symbolFamily_ker (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    LinearMap.ker (symbolFamily a c η hc θ hχ d W)=nextFiltration a c η hc θ d W := by
  ext f
  change symbolFamily a c η hc θ hχ d W f=0 ↔ f.val∈sourceFiltration a c η hc θ d (W+1)
  constructor
  · intro hf
    apply leading_restrictions_detect a c η hc θ d W f.val f.property
    intro T hT hs hd k z hw
    have h:=congrFun hf (⟨T,hT,hs,hd⟩ : SymbolIndex c η θ d)
    subst d
    change SplitTree.normalizedSymbol a c η hc θ T hs _ W f=0 at h
    rw [SplitTree.normalizedSymbol_eq_zero_iff] at h
    exact SplitTree.totalLeadingPolynomial_zero_test a c η hc θ T hs W f.val h k z hw
  · intro hf
    funext j
    change indexedSymbol a c η hc θ hχ d W j f=0
    obtain ⟨T,hT,hs,hd⟩:=j
    subst d
    change SplitTree.normalizedSymbol a c η hc θ T hs _ W f=0
    rw [SplitTree.normalizedSymbol_eq_zero_iff]
    exact SplitTree.totalLeadingPolynomial_next_zero a c η hc θ T hs W f.val hf

noncomputable def gradeSymbolFamily (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    SourceAssociatedGrade a c η hc θ d W →ₗ[ℚ]
      (∀ j : SymbolIndex c η θ d,
        MvPolynomial j.tree.Centers (SplitTree.tensor (SplitTree.quotientFamily a (SlopeArithmetic.slope c η)) j.tree)) :=
  (nextFiltration a c η hc θ d W).liftQ (symbolFamily a c η hc θ hχ d W)
    (le_of_eq (symbolFamily_ker a c η hc θ hχ d W).symm)

theorem gradeSymbolFamily_injective (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    Function.Injective (gradeSymbolFamily a c η hc θ hχ d W) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [← symbolFamily_ker a c η hc θ hχ d W]
    exact hf

end ElementaryPositivity.RawShuffle

end

end OAI
