import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.NormalizedTensorSymbol
import OAI.Combinatorics.Chromatic.Shuffle.PrimitiveSpace

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open SeparationInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def nextTensorFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    Submodule ℚ (sourceTensorFiltration a c η hc θ d e W) :=
  (sourceTensorFiltration a c η hc θ d e (W+1)).comap
    (sourceTensorFiltration a c η hc θ d e W).subtype

abbrev SourceTensorAssociatedGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :=
  LinearFiltration.Grade (sourceTensorFiltration a c η hc θ d e W)
    (sourceTensorFiltration a c η hc θ d e (W+1))

noncomputable def separationCoefficientRestricted (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W j : ℤ) :
    sourceFiltration a c η hc θ (d+e) W →ₗ[ℚ] sourceTensorFiltration a c η hc θ d e W :=
  ((separationCoefficient a c η hc hs j).comp
    (sourceFiltration a c η hc θ (d+e) W).subtype).codRestrict
      (sourceTensorFiltration a c η hc θ d e W)
      (fun f=>separationCoefficient_filtration a c η hc θ d e hs W j f.val f.property)

noncomputable def gradeSeparationCoefficient (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W j : ℤ) :
    SourceAssociatedGrade a c η hc θ (d+e) W →ₗ[ℚ]
      SourceTensorAssociatedGrade a c η hc θ d e W :=
  LinearFiltration.map (sourceFiltration a c η hc θ (d+e) W)
    (sourceFiltration a c η hc θ (d+e) (W+1))
    (sourceTensorFiltration a c η hc θ d e W)
    (sourceTensorFiltration a c η hc θ d e (W+1))
    (separationCoefficient a c η hc hs j)
    (separationCoefficient_filtration a c η hc θ d e hs W j)
    (separationCoefficient_filtration a c η hc θ d e hs (W+1) j)

lemma gradeSeparationCoefficient_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W j : ℤ)
    (f : sourceFiltration a c η hc θ (d+e) W) :
    gradeSeparationCoefficient a c η hc θ d e hs W j (Submodule.Quotient.mk f)=
      LinearFiltration.mk (sourceTensorFiltration a c η hc θ d e W)
        (sourceTensorFiltration a c η hc θ d e (W+1))
        (separationCoefficientRestricted a c η hc θ d e hs W j f) := rfl

theorem gradeSeparationCoefficient_negative (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (W j : ℤ) (hj : j<0) : gradeSeparationCoefficient a c η hc θ d e hs W j=0 := by
  apply LinearFiltration.map_eq_zero
  exact separationCoefficient_negative_filtration a c η hc θ hχ d e hs W j hj

noncomputable def separationCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ) :
    SourceAssociatedGrade a c η hc θ (d+e) W →ₗ[ℚ]
      SourceTensorAssociatedGrade a c η hc θ d e W :=
  gradeSeparationCoefficient a c η hc θ d e hs W 0

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
open scoped TensorProduct
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SplitTree.Regroup
omit [Fintype I] [DecidableEq I] in
lemma proper {T U : SplitTree I} (e : Regroup T U) (hT : T.IsProper) : U.IsProper := by
  induction e with
  | refl T => exact hT
  | assoc T U V => trivial
  | swap T U => trivial
  | node e f he hf => trivial
  | trans e f he hf => exact hf (he hT)
end SplitTree.Regroup

lemma properSourceFiltration_allTrees (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d : I → ℕ} (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈properSourceFiltration a c η hc θ d W) (T : SplitTree I)
    (hp : T.IsProper) (hs : T.OnSlope c η θ) (hd : T.dim=d)
    (k : T.Degrees) (z : T.Centers →₀ ℕ) (hw : 2*T.totalDegree k+T.doubleShift a<W) :
    restrictionTest a c η hc θ T hs hd k z f=0 := by
  obtain ⟨U,hU,⟨e⟩⟩ := SplitTree.Regroup.ordered_normalization T
  apply (e.equivalence (SplitTree.quotientFamily a (SlopeArithmetic.slope c η))).injective
  rw [map_zero,SplitTree.Regroup.restrictionTest_natural a c η hc θ e hs (e.onSlope c η θ hs)]
  apply hf U hU (e.proper hp)
  rw [e.totalDegree,e.doubleShift]
  exact hw

namespace SplitTree
lemma totalLeadingPolynomial_proper_next_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hp : T.IsProper)
    (hT : T.OnSlope c η θ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈properSourceFiltration a c η hc θ T.dim (W+1)) :
    totalLeadingPolynomial a c η hc θ T hT W f=0 := by
  ext z
  simp only [totalLeadingPolynomial,coeff_mapLinear,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  apply componentTensor_detect a (SlopeArithmetic.slope c η) T
  intro k
  rw [componentTensor_weightComponent]
  split_ifs with hw
  · exact properSourceFiltration_allTrees a c η hc θ (W+1) f hf T hp hT rfl k z (by omega)
  · rfl

lemma tensorTest_next_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (W : ℤ) (x : B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) R.dim)
    (hx : x∈sourceTensorFiltration a c η hc θ L.dim R.dim (W+1))
    (k : L.Degrees) (l : R.Degrees) (z : L.Centers →₀ ℕ) (w : R.Centers →₀ ℕ)
    (hw : (2*L.totalDegree k+L.doubleShift a)+(2*R.totalDegree l+R.doubleShift a)=W) :
    TensorProduct.map (restrictionTest a c η hc θ L hL rfl k z)
      (restrictionTest a c η hc θ R hR rfl l w) x=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨U,V,x,y,hUV,hx,hy,rfl⟩
    rw [TensorProduct.map_tmul]
    by_cases h : 2*L.totalDegree k+L.doubleShift a<U
    · rw [sourceFiltration_allTrees a c η hc θ U x hx L hL rfl k z h,TensorProduct.zero_tmul]
    · rw [sourceFiltration_allTrees a c η hc θ V y hy R hR rfl l w (by omega),TensorProduct.tmul_zero]
  | zero => exact map_zero _
  | add x y hx hy hix hiy => rw [map_add,hix,hiy,add_zero]
  | smul r x hx hix => rw [map_smul,hix,smul_zero]

lemma normalizedTensorSymbol_next_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (x : sourceTensorFiltration a c η hc θ L.dim R.dim W)
    (hx : x.val∈sourceTensorFiltration a c η hc θ L.dim R.dim (W+1)) :
    normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W x=0 := by
  rw [normalizedTensorSymbol_eq_zero_iff]
  ext s
  rw [coeff_mapLinear,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  apply componentTensor_detect a (SlopeArithmetic.slope c η) (.node L R)
  rintro ⟨k,l⟩
  rw [componentTensor_weightComponent]
  split_ifs with hw
  · let z := s.comapDomain Sum.inl Sum.inl_injective.injOn
    let w := s.comapDomain Sum.inr Sum.inr_injective.injOn
    have hsw : z.sumElim w=s := Finsupp.comapDomain_sumElim_comapDomain s
    rw [←hsw,refinedCenterPolynomial_coeff_test]
    apply tensorTest_next_zero a c η hc θ L R hL hR W x.val hx k l z w
    change 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=W at hw
    omega
  · rfl
end SplitTree

lemma separationCoproduct_mk_eq_zero_iff (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ)
    (f : sourceFiltration a c η hc θ (d+e) W) :
    separationCoproduct a c η hc θ d e hs W (Submodule.Quotient.mk f)=0 ↔
      separationCoefficient a c η hc hs 0 f.val∈sourceTensorFiltration a c η hc θ d e (W+1) :=
  Submodule.Quotient.mk_eq_zero _

lemma separationCoproduct_primitive_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ (d+e) W)
    (hf : f∈primitiveSpace a c η hc θ hχ (d+e) W) :
    separationCoproduct a c η hc θ d e hs W f=0 := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [primitiveSpace_mk_iff] at hf
    rw [separationCoproduct_mk_eq_zero_iff]
    apply SplitTree.normalizedTensorSymbol_detect a c η hc θ hχ d e W
      (separationCoefficientRestricted a c η hc θ d e hs W 0 f)
    intro L R hL hR hd he
    subst d
    subst e
    apply (SplitTree.coproduct_normalized_symbol a c η hc θ hχ L R hL hR W f).trans
    rw [SplitTree.normalizedSymbol_eq_zero_iff]
    exact SplitTree.totalLeadingPolynomial_proper_next_zero a c η hc θ (.node L R) trivial ⟨hL,hR⟩ W f.val hf

theorem primitiveSpace_iff_coproducts_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ d W) :
    f∈primitiveSpace a c η hc θ hχ d W ↔
      ∀ (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
        (hd : L.dim+R.dim=d),
      separationCoproduct a c η hc θ L.dim R.dim
        ((SplitTree.slope_dim c η hc hL).trans (SplitTree.slope_dim c η hc hR).symm) W
        (hd.symm ▸ f)=0 := by
  constructor
  · intro hf L R hL hR hd
    subst d
    exact separationCoproduct_primitive_zero a c η hc θ hχ L.dim R.dim _ W f hf
  · intro hf
    induction f using Submodule.Quotient.induction_on with
    | H f =>
      rw [primitiveSpace_mk_iff,proper_next_iff_symbols_zero a c η hc θ hχ d W f]
      rintro ⟨T,ho,hs,hd⟩ hp
      subst d
      cases T with
      | leaf d => exact False.elim hp
      | node L R =>
        have hf0:=hf L R hs.1 hs.2 rfl
        rw [separationCoproduct_mk_eq_zero_iff] at hf0
        change SplitTree.normalizedSymbol a c η hc θ (.node L R) hs _ W f=0
        rw [←SplitTree.coproduct_normalized_symbol a c η hc θ hχ L R hs.1 hs.2 W f]
        apply SplitTree.normalizedTensorSymbol_next_zero
        exact hf0

end ElementaryPositivity.RawShuffle

end

end OAI
