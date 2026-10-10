import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.DimensionEquivBTrans
import OAI.Combinatorics.Chromatic.Walls.RationalTensorDetection

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.LinearDetection
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

structure RestrictionIndex (c η : I → ℝ) (θ : ℝ) (d : I → ℕ) where
  tree : SplitTree I
  ordered : tree.IsOrderedList
  onSlope : tree.OnSlope c η θ
  dimension : tree.dim=d
  degree : tree.Degrees
  center : tree.Centers →₀ ℕ

def RestrictionIndex.weight (a : I → I → ℕ) {c η : I → ℝ} {θ : ℝ} {d : I → ℕ}
    (j : RestrictionIndex c η θ d) : ℤ :=
  2*j.tree.totalDegree j.degree+j.tree.doubleShift a

noncomputable def indexedRestriction (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (j : RestrictionIndex c η θ d) :=
  restrictionTest a c η hc θ j.tree j.onSlope j.dimension j.degree j.center

lemma sourceFiltration_eq_testFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :
    sourceFiltration a c η hc θ d W = testFiltration (indexedRestriction a c η hc θ d)
      (RestrictionIndex.weight a) W := by
  ext f
  rw [mem_testFiltration]
  constructor
  · intro hf j hj
    exact hf j.tree j.ordered j.onSlope j.dimension j.degree j.center hj
  · intro hf T hT hs hd k z hw
    exact hf ⟨T,hT,hs,hd,k,z⟩ hw

noncomputable def sourceTensorFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    Submodule ℚ (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e) :=
  additiveTensorFiltration (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ e) W

theorem sourceTensorFiltration_iff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e) :
    x∈sourceTensorFiltration a c η hc θ d e W ↔
      ∀ i : RestrictionIndex c η θ d, ∀ j : RestrictionIndex c η θ e,
        i.weight a+j.weight a<W → TensorProduct.map
          (indexedRestriction a c η hc θ d i) (indexedRestriction a c η hc θ e j) x=0 := by
  have hd : sourceFiltration a c η hc θ d =
      testFiltration (indexedRestriction a c η hc θ d) (RestrictionIndex.weight a) :=
    funext (sourceFiltration_eq_testFiltration a c η hc θ d)
  have he : sourceFiltration a c η hc θ e =
      testFiltration (indexedRestriction a c η hc θ e) (RestrictionIndex.weight a) :=
    funext (sourceFiltration_eq_testFiltration a c η hc θ e)
  unfold sourceTensorFiltration
  rw [hd,he]
  apply additiveTensorFiltration_iff_tests
    (L := -interaction a d d) (R := -interaction a e e)
  · rw [← hd,sourceFiltration_lower]
  · rw [← he,sourceFiltration_lower]

theorem tensor_leading_restrictions_detect (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e)
    (hx : x∈sourceTensorFiltration a c η hc θ d e W)
    (h : ∀ i : RestrictionIndex c η θ d, ∀ j : RestrictionIndex c η θ e,
      i.weight a+j.weight a=W → TensorProduct.map
        (indexedRestriction a c η hc θ d i) (indexedRestriction a c η hc θ e j) x=0) :
    x∈sourceTensorFiltration a c η hc θ d e (W+1) := by
  rw [sourceTensorFiltration_iff] at hx ⊢
  intro i j hij
  by_cases heq : i.weight a+j.weight a=W
  · exact h i j heq
  · exact hx i j (by omega)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.IndependentCoefficientTensor
open MvPolynomial
variable {α β R : Type*} [CommRing R]

lemma sumElim_eq_iff (a c : α →₀ ℕ) (b d : β →₀ ℕ) :
    a.sumElim b=c.sumElim d ↔ a=c ∧ b=d := by
  constructor
  · intro h
    constructor
    · ext i; exact congrArg (fun f : α ⊕ β →₀ ℕ=>f (Sum.inl i)) h
    · ext i; exact congrArg (fun f : α ⊕ β →₀ ℕ=>f (Sum.inr i)) h
  · rintro ⟨rfl,rfl⟩; rfl

lemma coeff_independent_product (p : MvPolynomial α R) (q : MvPolynomial β R)
    (z : α →₀ ℕ) (w : β →₀ ℕ) :
    (rename Sum.inl p * rename Sum.inr q).coeff (z.sumElim w)=p.coeff z*q.coeff w := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => simp only [map_add,add_mul,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hr]
  | monomial a c =>
    induction q using MvPolynomial.induction_on' with
    | add q r hq hr => simp only [map_add,mul_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hq,hr]
    | monomial b d =>
      rw [rename_monomial,rename_monomial,monomial_mul_monomial,←Finsupp.sumElim_eq_add]
      simp only [coeff_monomial,sumElim_eq_iff]
      by_cases ha : a=z <;> by_cases hb : b=w <;> simp [ha,hb]

end ElementaryPositivity.IndependentCoefficientTensor

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.IndependentCoefficientTensor
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
namespace SplitTree

lemma centerTranslation_node_coeff (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T U : SplitTree I) (z : T.Centers →₀ ℕ) (w : U.Centers →₀ ℕ)
    (x : tensor (quotientFamily a μ) (.node T U)) :
    (centerTranslation (quotientFamily a μ) (taylorB a μ) (.node T U) x).coeff (z.sumElim w)=
      TensorProduct.map
        (((lcoeff _ z).restrictScalars ℚ).comp (centerTranslation (quotientFamily a μ) (taylorB a μ) T).toLinearMap)
        (((lcoeff _ w).restrictScalars ℚ).comp (centerTranslation (quotientFamily a μ) (taylorB a μ) U).toLinearMap) x := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    erw [centerTranslation_tmul]
    change
      (rename Sum.inl (map (Algebra.TensorProduct.includeLeft : tensor (quotientFamily a μ) T →ₐ[ℚ]
        tensor (quotientFamily a μ) T ⊗[ℚ] tensor (quotientFamily a μ) U).toRingHom
        (centerTranslation (quotientFamily a μ) (taylorB a μ) T x)) *
       rename Sum.inr (map (Algebra.TensorProduct.includeRight : tensor (quotientFamily a μ) U →ₐ[ℚ]
        tensor (quotientFamily a μ) T ⊗[ℚ] tensor (quotientFamily a μ) U).toRingHom
        (centerTranslation (quotientFamily a μ) (taylorB a μ) U y))).coeff (z.sumElim w)=_
    rw [coeff_independent_product,coeff_map,coeff_map]
    change (_⊗ₜ[ℚ]1)*(1⊗ₜ[ℚ]_)=_
    rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
    rfl
  | add x y hx hy => simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hx,hy]

lemma restrictionTest_node (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T U : SplitTree I) (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (k : T.Degrees) (l : U.Degrees) (z : T.Centers →₀ ℕ) (w : U.Centers →₀ ℕ)
    (f : B a (SlopeArithmetic.slope c η) (T.dim+U.dim)) :
    restrictionTest a c η hc θ (.node T U) ⟨hT,hU⟩ rfl (k,l) (z.sumElim w) f=
    TensorProduct.map (restrictionTest a c η hc θ T hT rfl k z)
      (restrictionTest a c η hc θ U hU rfl l w)
      (RawShuffle.restrictionB a c η hc ((slope_dim c η hc hT).trans (slope_dim c η hc hU).symm)
        (firstCut T.dim U.dim) f) := by
  change componentTensor a (SlopeArithmetic.slope c η) (.node T U) (k,l)
    ((centerTranslation _ _ (.node T U)
      (restrictionB a c η hc θ (.node T U) ⟨hT,hU⟩ f)).coeff (z.sumElim w))=_
  rw [centerTranslation_node_coeff]
  simp only [restrictionB,AlgHom.comp_apply]
  generalize RawShuffle.restrictionB a c η hc ((slope_dim c η hc hT).trans (slope_dim c η hc hU).symm) (firstCut T.dim U.dim) f=x
  induction x using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]
end SplitTree

lemma restrictionB_sourceTensorFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    restrictionB a c η hc hs (firstCut d e) f∈sourceTensorFiltration a c η hc θ d e W := by
  rw [sourceTensorFiltration_iff]
  rintro ⟨T,hT,ht,hd,k,z⟩ ⟨U,hU,hu,he,l,w⟩ hw
  subst d
  subst e
  have hh:=sourceFiltration_allTrees a c η hc θ W f hf
    (.node T U) ⟨ht,hu⟩ rfl (k,l) (z.sumElim w)
  rw [SplitTree.restrictionTest_node (hT:=ht) (hU:=hu)] at hh
  apply hh
  change 2*(T.totalDegree k+U.totalDegree l)+(T.doubleShift a+U.doubleShift a)<W
  change (2*T.totalDegree k+T.doubleShift a)+(2*U.totalDegree l+U.doubleShift a)<W at hw
  omega

end ElementaryPositivity.RawShuffle

end

end OAI
