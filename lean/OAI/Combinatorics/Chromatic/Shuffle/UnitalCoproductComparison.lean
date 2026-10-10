import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TensorSymbolSwap

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cocommTensorBCommRing cocommTensorBAlgebra

lemma unitalSeparationConstant_eq (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (d e : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (hde : slope c η d=slope c η e) (x : B a (slope c η) (d+e)) :
    unitalSeparationConstant a c η hc d e hs x=
      separationCoefficient a c η hc (d:=d) (e:=e) hde 0 x := by
  have heq : unitalRestrictionRelativeB a c η hc hs=
      restrictionRelativeB a c η hc hde (firstCut d e) := by
    unfold unitalRestrictionRelativeB restrictionRelativeB
    congr 1
  simp only [unitalSeparationConstant,unitalSeparationSeries,LinearMap.comp_apply,heq,
    separationCoefficient_eq_coeff,separationSeries,neg_zero]
  rfl

lemma filtrationDimensionEquiv_castB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ)
    (f : sourceFiltration a c η hc θ d W) :
    (filtrationDimensionEquiv a c η hc θ h W f).val=castB a (slope c η) h f.val := by
  subst e
  rfl

lemma separationCoproduct_cocommutative_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hs : slope c η d=slope c η e) (W : ℤ)
    (x : B a (slope c η) (d+e)) (hx : x∈sourceFiltration a c η hc θ (d+e) W) :
    separationCoefficient a c η hc (d:=e) (e:=d) hs.symm 0
        (castB a (slope c η) (add_comm d e) x) -
      (-1:ℚ)^eulerForm a d e • TensorProduct.comm ℚ _ _
        (separationCoefficient a c η hc (d:=d) (e:=e) hs 0 x) ∈
      sourceTensorFiltration a c η hc θ e d (W+1) := by
  have h := separationCoproduct_cocommutative a c η hc θ hχ d e hs W
    (Submodule.Quotient.mk ⟨x,hx⟩)
  rw [sourceGradeDimensionEquiv_mk,separationCoproduct_mk,separationCoproduct_mk,
    sourceTensorGradeComm_mk] at h
  have hz := sub_eq_zero.mpr h
  change Submodule.Quotient.mk
    (separationCoefficientRestricted a c η hc θ e d hs.symm W 0
        (filtrationDimensionEquiv a c η hc θ (add_comm d e) W ⟨x,hx⟩) -
      (-1:ℚ)^eulerForm a d e • SplitTree.sourceTensorComm a c η hc θ d e W
        (separationCoefficientRestricted a c η hc θ d e hs W 0 ⟨x,hx⟩))=0 at hz
  have hm := (Submodule.Quotient.mk_eq_zero
    (next (sourceTensorFiltration a c η hc θ e d W)
      (sourceTensorFiltration a c η hc θ e d (W+1)))).mp hz
  change separationCoefficient a c η hc hs.symm 0
      (filtrationDimensionEquiv a c η hc θ (add_comm d e) W ⟨x,hx⟩).val -
      (-1:ℚ)^eulerForm a d e • TensorProduct.comm ℚ _ _
        (separationCoefficient a c η hc hs 0 x)∈sourceTensorFiltration a c η hc θ e d (W+1) at hm
  rw [filtrationDimensionEquiv_castB] at hm
  exact hm

lemma unitalSeparationConstant_cocommutative_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (W : ℤ)
    (x : B a (slope c η) (d+e)) (hx : x∈unitalSourceFiltration a c η hc θ (d+e) W) :
    unitalSeparationConstant a c η hc e d (he.compatible hd)
        (castB a (slope c η) (add_comm d e) x) -
      (-1:ℚ)^eulerForm a d e • TensorProduct.comm ℚ _ _
        (unitalSeparationConstant a c η hc d e (hd.compatible he) x) ∈
      unitalSourceTensorFiltration a c η hc θ e d (W+1) := by
  by_cases hd0 : d=0
  · subst d
    have hL := unitalSeparationConstant_zero_left a c η hc e
      (castB a (slope c η) (zero_add e) x)
    have hR := unitalSeparationConstant_zero_right a c η hc e
      (castB a (slope c η) (zero_add e) x)
    simp only [castB_trans,castB_rfl] at hL hR
    rw [hL,hR,TensorProduct.comm_tmul]
    simp [eulerForm]
  by_cases he0 : e=0
  · subst e
    have hL := unitalSeparationConstant_zero_left a c η hc d
      (castB a (slope c η) (add_zero d) x)
    have hR := unitalSeparationConstant_zero_right a c η hc d
      (castB a (slope c η) (add_zero d) x)
    simp only [castB_rfl] at hL hR
    rw [hL,hR,TensorProduct.comm_tmul]
    simp [eulerForm]
  have hde : slope c η d=slope c η e := (hd.compatible he).resolve_left hd0 |>.resolve_left he0
  rw [unitalSourceFiltration_nonzero a c η hc θ (d+e) (add_ne_zero_left _ _ hd0) W] at hx
  rw [unitalSourceTensorFiltration_nonzero a c η hc θ e d he0 hd0,
    unitalSeparationConstant_eq a c η hc e d _ hde.symm,
    unitalSeparationConstant_eq a c η hc d e _ hde]
  exact separationCoproduct_cocommutative_filtration a c η hc θ hχ d e hde W x hx

end ElementaryPositivity.RawShuffle

end

end OAI
