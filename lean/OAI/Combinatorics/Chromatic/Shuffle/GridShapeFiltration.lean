import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.Product
import OAI.Combinatorics.Chromatic.QuantumTorus.ProductUnitFiltration
import OAI.Combinatorics.Chromatic.Shuffle.ClearedSeparationB

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

def ShuffleFiltered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) : Prop :=
  ∀ (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e)
    (U V : ℤ) (f : B a (slope c η) d) (g : B a (slope c η) e),
    f∈unitalSourceFiltration a c η hc θ d U →
    g∈unitalSourceFiltration a c η hc θ e V →
    shuffleBUnit a c η hc d e (hd.compatible he) f g∈unitalSourceFiltration a c η hc θ (d+e) (U+V)

lemma quotient_fourGrid_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e : I → ℕ} (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (ih₁ : ShuffleFiltered a c η hc θ d₁ e₁) (ih₂ : ShuffleFiltered a c η hc θ d₂ e₂)
    (h : d+e=(d₁+e₁)+(d₂+e₂)) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V) :
    quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
      (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))∈
    unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V) := by
  classical
  by_cases hd : d₁+d₂=d
  · have he : e₁+e₂=e := by
      apply add_left_cancel (a:=d)
      calc
        d+(e₁+e₂)=(d₁+e₁)+(d₂+e₂) := by rw [←hd]; ac_rfl
        _=d+e := h.symm
    subst d
    subst e
    exact quotient_cellTransfer_filtered a c η hc θ d₁ e₁ d₂ e₂
      (hon.1.compatible hon.2.2.1) (hon.2.1.compatible hon.2.2.2)
      (hon.1.compatible hon.2.1) (hon.2.2.1.compatible hon.2.2.2)
      (ih₁ hon.1 hon.2.1) (ih₂ hon.2.2.1 hon.2.2.2) U V f g hf hg
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hd,map_zero,map_zero]
    exact Submodule.zero_mem _

lemma quotientTensor_cast_mem_unitalSource (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (W : ℤ) (f : S d⊗[ℚ]S e)
    (hf : quotientTensor a (slope c η) d e f∈unitalSourceTensorFiltration a c η hc θ d e W) :
    quotientTensor a (slope c η) d' e' (castTensor h k f)∈
      unitalSourceTensorFiltration a c η hc θ d' e' W := by
  subst d'
  subst e'
  exact hf

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
omit [∀ i,Fintype (A i)] in
lemma quotient_gridShapeTensor_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e α β : I → ℕ} (h : d+e=α+β)
    (ihα : ∀ d' e',d'+e'=α → ShuffleFiltered a c η hc θ d' e')
    (ihβ : ∀ d' e',d'+e'=β → ShuffleFiltered a c η hc θ d' e')
    (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p))
    (hon : CellsOnSlope c η θ
      (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)) :
    quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v)∈
      unitalSourceTensorFiltration a c η hc θ α β (U+V) := by
  have hα := (shape_add_complement u).trans (realization_card R)
  have hβ := (shape_add_complement v).trans (realization_card T)
  unfold gridShapeTensor
  apply quotientTensor_cast_mem_unitalSource
  apply quotient_fourGrid_filtered a c η hc θ _ _ _ _ hon
    (ihα _ _ hα) (ihβ _ _ hβ) _ U V f g hf hg
  rw [hα,hβ]
  exact h

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma restriction_shuffleBUnit_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e α β : I → ℕ) (hα : α≠0) (hβ : β≠0)
    (hdθ : slope c η d=θ) (hαθ : slope c η α=θ) (hβθ : slope c η β=θ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (h : α+β=d+e)
    (ihα : ∀ d' e',d'+e'=α → ShuffleFiltered a c η hc θ d' e')
    (ihβ : ∀ d' e',d'+e'=β → ShuffleFiltered a c η hc θ d' e')
    (U V : ℤ) (f : B a (slope c η) d) (g : B a (slope c η) e)
    (hf : f∈unitalSourceFiltration a c η hc θ d U)
    (hg : g∈unitalSourceFiltration a c η hc θ e V) :
    restrictionB a c η hc (hαθ.trans hβθ.symm) (firstCut α β)
      (castB a (slope c η) h.symm (shuffleBUnit a c η hc d e hs f g))∈
    sourceTensorFiltration a c η hc θ α β (U+V) := by
  classical
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      change restrictionB a c η hc (hαθ.trans hβθ.symm) (firstCut α β) (castB a (slope c η) h.symm
        (quotientAlg a (slope c η) (d+e) (shufflePolynomial a f g)))∈_
      rw [castB_mk,restrictionB_mk]
      apply sourceTensorFiltration_cross_cancel a c η hc θ α β (U+V)
      let R : Realization (α+β) (A:=fun i=>Fin ((α+β) i)) (fun _=>Finset.univ) :=
        fun _=>(Equiv.subtypeUnivEquiv (fun _=>Finset.mem_univ _)).symm
      rw [cleared_restriction_sameSlope_support a c η hc h.symm f g R (firstCut α β)
        (hαθ.trans hβθ.symm) (hdθ.trans hαθ.symm)]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro x hx
      apply Submodule.sum_mem
      intro y hy
      split_ifs with hon
      · rw [←unitalSourceTensorFiltration_nonzero a c η hc θ α β hα hβ]
        apply quotient_gridShapeTensor_filtered a c η hc θ h.symm ihα ihβ U V f g hf hg
        rwa [hαθ] at hon
      · exact Submodule.zero_mem _

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
open SplitTree
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sourceFiltration_of_binary (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (slope c η) d)
    (hleaf : ∀ t : ℚ,translationB a (slope c η) d t f∈degreeCutSubmodule a (slope c η) (.leaf d) W)
    (hpair : ∀ (α β : I → ℕ) (_hα : α≠0) (_hβ : β≠0)
      (hsα : slope c η α=θ) (hsβ : slope c η β=θ) (h : α+β=d),
      RawShuffle.restrictionB a c η hc (hsα.trans hsβ.symm) (firstCut α β)
        (castB a (slope c η) h.symm f)∈sourceTensorFiltration a c η hc θ α β W) :
    f∈sourceFiltration a c η hc θ d W := by
  intro T hT hs hd k z hw
  subst d
  cases T with
  | leaf d =>
    have hz : z=Finsupp.single () (z ()) := by apply Finsupp.ext; intro u; cases u; simp
    rw [hz,restrictionTest_leaf_coeff]
    exact ElementaryPositivity.CommonTranslation.polynomial_coeff_mem (A:=B a (slope c η) d)
      (degreeCutSubmodule a (slope c η) (.leaf d) W) (taylorB a (slope c η) d f)
      (fun t => by erw [taylorB_eval]; exact hleaf t) (z ()) k hw
  | node T U =>
    cases T with
    | node T V => exact False.elim hT
    | leaf α =>
      let β:=U.dim
      have hr:=hpair α β hs.1.1 (dim_ne_zero hs.2) hs.1.2 (slope_dim c η hc hs.2) rfl
      have ht:=(sourceTensorFiltration_iff a c η hc θ α β W _).mp hr
      let z₁ := z.comapDomain Sum.inl Sum.inl_injective.injOn
      let z₂ := z.comapDomain Sum.inr Sum.inr_injective.injOn
      have hz : z₁.sumElim z₂=z := Finsupp.comapDomain_sumElim_comapDomain z
      rw [←hz,restrictionTest_node]
      exact ht ⟨.leaf α,trivial,hs.1,rfl,k.1,z₁⟩ ⟨U,hT,hs.2,rfl,k.2,z₂⟩ (by
        convert hw using 1; dsimp [RestrictionIndex.weight,totalDegree,doubleShift]; ring)

end ElementaryPositivity.RawShuffle

end

end OAI
