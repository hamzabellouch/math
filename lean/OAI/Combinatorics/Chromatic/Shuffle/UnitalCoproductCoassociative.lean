import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalCoproductComparison
import OAI.Combinatorics.Chromatic.Walls.UnitalCoproductNaturality
import OAI.Combinatorics.Chromatic.Shuffle.PolynomialExtendInjective
import OAI.Combinatorics.Chromatic.Walls.TensorGradeFunctor

namespace OAI

section
namespace ElementaryPositivity.TensorTransport
open scoped TensorProduct
lemma assoc_sub_symm {M N P : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] [AddCommGroup P] [Module ℚ P]
    (x : (M⊗[ℚ]N)⊗[ℚ]P) (y : M⊗[ℚ](N⊗[ℚ]P)) :
    TensorProduct.assoc ℚ M N P (x-(TensorProduct.assoc ℚ M N P).symm y)=
      TensorProduct.assoc ℚ M N P x-y := by
  simp only [map_sub,LinearEquiv.apply_symm_apply]
end ElementaryPositivity.TensorTransport

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
  ElementaryPositivity.LinearFiltration SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] naturalTensorAdd naturalTensorModule pairAdd tripleAdd tripleFilterAdd

noncomputable local instance unitalTripleRightAdd (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e f : I → ℕ) : AddCommGroup (B a μ d⊗[ℚ](B a μ e⊗[ℚ]B a μ f)) :=
  TensorProduct.addCommGroup
noncomputable local instance unitalTripleRightModule (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e f : I → ℕ) : Module ℚ (B a μ d⊗[ℚ](B a μ e⊗[ℚ]B a μ f)) :=
  TensorProduct.leftModule

lemma unitalSeparationConstant_eq_linear (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (d e : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (hde : slope c η d=slope c η e) :
    unitalSeparationConstant a c η hc d e hs=
      separationCoefficient a c η hc (d:=d) (e:=e) hde 0 := by
  apply LinearMap.ext
  intro x
  exact unitalSeparationConstant_eq a c η hc d e hs hde x

theorem unitalCoproduct_coassoc_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e f : I → ℕ) (hd : OnSlopeOrZero c η θ d)
    (he : OnSlopeOrZero c η θ e) (hf : OnSlopeOrZero c η θ f)
    (W : ℤ) (x : B a (slope c η) ((d+e)+f))
    (hx : x∈unitalSourceFiltration a c η hc θ ((d+e)+f) W) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (unitalSeparationConstant a c η hc d e (hd.compatible he)) LinearMap.id
        (unitalSeparationConstant a c η hc (d+e) f ((hd.add hc he).compatible hf) x)) -
      TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc e f (he.compatible hf))
        (unitalSeparationConstant a c η hc d (e+f) (hd.compatible (he.add hc hf))
          (castB a (slope c η) (add_assoc d e f) x)) ∈
      additiveTensorFiltration (unitalSourceFiltration a c η hc θ d)
        (unitalSourceTensorFiltration a c η hc θ e f) (W+1) := by
  by_cases hd0 : d=0
  · subst d
    rw [unitalCoproduct_coassoc_zero_left a c η hc θ e f he hf x,sub_self]
    exact Submodule.zero_mem _
  by_cases he0 : e=0
  · subst e
    rw [unitalCoproduct_coassoc_zero_middle a c η hc θ d f hd hf x,sub_self]
    exact Submodule.zero_mem _
  by_cases hf0 : f=0
  · subst f
    rw [unitalCoproduct_coassoc_zero_right a c η hc θ d e hd he x,sub_self]
    exact Submodule.zero_mem _
  have hde : slope c η d=slope c η e := (hd.resolve_left hd0).trans (he.resolve_left he0).symm
  have hef : slope c η e=slope c η f := (he.resolve_left he0).trans (hf.resolve_left hf0).symm
  have hdef : slope c η (d+e)=slope c η f := (slope_add_same c η hc hde).trans (hde.trans hef)
  have hdef' : slope c η d=slope c η (e+f) := hde.trans (slope_add_same c η hc hef).symm
  rw [unitalSourceFiltration_nonzero a c η hc θ ((d+e)+f)
    (add_ne_zero_left _ _ (add_ne_zero_left _ _ hd0)) W] at hx
  have hm := separation_coassoc_filtration a c η hc θ hχ d e f hde hef W ⟨x,hx⟩
  have hm' := assoc_mem_tensorFiltration (sourceFiltration a c η hc θ d)
    (sourceFiltration a c η hc θ e) (sourceFiltration a c η hc θ f) (W+1) _ hm
  change TensorProduct.assoc ℚ _ _ _
    ((iteratedCoproductLeft a c η hc θ d e f hde hef W ⟨x,hx⟩).val -
      (TensorProduct.assoc ℚ _ _ _).symm
        (iteratedCoproductRight a c η hc θ d e f hde hef W ⟨x,hx⟩).val) ∈ _ at hm'
  rw [TensorTransport.assoc_sub_symm] at hm'
  rw [show unitalSourceFiltration a c η hc θ d=sourceFiltration a c η hc θ d from
      funext (unitalSourceFiltration_nonzero a c η hc θ d hd0),
    show unitalSourceTensorFiltration a c η hc θ e f=sourceTensorFiltration a c η hc θ e f from
      funext (unitalSourceTensorFiltration_nonzero a c η hc θ e f he0 hf0),
    unitalSeparationConstant_eq_linear a c η hc d e _ hde,
    unitalSeparationConstant_eq_linear a c η hc e f _ hef,
    unitalSeparationConstant_eq_linear a c η hc (d+e) f _ hdef,
    unitalSeparationConstant_eq_linear a c η hc d (e+f) _ hdef']
  change TensorProduct.assoc ℚ _ _ _
    (TensorProduct.map (separationCoefficient a c η hc hde 0) LinearMap.id
      (separationCoefficient a c η hc hdef 0 x)) -
    TensorProduct.map LinearMap.id (separationCoefficient a c η hc hef 0)
      (separationCoefficient a c η hc hdef' 0
        (filtrationDimensionEquiv a c η hc θ (add_assoc d e f) W ⟨x,hx⟩).val)∈_ at hm'
  rw [filtrationDimensionEquiv_castB] at hm'
  exact hm'

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
  ElementaryPositivity.LinearFiltration SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] naturalTensorAdd naturalTensorModule pairAdd tripleAdd tripleFilterAdd
  unitalTripleRightAdd unitalTripleRightModule

lemma unitalSeparationConstant_filtered (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (W : ℤ) (x : B a (slope c η) (d+e))
    (hx : x∈unitalSourceFiltration a c η hc θ (d+e) W) :
    unitalSeparationConstant a c η hc d e hs x∈unitalSourceTensorFiltration a c η hc θ d e W :=
  unitalSeparationSeries_coeff_filtration a c η hc θ d e hs W 0 x hx

noncomputable def unitalTensorCoproductLeft (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (W : ℤ) :
    UnitalSourceTensorGrade a c η hc θ (d+e) f W →ₗ[ℚ]
      TensorGrade (unitalSourceTensorFiltration a c η hc θ d e)
        (unitalSourceFiltration a c η hc θ f) W :=
  tensorGradeMap (unitalSourceFiltration a c η hc θ (d+e))
    (unitalSourceFiltration a c η hc θ f) (unitalSourceTensorFiltration a c η hc θ d e)
    (unitalSourceFiltration a c η hc θ f)
    (unitalSeparationConstant a c η hc d e hs) LinearMap.id
    (unitalSeparationConstant_filtered a c η hc θ d e hs) (fun _ _ h=>h) W

noncomputable def unitalTensorCoproductRight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : e=0 ∨ f=0 ∨ slope c η e=slope c η f) (W : ℤ) :
    UnitalSourceTensorGrade a c η hc θ d (e+f) W →ₗ[ℚ]
      TensorGrade (unitalSourceFiltration a c η hc θ d)
        (unitalSourceTensorFiltration a c η hc θ e f) W :=
  tensorGradeMap (unitalSourceFiltration a c η hc θ d)
    (unitalSourceFiltration a c η hc θ (e+f)) (unitalSourceFiltration a c η hc θ d)
    (unitalSourceTensorFiltration a c η hc θ e f) LinearMap.id
    (unitalSeparationConstant a c η hc e f hs)
    (fun _ _ h=>h) (unitalSeparationConstant_filtered a c η hc θ e f hs) W

theorem unitalGradeCoproduct_coassociative (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e f : I → ℕ) (hd : OnSlopeOrZero c η θ d)
    (he : OnSlopeOrZero c η θ e) (hf : OnSlopeOrZero c η θ f)
    (W : ℤ) (x : UnitalSourceGrade a c η hc θ ((d+e)+f) W) :
    tensorGradeAssoc (unitalSourceFiltration a c η hc θ d)
      (unitalSourceFiltration a c η hc θ e) (unitalSourceFiltration a c η hc θ f) W
      (unitalTensorCoproductLeft a c η hc θ d e f (hd.compatible he) W
        (unitalGradeCoproduct a c η hc θ (d+e) f ((hd.add hc he).compatible hf) W x))=
      unitalTensorCoproductRight a c η hc θ d e f (he.compatible hf) W
        (unitalGradeCoproduct a c η hc θ d (e+f) (hd.compatible (he.add hc hf)) W
          (unitalGradeCast a c η hc θ (add_assoc d e f) rfl x)) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [unitalGradeCast_mk,unitalGradeCoproduct_mk,unitalGradeCoproduct_mk]
    apply sub_eq_zero.mp
    change mk _ _ ⟨TensorProduct.assoc ℚ _ _ _
        (TensorProduct.map (unitalSeparationConstant a c η hc d e (hd.compatible he)) LinearMap.id
          (unitalSeparationConstant a c η hc (d+e) f ((hd.add hc he).compatible hf) x.val)),_⟩ -
      mk _ _ ⟨TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc e f (he.compatible hf))
        (unitalSeparationConstant a c η hc d (e+f) (hd.compatible (he.add hc hf))
          (unitalFiltrationCast a c η hc θ (add_assoc d e f) rfl x).val),_⟩=0
    rw [←LinearMap.map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change TensorProduct.assoc ℚ _ _ _
        (TensorProduct.map (unitalSeparationConstant a c η hc d e (hd.compatible he)) LinearMap.id
          (unitalSeparationConstant a c η hc (d+e) f ((hd.add hc he).compatible hf) x.val)) -
      TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc e f (he.compatible hf))
        (unitalSeparationConstant a c η hc d (e+f) (hd.compatible (he.add hc hf))
          (unitalFiltrationCast a c η hc θ (add_assoc d e f) rfl x).val)∈
      additiveTensorFiltration (unitalSourceFiltration a c η hc θ d)
        (unitalSourceTensorFiltration a c η hc θ e f) (W+1)
    rw [unitalFiltrationCast_val]
    exact unitalCoproduct_coassoc_filtration a c η hc θ hχ d e f hd he hf W x.val x.property
end ElementaryPositivity.RawShuffle

end

end OAI
