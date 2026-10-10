import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SymbolSwap
import OAI.Combinatorics.Chromatic.Shuffle.GradedCoproduct
import OAI.Combinatorics.Chromatic.Walls.FilteredTensorComm

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.LinearFiltration
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma box_swap {A B α β : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (p : MvPolynomial α A) (q : MvPolynomial β B) :
    extendPolynomial (Algebra.TensorProduct.comm ℚ A B).toAlgHom (Equiv.sumComm α β)
      (box p q)=box q p := by
  change extendPolynomial _ _
    (extendPolynomial (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] B) Sum.inl p*
      extendPolynomial (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A ⊗[ℚ] B) Sum.inr q)=
    extendPolynomial (Algebra.TensorProduct.includeLeft : B →ₐ[ℚ] B ⊗[ℚ] A) Sum.inl q*
      extendPolynomial (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] B ⊗[ℚ] A) Sum.inr p
  rw [map_mul,extendPolynomial_comp,extendPolynomial_comp,mul_comm]
  congr 1

noncomputable def sourceTensorComm (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    sourceTensorFiltration a c η hc θ d e W ≃ₗ[ℚ] sourceTensorFiltration a c η hc θ e d W :=
  tensorFiltrationComm (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ e) W

lemma normalizedTensorSymbol_tmul_eq (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W U V : ℤ) (hw : W=U+V)
    (x : sourceFiltration a c η hc θ L.dim U)
    (y : sourceFiltration a c η hc θ R.dim V) :
    normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W
      ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,hw.le,x.property,y.property,rfl⟩⟩=
      box (normalizedSymbol a c η hc θ L hL hχL U x)
        (normalizedSymbol a c η hc θ R hR hχR V y) := by
  subst W
  exact normalizedTensorSymbol_tmul a c η hc θ L R hL hR hχL hχR U V x y

lemma normalizedTensorSymbol_swap (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (z : sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    normalizedTensorSymbol a c η hc θ R L hR hL hχR hχL W
      (sourceTensorComm a c η hc θ L.dim R.dim W z)=
    extendPolynomial ((Regroup.swap L R).equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
      (Regroup.swap L R).centers
      (normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W z) := by
  let f := (normalizedTensorSymbol a c η hc θ R L hR hL hχR hχL W).comp
    (sourceTensorComm a c η hc θ L.dim R.dim W).toLinearMap
  let g := (extendPolynomial
    ((Regroup.swap L R).equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
    (Regroup.swap L R).centers).toLinearMap.comp
    (normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W)
  have he : f=g := by
    apply linearMap_span_ext
    rintro _ ⟨u,v,x,y,huv,hx,hy,rfl⟩
    change normalizedTensorSymbol a c η hc θ R L hR hL hχR hχL W
      (sourceTensorComm a c η hc θ L.dim R.dim W ⟨x⊗ₜ[ℚ]y,_⟩)=
      extendPolynomial _ _ (normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W ⟨x⊗ₜ[ℚ]y,_⟩)
    by_cases hw : W=u+v
    · subst W
      have hl:=normalizedTensorSymbol_tmul_eq a c η hc θ R L hR hL hχR hχL (u+v) v u
        (by omega) ⟨y,hy⟩ ⟨x,hx⟩
      rw [normalizedTensorSymbol_tmul a c η hc θ L R hL hR hχL hχR u v ⟨x,hx⟩ ⟨y,hy⟩]
      exact hl.trans (box_swap _ _).symm
    · have hnext : x⊗ₜ[ℚ]y∈sourceTensorFiltration a c η hc θ L.dim R.dim (W+1) :=
        Submodule.subset_span ⟨u,v,x,y,by omega,hx,hy,rfl⟩
      rw [normalizedTensorSymbol_next_zero a c η hc θ L R hL hR hχL hχR W _ hnext,map_zero]
      apply normalizedTensorSymbol_next_zero
      exact comm_mem_tensorFiltration _ _ (W+1) _ hnext
  exact LinearMap.congr_fun he z

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
open LinearFiltration
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance cocommTensorBCommRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d ⊗[ℚ] B a μ e) := inferInstance
noncomputable local instance cocommTensorBAlgebra (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d ⊗[ℚ] B a μ e) := inferInstance

noncomputable def sourceGradeDimensionEquiv (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ) :
    SourceAssociatedGrade a c η hc θ d W ≃ₗ[ℚ] SourceAssociatedGrade a c η hc θ e W := by
  subst e
  exact LinearEquiv.refl _ _

lemma sourceGradeDimensionEquiv_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ) (f : sourceFiltration a c η hc θ d W) :
    sourceGradeDimensionEquiv a c η hc θ h W (Submodule.Quotient.mk f)=
      Submodule.Quotient.mk (filtrationDimensionEquiv a c η hc θ h W f) := by
  subst e
  rfl

noncomputable def sourceTensorGradeComm (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    SourceTensorAssociatedGrade a c η hc θ d e W →ₗ[ℚ] SourceTensorAssociatedGrade a c η hc θ e d W :=
  tensorGradeComm (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ e) W

lemma sourceTensorGradeComm_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) (x : sourceTensorFiltration a c η hc θ d e W) :
    sourceTensorGradeComm a c η hc θ d e W (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk (SplitTree.sourceTensorComm a c η hc θ d e W x) := rfl

lemma separationCoproduct_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ)
    (f : sourceFiltration a c η hc θ (d+e) W) :
    separationCoproduct a c η hc θ d e hs W (Submodule.Quotient.mk f)=
      Submodule.Quotient.mk (separationCoefficientRestricted a c η hc θ d e hs W 0 f) := rfl

theorem separationCoproduct_cocommutative (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ (d+e) W) :
    separationCoproduct a c η hc θ e d hs.symm W
      (sourceGradeDimensionEquiv a c η hc θ (add_comm d e) W f)=
      (-1:ℚ)^eulerForm a d e • sourceTensorGradeComm a c η hc θ d e W
        (separationCoproduct a c η hc θ d e hs W f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [sourceGradeDimensionEquiv_mk a c η hc θ (add_comm d e) W f,
      separationCoproduct_mk a c η hc θ e d hs.symm W,
      separationCoproduct_mk a c η hc θ d e hs W,
      sourceTensorGradeComm_mk a c η hc θ d e W]
    apply sub_eq_zero.mp
    change Submodule.Quotient.mk
      (separationCoefficientRestricted a c η hc θ e d hs.symm W 0
        (filtrationDimensionEquiv a c η hc θ (add_comm d e) W f) -
        (-1:ℚ)^eulerForm a d e •
          SplitTree.sourceTensorComm a c η hc θ d e W
            (separationCoefficientRestricted a c η hc θ d e hs W 0 f))=0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    let x := separationCoefficientRestricted a c η hc θ e d hs.symm W 0
        (filtrationDimensionEquiv a c η hc θ (add_comm d e) W f) -
      (-1:ℚ)^eulerForm a d e • SplitTree.sourceTensorComm a c η hc θ d e W
        (separationCoefficientRestricted a c η hc θ d e hs W 0 f)
    change x.val ∈ sourceTensorFiltration a c η hc θ e d (W+1)
    apply SplitTree.normalizedTensorSymbol_detect a c η hc θ hχ e d W x
    intro R L hR hL he hd
    subst d
    subst e
    let N := SplitTree.normalizedTensorSymbol a c η hc θ R L hR hL
      (SplitTree.pairSymmetric_of_slope a c η θ hχ R hR)
      (SplitTree.pairSymmetric_of_slope a c η θ hχ L hL) W
    let C := separationCoefficientRestricted a c η hc θ L.dim R.dim hs W 0 f
    let C' := separationCoefficientRestricted a c η hc θ R.dim L.dim hs.symm W 0
      (filtrationDimensionEquiv a c η hc θ (add_comm L.dim R.dim) W f)
    change N (C' - (-1:ℚ)^eulerForm a L.dim R.dim •
      SplitTree.sourceTensorComm a c η hc θ L.dim R.dim W C)=0
    rw [N.map_sub, N.map_smul]
    change SplitTree.normalizedTensorSymbol a c η hc θ R L hR hL _ _ W C' -
      (-1:ℚ)^eulerForm a L.dim R.dim •
        SplitTree.normalizedTensorSymbol a c η hc θ R L hR hL _ _ W
          (SplitTree.sourceTensorComm a c η hc θ L.dim R.dim W C)=0
    have hC := SplitTree.coproduct_normalized_symbol a c η hc θ hχ L R hL hR W f
    have hC' := SplitTree.coproduct_normalized_symbol a c η hc θ hχ R L hR hL W
      (filtrationDimensionEquiv a c η hc θ (add_comm L.dim R.dim) W f)
    change SplitTree.normalizedTensorSymbol a c η hc θ L R hL hR _ _ W C=_ at hC
    change SplitTree.normalizedTensorSymbol a c η hc θ R L hR hL _ _ W C'=_ at hC'
    rw [hC',SplitTree.normalizedTensorSymbol_swap,hC,
      SplitTree.Regroup.normalizedSymbol_swap a c η hc θ hχ L R hL hR]
    exact sub_self _

end ElementaryPositivity.RawShuffle

end

end OAI
