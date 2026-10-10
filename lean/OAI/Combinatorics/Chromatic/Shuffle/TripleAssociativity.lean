import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CoproductIteration
import OAI.Combinatorics.Chromatic.Walls.FilteredTensorInsert
import OAI.Combinatorics.Chromatic.Shuffle.TensorPolynomialAssoc
import OAI.Combinatorics.Chromatic.Walls.TensorPolynomialLinear

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def normalizedRightTripleSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ) :
    additiveTensorFiltration (sourceFiltration a c η hc θ L.dim)
      (sourceTensorFiltration a c η hc θ M.dim N.dim) W →ₗ[ℚ]
      MvPolynomial (L.node (M.node N)).Centers
        (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (L.node (M.node N))) :=
  ((extendPolynomial ((Regroup.assoc L M N).equivalence
      (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom (Regroup.assoc L M N).centers).toLinearMap.comp
    (normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN W)).comp
    (tensorFiltrationAssoc (sourceFiltration a c η hc θ L.dim) (sourceFiltration a c η hc θ M.dim)
      (sourceFiltration a c η hc θ N.dim) W).symm.toLinearMap

lemma normalizedRightTripleSymbol_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (U V : ℤ)
    (x : sourceFiltration a c η hc θ L.dim U)
    (y : sourceTensorFiltration a c η hc θ M.dim N.dim V) :
    normalizedRightTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN (U+V)
      ⟨x.val⊗ₜ[ℚ]y.val,tmul_mem_additiveTensorFiltration _ _ (le_refl _) x.property y.property⟩=
      box (normalizedSymbol a c η hc θ L hL hχL U x)
        (normalizedTensorSymbol a c η hc θ M N hM hN hχM hχN V y) := by
  let E := (extendPolynomial ((Regroup.assoc L M N).equivalence
    (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom (Regroup.assoc L M N).centers).toLinearMap
  let F := (E.comp (normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN (U+V))).comp
    (unassocTensorFixedLeft (sourceFiltration a c η hc θ L.dim) (sourceFiltration a c η hc θ M.dim)
      (sourceFiltration a c η hc θ N.dim) U V x)
  let G := (boxRightLinear (normalizedSymbol a c η hc θ L hL hχL U x)).comp
    (normalizedTensorSymbol a c η hc θ M N hM hN hχM hχN V)
  have he : F=G := by
    apply linearMap_span_ext
    rintro _ ⟨s,t,p,q,hst,hp,hq,rfl⟩
    have hq' := sourceFiltration_antitone a c η hc θ N.dim (show V-s≤t by omega) hq
    let xp : sourceTensorFiltration a c η hc θ L.dim M.dim (U+s) :=
      ⟨x.val⊗ₜ[ℚ]p,tmul_mem_additiveTensorFiltration _ _ (le_refl _) x.property hp⟩
    have h1 := normalizedTripleSymbol_tmul_eq a c η hc θ L M N hL hM hN hχL hχM hχN
      (U+V) (U+s) (V-s) (by omega) xp ⟨q,hq'⟩
    have h2 := normalizedTensorSymbol_tmul a c η hc θ L M hL hM hχL hχM U s x ⟨p,hp⟩
    have h3 := normalizedTensorSymbol_tmul_eq a c η hc θ M N hM hN hχM hχN
      V s (V-s) (by omega) ⟨p,hp⟩ ⟨q,hq'⟩
    change E (normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN (U+V)
      ⟨(x.val⊗ₜ[ℚ]p)⊗ₜ[ℚ]q,_⟩)=
      box (normalizedSymbol a c η hc θ L hL hχL U x)
        (normalizedTensorSymbol a c η hc θ M N hM hN hχM hχN V ⟨p⊗ₜ[ℚ]q,_⟩)
    rw [h1,h3]
    change E (box (normalizedTensorSymbol a c η hc θ L M hL hM hχL hχM (U+s)
      ⟨x.val⊗ₜ[ℚ]p,_⟩) _)=_
    rw [h2]
    exact box_assoc _ _ _
  exact LinearMap.congr_fun he y

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection ElementaryPositivity.LinearFiltration
open SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma tensorSeparationRight_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : SlopeArithmetic.slope c η e=SlopeArithmetic.slope c η f)
    (W : ℤ) (x : B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) (e+f))
    (hx : x∈sourceTensorFiltration a c η hc θ d (e+f) W) :
    TensorProduct.map LinearMap.id (separationCoefficient a c η hc hs 0) x∈
      additiveTensorFiltration (sourceFiltration a c η hc θ d)
        (sourceTensorFiltration a c η hc θ e f) W :=
  tensor_map_mem_filtration (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ (e+f))
    (sourceFiltration a c η hc θ d) (sourceTensorFiltration a c η hc θ e f)
    LinearMap.id (separationCoefficient a c η hc hs 0)
    (fun _ _ h=>h) (fun w=>separationCoefficient_filtration a c η hc θ e f hs w 0) W x hx

noncomputable def tensorSeparationRight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : SlopeArithmetic.slope c η e=SlopeArithmetic.slope c η f) (W : ℤ) :
    sourceTensorFiltration a c η hc θ d (e+f) W →ₗ[ℚ]
      additiveTensorFiltration (sourceFiltration a c η hc θ d)
        (sourceTensorFiltration a c η hc θ e f) W :=
  let C : B a (SlopeArithmetic.slope c η) (e+f) →ₗ[ℚ]
      B a (SlopeArithmetic.slope c η) e⊗[ℚ]B a (SlopeArithmetic.slope c η) f :=
    separationCoefficient a c η hc hs 0
  let F : (B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) (e+f)) →ₗ[ℚ]
      (B a (SlopeArithmetic.slope c η) d⊗[ℚ](B a (SlopeArithmetic.slope c η) e⊗[ℚ]
        B a (SlopeArithmetic.slope c η) f)) := TensorProduct.map LinearMap.id C
  (F.comp (sourceTensorFiltration a c η hc θ d (e+f) W).subtype).codRestrict
    (additiveTensorFiltration (sourceFiltration a c η hc θ d)
      (sourceTensorFiltration a c η hc θ e f) W)
    (fun x=>tensorSeparationRight_filtration a c η hc θ d e f hs W x.val x.property)

namespace SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus

lemma normalizedRightTripleSymbol_tmul_eq (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a)
    (W U V : ℤ) (hw : W=U+V)
    (x : sourceFiltration a c η hc θ L.dim U)
    (y : sourceTensorFiltration a c η hc θ M.dim N.dim V) :
    normalizedRightTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN W
      ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,hw.le,x.property,y.property,rfl⟩⟩=
      box (normalizedSymbol a c η hc θ L hL hχL U x)
        (normalizedTensorSymbol a c η hc θ M N hM hN hχM hχN V y) := by
  subst W
  exact normalizedRightTripleSymbol_tmul a c η hc θ L M N hL hM hN hχL hχM hχN U V x y

 theorem tensorSeparationRight_normalized_symbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
    (hN : N.OnSlope c η θ) (W : ℤ)
    (x : sourceTensorFiltration a c η hc θ L.dim (M.dim+N.dim) W) :
    normalizedRightTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      (tensorSeparationRight a c η hc θ L.dim M.dim N.dim
        ((slope_dim c η hc hM).trans (slope_dim c η hc hN).symm) W x)=
      normalizedTensorSymbol a c η hc θ L (.node M N) hL ⟨hM,hN⟩
        (pairSymmetric_of_slope a c η θ hχ L hL)
        (pairSymmetric_of_slope a c η θ hχ (.node M N) ⟨hM,hN⟩) W x := by
  let hMN := (slope_dim c η hc hM).trans (slope_dim c η hc hN).symm
  let χL:=pairSymmetric_of_slope a c η θ hχ L hL
  let χM:=pairSymmetric_of_slope a c η θ hχ M hM
  let χN:=pairSymmetric_of_slope a c η θ hχ N hN
  let χMN:=pairSymmetric_of_slope a c η θ hχ (.node M N) ⟨hM,hN⟩
  let F:=(normalizedRightTripleSymbol a c η hc θ L M N hL hM hN χL χM χN W).comp
    (tensorSeparationRight a c η hc θ L.dim M.dim N.dim hMN W)
  let G:=normalizedTensorSymbol a c η hc θ L (.node M N) hL ⟨hM,hN⟩ χL χMN W
  have he : F=G := by
    apply linearMap_span_ext
    rintro _ ⟨u,v,p,q,huv,hp,hq,rfl⟩
    have hq' := sourceFiltration_antitone a c η hc θ (M.dim+N.dim) (show W-u≤v by omega) hq
    let q0:=separationCoefficientRestricted a c η hc θ M.dim N.dim hMN (W-u) 0 ⟨q,hq'⟩
    have hp0:=normalizedRightTripleSymbol_tmul_eq a c η hc θ L M N hL hM hN χL χM χN
      W u (W-u) (by omega) ⟨p,hp⟩ q0
    change normalizedRightTripleSymbol a c η hc θ L M N hL hM hN χL χM χN W
      ⟨p⊗ₜ[ℚ]q0.val,_⟩=G ⟨p⊗ₜ[ℚ]q,_⟩
    rw [hp0]
    have hq1:=coproduct_normalized_symbol a c η hc θ hχ M N hM hN (W-u) ⟨q,hq'⟩
    have hp2:=normalizedTensorSymbol_tmul_eq a c η hc θ L (.node M N) hL ⟨hM,hN⟩ χL χMN
      W u (W-u) (by omega) ⟨p,hp⟩ ⟨q,hq'⟩
    change box (normalizedSymbol a c η hc θ L hL χL u ⟨p,hp⟩)
      (normalizedTensorSymbol a c η hc θ M N hM hN χM χN (W-u) q0)=_
    change normalizedTensorSymbol a c η hc θ M N hM hN χM χN (W-u) q0=
      normalizedSymbol a c η hc θ (.node M N) ⟨hM,hN⟩ χMN (W-u) ⟨q,hq'⟩ at hq1
    rw [hq1]
    exact hp2.symm
  exact LinearMap.congr_fun he x

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
