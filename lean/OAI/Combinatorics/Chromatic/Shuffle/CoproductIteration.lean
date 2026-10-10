import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TensorSymbolSwap
import OAI.Combinatorics.Chromatic.Shuffle.NormalizedTripleSymbol

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection ElementaryPositivity.LinearFiltration
open SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma tensorSeparationLeft_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (W : ℤ) (x : B a (SlopeArithmetic.slope c η) (d+e)⊗[ℚ]B a (SlopeArithmetic.slope c η) f)
    (hx : x∈sourceTensorFiltration a c η hc θ (d+e) f W) :
    TensorProduct.map (separationCoefficient a c η hc hs 0) LinearMap.id x∈
      sourceTripleFiltration a c η hc θ d e f W :=
  tensor_map_mem_filtration (sourceFiltration a c η hc θ (d+e)) (sourceFiltration a c η hc θ f)
    (sourceTensorFiltration a c η hc θ d e) (sourceFiltration a c η hc θ f)
    (separationCoefficient a c η hc hs 0) LinearMap.id
    (fun w=>separationCoefficient_filtration a c η hc θ d e hs w 0) (fun _ _ h=>h) W x hx

noncomputable def tensorSeparationLeft (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ) :
    sourceTensorFiltration a c η hc θ (d+e) f W →ₗ[ℚ]
      sourceTripleFiltration a c η hc θ d e f W :=
  let C : B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e :=
    separationCoefficient a c η hc hs 0
  let F : (B a (SlopeArithmetic.slope c η) (d+e)⊗[ℚ]B a (SlopeArithmetic.slope c η) f) →ₗ[ℚ]
      ((B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)⊗[ℚ]
        B a (SlopeArithmetic.slope c η) f) := TensorProduct.map C LinearMap.id
  (F.comp (sourceTensorFiltration a c η hc θ (d+e) f W).subtype).codRestrict
    (sourceTripleFiltration a c η hc θ d e f W)
    (fun x=>tensorSeparationLeft_filtration a c η hc θ d e f hs W x.val x.property)

namespace SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus

lemma normalizedTripleSymbol_tmul_eq (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a)
    (W U V : ℤ) (hw : W=U+V)
    (x : sourceTensorFiltration a c η hc θ L.dim M.dim U)
    (y : sourceFiltration a c η hc θ N.dim V) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN W
      ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,hw.le,x.property,y.property,rfl⟩⟩=
      box (normalizedTensorSymbol a c η hc θ L M hL hM hχL hχM U x)
        (normalizedSymbol a c η hc θ N hN hχN V y) := by
  subst W
  exact normalizedTripleSymbol_tmul a c η hc θ L M N hL hM hN hχL hχM hχN U V x y

theorem tensorSeparationLeft_normalized_symbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
    (hN : N.OnSlope c η θ) (W : ℤ)
    (x : sourceTensorFiltration a c η hc θ (L.dim+M.dim) N.dim W) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      (tensorSeparationLeft a c η hc θ L.dim M.dim N.dim
        ((slope_dim c η hc hL).trans (slope_dim c η hc hM).symm) W x)=
      normalizedTensorSymbol a c η hc θ (.node L M) N ⟨hL,hM⟩ hN
        (pairSymmetric_of_slope a c η θ hχ (.node L M) ⟨hL,hM⟩)
        (pairSymmetric_of_slope a c η θ hχ N hN) W x := by
  let hLM := (slope_dim c η hc hL).trans (slope_dim c η hc hM).symm
  let χL:=pairSymmetric_of_slope a c η θ hχ L hL
  let χM:=pairSymmetric_of_slope a c η θ hχ M hM
  let χN:=pairSymmetric_of_slope a c η θ hχ N hN
  let χLM:=pairSymmetric_of_slope a c η θ hχ (.node L M) ⟨hL,hM⟩
  let F:=(normalizedTripleSymbol a c η hc θ L M N hL hM hN χL χM χN W).comp
    (tensorSeparationLeft a c η hc θ L.dim M.dim N.dim hLM W)
  let G:=normalizedTensorSymbol a c η hc θ (.node L M) N ⟨hL,hM⟩ hN χLM χN W
  have he : F=G := by
    apply linearMap_span_ext
    rintro _ ⟨u,v,p,q,huv,hp,hq,rfl⟩
    have hq' := sourceFiltration_antitone a c η hc θ N.dim (show W-u≤v by omega) hq
    let p0:=separationCoefficientRestricted a c η hc θ L.dim M.dim hLM u 0 ⟨p,hp⟩
    have hp0:=normalizedTripleSymbol_tmul_eq a c η hc θ L M N hL hM hN χL χM χN
      W u (W-u) (by omega) p0 ⟨q,hq'⟩
    change normalizedTripleSymbol a c η hc θ L M N hL hM hN χL χM χN W
      ⟨p0.val⊗ₜ[ℚ]q,_⟩=G ⟨p⊗ₜ[ℚ]q,_⟩
    rw [hp0]
    have hp1:=coproduct_normalized_symbol a c η hc θ hχ L M hL hM u ⟨p,hp⟩
    have hp2:=normalizedTensorSymbol_tmul_eq a c η hc θ (.node L M) N ⟨hL,hM⟩ hN χLM χN
      W u (W-u) (by omega) ⟨p,hp⟩ ⟨q,hq'⟩
    change box (normalizedTensorSymbol a c η hc θ L M hL hM χL χM u p0)
      (normalizedSymbol a c η hc θ N hN χN (W-u) ⟨q,hq'⟩)=_
    change normalizedTensorSymbol a c η hc θ L M hL hM χL χM u p0=
      normalizedSymbol a c η hc θ (.node L M) ⟨hL,hM⟩ χLM u ⟨p,hp⟩ at hp1
    rw [hp1]
    exact hp2.symm
  exact LinearMap.congr_fun he x

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
