import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TripleSymbols

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def tripleClearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ)
    (f : sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W) :
    MvPolynomial ((L.node M).node N).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)) :=
  Classical.choose (refinedTripleLeadingPolynomial_denominator_divisible a c η hc θ L M N hL hM hN hχL hχM hχN W f.val f.property)

lemma denominator_tripleClearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ)
    (f : sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)))
      (tripleInternalDenominator a L M N)*tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN W f=
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) ((L.node M).node N) W)
        (refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN f.val) :=
  (Classical.choose_spec (refinedTripleLeadingPolynomial_denominator_divisible a c η hc θ L M N hL hM hN hχL hχM hχN W f.val f.property)).symm

noncomputable def tripleClearedLeadingMap (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ) :
    sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W →ₗ[ℚ]
      MvPolynomial ((L.node M).node N).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)) :=
  { toFun := tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN W
    map_add' := by
      intro f g
      apply scalar_mul_injective _ (tripleInternalDenominator_ne_zero a L M N)
      dsimp only
      rw [mul_add,denominator_tripleClearedLeading,denominator_tripleClearedLeading,denominator_tripleClearedLeading]
      simp only [Submodule.coe_add,LinearMap.map_add]
    map_smul' := by
      intro r f
      apply scalar_mul_injective _ (tripleInternalDenominator_ne_zero a L M N)
      dsimp only
      rw [mul_smul_comm,denominator_tripleClearedLeading,denominator_tripleClearedLeading]
      simp only [Submodule.coe_smul,LinearMap.map_smul,RingHom.id_apply] }

noncomputable def normalizedTripleSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ) :
    sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W →ₗ[ℚ]
      MvPolynomial ((L.node M).node N).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)) :=
  (LinearMap.mulLeft ℚ (map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)))
    (tripleInternalNumerator a L M N))).comp (tripleClearedLeadingMap a c η hc θ L M N hL hM hN hχL hχM hχN W)

lemma normalizedTripleSymbol_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (U V : ℤ)
    (x : sourceTensorFiltration a c η hc θ L.dim M.dim U)
    (y : sourceFiltration a c η hc θ N.dim V) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN (U+V)
      ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,le_refl _,x.property,y.property,rfl⟩⟩=
      box (normalizedTensorSymbol a c η hc θ L M hL hM hχL hχM U x)
        (normalizedSymbol a c η hc θ N hN hχN V y) := by
  let xy : sourceTripleFiltration a c η hc θ L.dim M.dim N.dim (U+V) :=
    ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,le_refl _,x.property,y.property,rfl⟩⟩
  have h : tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN (U+V) xy=
      box (tensorClearedLeading a c η hc θ L M hL hM hχL hχM U x) (clearedLeading a c η hc θ N hN hχN V y) := by
    apply scalar_mul_injective _ (tripleInternalDenominator_ne_zero a L M N)
    dsimp only
    rw [denominator_tripleClearedLeading]
    change mapLinear _ (refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN (x.val⊗ₜ[ℚ]y.val))=_
    rw [refinedTripleLeadingPolynomial_tmul a c η hc θ L M N hL hM hN U V x.val y.val x.property y.property,
      ←denominator_tensorClearedLeading a c η hc θ L M hL hM hχL hχM U x,
      ←denominator_clearedLeading a c η hc θ N hN hχN V y,box_scalar_left]
    rfl
  change map _ (tripleInternalNumerator a L M N)*tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN (U+V) xy=
    box (map _ (internalNumerator a L M)*tensorClearedLeading a c η hc θ L M hL hM hχL hχM U x)
      (map _ (centerNumerator a N N.centerPairs)*clearedLeading a c η hc θ N hN hχN V y)
  rw [h,box_scalar_left]
  rfl

lemma normalizedTripleSymbol_eq_zero_iff (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ)
    (f : sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN W f=0 ↔
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) ((L.node M).node N) W)
        (refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN f.val)=0 := by
  change map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)))
    (tripleInternalNumerator a L M N)*tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN W f=0 ↔ _
  rw [SymbolCoordinates.scalar_mul_eq_zero_iff _ (tripleInternalNumerator_ne_zero a L M N)]
  rw [←denominator_tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN W f,
    SymbolCoordinates.scalar_mul_eq_zero_iff _ (tripleInternalDenominator_ne_zero a L M N)]

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma degreeCut_node_tmul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (L R : SplitTree I) (U V : ℤ)
    (x : tensor (quotientFamily a μ) L) (y : tensor (quotientFamily a μ) R)
    (hx : x∈degreeCutSubmodule a μ L U) (hy : y∈degreeCutSubmodule a μ R V) :
    x⊗ₜ[ℚ]y∈degreeCutSubmodule a μ (.node L R) (U+V) := by
  rintro ⟨k,l⟩ hkl
  change componentTensor a μ L k x⊗ₜ[ℚ]componentTensor a μ R l y=0
  change 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)<U+V at hkl
  by_cases hk : 2*L.totalDegree k+L.doubleShift a<U
  · rw [hx k hk,TensorProduct.zero_tmul]
  · rw [hy l (by omega),TensorProduct.tmul_zero]

lemma refinedTripleCenterPolynomial_coeff_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ) (W : ℤ)
    (x : (B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) M.dim)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) N.dim)
    (hx : x∈sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W)
    (z : ((L.node M).node N).Centers →₀ ℕ) :
    (refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN x).coeff z∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) ((L.node M).node N) W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨U,V,x,y,hUV,hx,hy,rfl⟩:=hx
    have hy' := sourceFiltration_antitone a c η hc θ N.dim (show W-U≤V by omega) hy
    rw [refinedTripleCenterPolynomial_tmul,←Finsupp.comapDomain_sumElim_comapDomain z,coeff_box]
    have he : W=U+(W-U) := by omega
    rw [he]
    exact degreeCut_node_tmul a _ (.node L M) N U (W-U) _ _
      (refinedCenterPolynomial_coeff_degreeCut a c η hc θ L M hL hM U x hx _)
      (centeredRestrictionB_coeff_degreeCut a c η hc θ N hN (W-U) y hy' _)
  | zero =>
    rw [LinearMap.map_zero,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
    exact (degreeCutSubmodule a (SlopeArithmetic.slope c η) ((L.node M).node N) W).zero_mem
  | add x y hx hy ihx ihy =>
    rw [LinearMap.map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply]
    exact (degreeCutSubmodule a (SlopeArithmetic.slope c η) ((L.node M).node N) W).add_mem ihx ihy
  | smul r x hx ih =>
    rw [LinearMap.map_smul,coeff_smul]
    exact (degreeCutSubmodule a (SlopeArithmetic.slope c η) ((L.node M).node N) W).smul_mem r ih

lemma normalizedTripleSymbol_next_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ)
    (x : sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W)
    (hx : x.val∈sourceTripleFiltration a c η hc θ L.dim M.dim N.dim (W+1)) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN W x=0 := by
  rw [normalizedTripleSymbol_eq_zero_iff]
  ext z
  rw [coeff_mapLinear,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  apply degreeCut_weightComponent_zero
  exact refinedTripleCenterPolynomial_coeff_degreeCut a c η hc θ L M N hL hM hN (W+1) x.val hx z

theorem normalizedTripleSymbol_detect (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e f : I → ℕ) (W : ℤ) (x : sourceTripleFiltration a c η hc θ d e f W)
    (h : ∀ (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
      (hN : N.OnSlope c η θ) (hd : L.dim=d) (he : M.dim=e) (hf : N.dim=f),
      normalizedTripleSymbol a c η hc θ L M N hL hM hN
        (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
        (pairSymmetric_of_slope a c η θ hχ N hN) W (hd ▸ he ▸ hf ▸ x)=0) :
    x.val∈sourceTripleFiltration a c η hc θ d e f (W+1) := by
  apply triple_leading_restrictions_detect a c η hc θ d e f W x.val x.property
  rintro ⟨L,hoL,hL,hd,k,z⟩ ⟨M,hoM,hM,he,l,w⟩ ⟨N,hoN,hN,hf,m,t⟩ hw
  subst d
  subst e
  subst f
  have hp := (normalizedTripleSymbol_eq_zero_iff a c η hc θ L M N hL hM hN _ _ _ W x).mp
    (h L M N hL hM hN rfl rfl rfl)
  have ht := congrArg (fun p=>componentTensor a (SlopeArithmetic.slope c η) ((L.node M).node N) ((k,l),m)
    (AddMonoidAlgebra.coeff p ((z.sumElim w).sumElim t))) hp
  have heq : 2*((L.totalDegree k+M.totalDegree l)+N.totalDegree m)+
      ((L.doubleShift a+M.doubleShift a)+N.doubleShift a)=W := by
    change (2*L.totalDegree k+L.doubleShift a)+(2*M.totalDegree l+M.doubleShift a)+
      (2*N.totalDegree m+N.doubleShift a)=W at hw
    omega
  rw [coeff_mapLinear,componentTensor_weightComponent,ite_eq_left heq,
    AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,LinearMap.map_zero,
    refinedTripleCenterPolynomial_coeff_test] at ht
  exact ht

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
