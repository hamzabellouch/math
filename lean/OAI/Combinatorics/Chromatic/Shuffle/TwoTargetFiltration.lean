import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TensorColumnNaturality
import OAI.Combinatorics.Chromatic.Walls.ShuffleFiltration

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def twoTargetTransferB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
    (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂) :
    (B a (slope c η) d₁⊗[ℚ]B a (slope c η) e₁)⊗[ℚ]
      (B a (slope c η) d₂⊗[ℚ]B a (slope c η) e₂) →ₗ[ℚ]
    B a (slope c η) (d₁+e₁)⊗[ℚ]B a (slope c η) (d₂+e₂) :=
  TensorProduct.map (shuffleTensorBUnit a c η hc d₁ e₁ h₁)
    (shuffleTensorBUnit a c η hc d₂ e₂ h₂)

lemma twoTargetTransferB_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd₁ : OnSlopeOrZero c η θ d₁) (he₁ : OnSlopeOrZero c η θ e₁)
    (hd₂ : OnSlopeOrZero c η θ d₂) (he₂ : OnSlopeOrZero c η θ e₂)
    (W : ℤ) (x : (B a (slope c η) d₁⊗[ℚ]B a (slope c η) e₁)⊗[ℚ]
      (B a (slope c η) d₂⊗[ℚ]B a (slope c η) e₂))
    (hx : x∈fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ W) :
    twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ (hd₁.compatible he₁) (hd₂.compatible he₂) x∈
      unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) W := by
  let F:=unitalSourceFiltration a c η hc θ
  exact tensor_map_mem_filtration _ _ (F (d₁+e₁)) (F (d₂+e₂))
    (shuffleTensorBUnit a c η hc d₁ e₁ (hd₁.compatible he₁))
    (shuffleTensorBUnit a c η hc d₂ e₂ (hd₂.compatible he₂))
    (lift_mem_filtration _ _ _ (unitalSourceFiltration_antitone a c η hc θ (d₁+e₁)) _
      (shuffleBUnit_filtered a c η hc θ hχ d₁ e₁ hd₁ he₁))
    (lift_mem_filtration _ _ _ (unitalSourceFiltration_antitone a c η hc θ (d₂+e₂)) _
      (shuffleBUnit_filtered a c η hc θ hχ d₂ e₂ hd₂ he₂)) W x hx

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule
attribute [local instance] braidFourTensor braidFourTensorAlg braidFourRing braidFourAlg
attribute [local instance] braidFourTensorN braidFourTensorM braidFourN braidFourM

lemma quotient_twoTargetSeries (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
    (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂)
    (F : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) :
    mapRing (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)).toRingHom
      (mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) F)=
    mapLinear (twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ h₁ h₂)
      (mapRing (fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toRingHom F) := by
  apply HahnSeries.ext
  funext j
  exact quotient_twoTargetTransfer_unit a c η hc d₁ e₁ d₂ e₂ h₁ h₂ (F.coeff j)

lemma clearedSeparationB_cell (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
    (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    clearedSeparationB a (slope c η) (d₁+e₁) (d₂+e₂)
      (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
    ((-1 : ℚ)^eulerForm a d₂ e₁) •
      mapLinear (twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ h₁ h₂)
        (fourInputSeriesB a c η hc d₁ e₁ d₂ e₂ hd he
          (quotientAlg a (slope c η) (d₁+d₂) f) (quotientAlg a (slope c η) (e₁+e₂) g)) := by
  rw [clearedSeparationB_mk,cellTransfer_normalized,mapRing_rat_smul,
    quotient_twoTargetSeries a c η hc d₁ e₁ d₂ e₂ h₁ h₂,
    fourInputSeriesB_mk a c η hc d₁ e₁ d₂ e₂ hd he]

lemma clearedSeparationB_cell_constant_next (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd₁ : OnSlopeOrZero c η θ d₁) (he₁ : OnSlopeOrZero c η θ e₁)
    (hd₂ : OnSlopeOrZero c η θ d₂) (he₂ : OnSlopeOrZero c η θ e₂)
    (U V : ℤ) (f : S (d₁+d₂)) (g : S (e₁+e₂))
    (hf : quotientAlg a (slope c η) (d₁+d₂) f∈unitalSourceFiltration a c η hc θ (d₁+d₂) U)
    (hg : quotientAlg a (slope c η) (e₁+e₂) g∈unitalSourceFiltration a c η hc θ (e₁+e₂) V) :
    (clearedSeparationB a (slope c η) (d₁+e₁) (d₂+e₂)
      (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))).coeff 0-
    ((-1 : ℚ)^eulerForm a d₂ e₁) •
      twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ (hd₁.compatible he₁) (hd₂.compatible he₂)
        (fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂
          ((unitalSeparationSeries a c η hc (hd₁.compatible hd₂)
              (quotientAlg a (slope c η) (d₁+d₂) f)).coeff 0⊗ₜ[ℚ]
           (unitalSeparationSeries a c η hc (he₁.compatible he₂)
              (quotientAlg a (slope c η) (e₁+e₂) g)).coeff 0))∈
      unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V+1) := by
  rw [clearedSeparationB_cell a c η hc d₁ e₁ d₂ e₂
    (hd₁.compatible hd₂) (he₁.compatible he₂) (hd₁.compatible he₁) (hd₂.compatible he₂)]
  simp only [coeff_smul,mapLinear_coeff]
  rw [←smul_sub,←LinearMap.map_sub]
  apply Submodule.smul_mem
  exact twoTargetTransferB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂ hd₁ he₁ hd₂ he₂ (U+V+1) _
    (fourInputSeriesB_constant_next a c η hc θ hχ d₁ e₁ d₂ e₂
      (hd₁.compatible hd₂) (he₁.compatible he₂) U V _ _ hf hg)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open ElementaryPositivity.PackConvolution HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearBTensorB clearBTensorBA Classical.propDecidable

noncomputable def clearedConstantB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    B a μ d⊗[ℚ]B a μ e →ₗ[ℚ] B a μ d⊗[ℚ]B a μ e :=
  (coeff.linearMap (R:=ℚ) 0).comp (clearedSeparationB a μ d e)

lemma clearedConstantB_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : B a μ d⊗[ℚ]B a μ e) :
    clearedConstantB a μ d e x=(clearedSeparationB a μ d e x).coeff 0 := rfl

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
lemma unitalSeparationConstant_shuffle_grid (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e α β : I → ℕ} (h : d+e=α+β)
    (hs : α=0 ∨ β=0 ∨ slope c η α=slope c η β)
    (f : S d) (g : S e) {s : Pack (A:=A)} (R : Realization (α+β) s) :
    (unitalSeparationSeries a c η hc hs
      (quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g)))).coeff 0=
    clearedConstantB a (slope c η) α β
      (quotientTensor a (slope c η) α β
        (gridTensor a f g (cutRealizationEquiv R (firstCut α β)).val
          (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β)))) := by
  exact congrArg (fun F=>F.coeff 0) (unitalSeparationSeries_shuffle_grid a c η hc h hs f g R)

omit [∀ i, Fintype (A i)] in
lemma clearedConstantB_grid_sameSlope_support (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) {d e α β : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=A)} (p : ElementaryPositivity.PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (ht : slope c η α=slope c η β) (hs : slope c η d=slope c η α) :
    clearedConstantB a (slope c η) α β (quotientTensor a (slope c η) α β (gridTensor a f g p R T))=
    ∑ u : CutShape (left p),∑ v : CutShape (right p),
      if CellsOnSlope c η (slope c η α)
        (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)
      then clearedConstantB a (slope c η) α β
        (quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v)) else 0 := by
  classical
  rw [quotient_gridTensor_sameSlope_support a c η hc f g p R T ht hs]
  simp only [map_sum,apply_ite,(clearedConstantB a (slope c η) α β).map_zero]

end ElementaryPositivity.RawShuffle

end

end OAI
