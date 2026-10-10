import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalLocalizationBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalRellichValue

namespace OAI

/-! Compact localization of the completed global automorphic energy
space in an actual injective compact chart. -/
noncomputable section
open Set MeasureTheory Topology
open scoped ContDiff
namespace CubicFirstMoment

local instance globalLocalRellich_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaGlobalEnergyTestLinear : cubicThetaSmoothTests →ₗ[ℂ] cubicThetaGlobalEnergySpace :=
  cubicThetaGlobalEnergyGraph.codRestrict cubicThetaGlobalEnergySpace
    (fun F => Submodule.le_topologicalClosure cubicThetaGlobalEnergyGraph.range ⟨F,rfl⟩)

lemma cubicThetaGlobalEnergyTestLinear_dense : DenseRange cubicThetaGlobalEnergyTestLinear := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range cubicThetaGlobalEnergyTestLinear=
      Set.range cubicThetaGlobalEnergyGraph := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨cubicThetaGlobalEnergyTestLinear F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

variable {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
  (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
  (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
  (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
  {S : Set CubicThetaPoint} (hS : IsCompact S) (hSe : S⊆e.source)
  (hsupp : tsupport φ⊆cubicThetaPointCoordinates '' S)

def cubicThetaLocalEnergyTestLinear : cubicThetaSmoothTests →ₗ[ℂ]
    cubicThetaLocalEnergySpace hφ hc hp :=
  (cubicThetaLocalEnergyGraph hφ hc hp).codRestrict (cubicThetaLocalEnergySpace hφ hc hp)
    (fun F => Submodule.le_topologicalClosure (cubicThetaLocalEnergyGraph hφ hc hp).range ⟨F,rfl⟩)

include e he hS hSe hsupp in
lemma cubicThetaGlobalToLocal_bound : ∃ C, ∀ F : cubicThetaSmoothTests,
    ‖cubicThetaLocalEnergyTestLinear hφ hc hp F‖≤C*‖cubicThetaGlobalEnergyTestLinear F‖ := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaGlobalLocalization_bound hφ hc hp e he hS hSe hsupp
  refine ⟨Real.sqrt C,fun F => ?_⟩
  have hs : ‖cubicThetaLocalEnergyTestLinear hφ hc hp F‖^2≤
      C*‖cubicThetaGlobalEnergyTestLinear F‖^2 := hbound F
  have hsqrt : (Real.sqrt C*‖cubicThetaGlobalEnergyTestLinear F‖)^2=
      C*‖cubicThetaGlobalEnergyTestLinear F‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  exact _root_.le_of_sq_le_sq (hs.trans_eq hsqrt.symm)
    (mul_nonneg (Real.sqrt_nonneg C) (_root_.norm_nonneg _))

def cubicThetaGlobalToLocalEnergy : cubicThetaGlobalEnergySpace →L[ℂ]
    cubicThetaLocalEnergySpace hφ hc hp :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=↥cubicThetaSmoothTests) (Eₗ:=↥cubicThetaGlobalEnergySpace)
    (F:=↥(cubicThetaLocalEnergySpace hφ hc hp))
    (cubicThetaLocalEnergyTestLinear hφ hc hp) cubicThetaGlobalEnergyTestLinear

include e he hS hSe hsupp in
lemma cubicThetaGlobalToLocalEnergy_test (F : cubicThetaSmoothTests) :
    cubicThetaGlobalToLocalEnergy hφ hc hp (cubicThetaGlobalEnergyTest F)=
      LocalSobolev.localEnergyTest hφ hc hp F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=↥cubicThetaSmoothTests) (Eₗ:=↥cubicThetaGlobalEnergySpace)
    (F:=↥(cubicThetaLocalEnergySpace hφ hc hp))
    (f:=cubicThetaLocalEnergyTestLinear hφ hc hp) (e:=cubicThetaGlobalEnergyTestLinear)
    cubicThetaGlobalEnergyTestLinear_dense
    (cubicThetaGlobalToLocal_bound hφ hc hp e he hS hSe hsupp) F

def cubicThetaGlobalLocalInclusion : cubicThetaGlobalEnergySpace →L[ℝ] LocalSobolev.TangentComplexL2 :=
  (LocalSobolev.localEnergyInclusion hφ hc hp).comp
    ((cubicThetaGlobalToLocalEnergy hφ hc hp).restrictScalars ℝ)

theorem cubicThetaGlobalLocalInclusion_compact :
    IsCompactOperator (cubicThetaGlobalLocalInclusion hφ hc hp) :=
  (LocalSobolev.localEnergyInclusion_compact hφ hc hp).comp_clm
    ((cubicThetaGlobalToLocalEnergy hφ hc hp).restrictScalars ℝ)

include e he hS hSe hsupp in
theorem cubicThetaGlobalLocalInclusion_test (F : cubicThetaSmoothTests) :
    cubicThetaGlobalLocalInclusion hφ hc hp (cubicThetaGlobalEnergyTest F)=
      LocalSobolev.tangentFunctionL2 (cubicThetaTestLocalization φ F)
        ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
        (cubicThetaTestLocalization_compact hc F) := by
  change LocalSobolev.localEnergyInclusion hφ hc hp
    (cubicThetaGlobalToLocalEnergy hφ hc hp (cubicThetaGlobalEnergyTest F))=_
  rw [cubicThetaGlobalToLocalEnergy_test hφ hc hp e he hS hSe hsupp]
  exact LocalSobolev.localEnergyInclusion_test hφ hc hp F

end CubicFirstMoment

end

end OAI
