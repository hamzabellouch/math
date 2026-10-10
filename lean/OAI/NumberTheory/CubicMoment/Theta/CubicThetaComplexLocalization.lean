import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalLocalRellich

namespace OAI

/-! The compact chart inclusion also respects the complex scalar action.
The extension is identified on the dense genuine smooth sections. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

local instance complexLocalization_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance complexLocalization_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩
local instance complexLocalization_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

variable {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
  (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})

include hφ hc hp in
private theorem valueMemLp (F : cubicThetaSmoothTests) :
    MemLp (cubicThetaTestLocalization φ F ∘ cubicThetaTangentCoordinates) 2
      LocalSobolev.tangentBorelVolume :=
  LocalSobolev.tangentFunction_memLp (cubicThetaTestLocalization φ F)
    ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
    (cubicThetaTestLocalization_compact hc F)

def cubicThetaLocalValue : cubicThetaSmoothTests →ₗ[ℂ] LocalSobolev.TangentComplexL2 where
  toFun F := (valueMemLp hφ hc hp F).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(valueMemLp hφ hc hp (F+G)).coeFn_toLp,
      (valueMemLp hφ hc hp F).coeFn_toLp,(valueMemLp hφ hc hp G).coeFn_toLp,
      Lp.coeFn_add ((valueMemLp hφ hc hp F).toLp _) ((valueMemLp hφ hc hp G).toLp _)]
      with u hFG hF hG ha
    simp only [Pi.add_apply] at ha
    rw [hFG,ha,hF,hG]
    change cubicThetaTestLocalization φ ((F+G : cubicThetaSmoothTests) : CubicThetaSection) _=_
    rw [cubicThetaTestLocalization_add]
    rfl
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(valueMemLp hφ hc hp (c • F)).coeFn_toLp,
      (valueMemLp hφ hc hp F).coeFn_toLp,
      Lp.coeFn_smul c ((valueMemLp hφ hc hp F).toLp _)] with u hCF hF hs
    simp only [Pi.smul_apply,RingHom.id_apply] at hs ⊢
    rw [hCF,hs,hF]
    change cubicThetaTestLocalization φ ((c • F : cubicThetaSmoothTests) : CubicThetaSection) _=_
    rw [cubicThetaTestLocalization_smul]
    rfl

lemma cubicThetaLocalValue_apply (F : cubicThetaSmoothTests) :
    cubicThetaLocalValue hφ hc hp F=
      LocalSobolev.tangentFunctionL2 (cubicThetaTestLocalization φ F)
        ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
        (cubicThetaTestLocalization_compact hc F) := rfl

variable (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
  (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
  {S : Set CubicThetaPoint} (hS : IsCompact S) (hSe : S⊆e.source)
  (hsupp : tsupport φ⊆cubicThetaPointCoordinates '' S)

include e he hS hSe hsupp in
lemma cubicThetaLocalValue_bound : ∃ C, ∀ F : cubicThetaSmoothTests,
    ‖cubicThetaLocalValue hφ hc hp F‖≤C*‖cubicThetaGlobalEnergyTestLinear F‖ := by
  refine ⟨‖cubicThetaGlobalLocalInclusion hφ hc hp‖,fun F => ?_⟩
  rw [cubicThetaLocalValue_apply,← cubicThetaGlobalLocalInclusion_test hφ hc hp e he hS hSe hsupp F]
  exact (cubicThetaGlobalLocalInclusion hφ hc hp).le_opNorm (cubicThetaGlobalEnergyTest F)

def cubicThetaComplexLocalInclusion : cubicThetaGlobalEnergySpace →L[ℂ] LocalSobolev.TangentComplexL2 :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=↥cubicThetaSmoothTests) (Eₗ:=↥cubicThetaGlobalEnergySpace)
    (F:=LocalSobolev.TangentComplexL2)
    (cubicThetaLocalValue hφ hc hp) cubicThetaGlobalEnergyTestLinear

include e he hS hSe hsupp in
lemma cubicThetaComplexLocalInclusion_test (F : cubicThetaSmoothTests) :
    cubicThetaComplexLocalInclusion hφ hc hp (cubicThetaGlobalEnergyTest F)=
      cubicThetaLocalValue hφ hc hp F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaLocalValue hφ hc hp) (e:=cubicThetaGlobalEnergyTestLinear)
    cubicThetaGlobalEnergyTestLinear_dense (cubicThetaLocalValue_bound hφ hc hp e he hS hSe hsupp) F

include e he hS hSe hsupp in
theorem cubicThetaComplexLocalInclusion_eq :
    (cubicThetaComplexLocalInclusion hφ hc hp : cubicThetaGlobalEnergySpace → LocalSobolev.TangentComplexL2)=
      cubicThetaGlobalLocalInclusion hφ hc hp := by
  apply cubicThetaGlobalEnergyTestLinear_dense.equalizer
    (cubicThetaComplexLocalInclusion hφ hc hp).continuous
    (cubicThetaGlobalLocalInclusion hφ hc hp).continuous
  funext F
  change cubicThetaComplexLocalInclusion hφ hc hp (cubicThetaGlobalEnergyTest F)=
    cubicThetaGlobalLocalInclusion hφ hc hp (cubicThetaGlobalEnergyTest F)
  rw [cubicThetaComplexLocalInclusion_test hφ hc hp e he hS hSe hsupp,
    cubicThetaGlobalLocalInclusion_test hφ hc hp e he hS hSe hsupp,cubicThetaLocalValue_apply]

include e he hS hSe hsupp in
theorem cubicThetaComplexLocalInclusion_compact :
    IsCompactOperator (cubicThetaComplexLocalInclusion hφ hc hp) := by
  rw [cubicThetaComplexLocalInclusion_eq hφ hc hp e he hS hSe hsupp]
  exact cubicThetaGlobalLocalInclusion_compact hφ hc hp

end CubicFirstMoment

end

end OAI
