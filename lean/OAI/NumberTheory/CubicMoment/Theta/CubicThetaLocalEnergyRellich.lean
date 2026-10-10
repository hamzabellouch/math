import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalizationLinear
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! Rellich compactness on the completion of the actual local energy
graph. No independent value and derivative data are introduced. -/
noncomputable section
open Set MeasureTheory Topology
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance energyRellich_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance energyRellich_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

local instance energyRellich_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

lemma supported_closed (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    IsClosed (h1On (cubicThetaTangentCoordinates ⁻¹' K)
      (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable) :
        Set (h1 (E:=CubicThetaTangent) (μ:=(volume : Measure CubicThetaTangent)))) := by
  exact (isClosed_range_extendByZero _ _).preimage
    (h1ToL2 (μ:=(volume : Measure CubicThetaTangent))).continuous

instance supported_complete (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    CompleteSpace (Supported K hK) := (supported_closed K hK).isComplete.completeSpace_coe

local instance energyRellich_supportedBounded (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    IsBoundedSMul ℝ (Supported K hK) where
  dist_smul_pair' c u v := by
    change dist (c • (u.val.val : H1Target (μ:=tangentBorelVolume)))
        (c • (v.val.val : H1Target (μ:=tangentBorelVolume)))≤
      dist c 0*dist (u.val.val : H1Target (μ:=tangentBorelVolume)) v.val.val
    exact dist_smul_pair c _ _
  dist_pair_smul' c d u := by
    change dist (c • (u.val.val : H1Target (μ:=tangentBorelVolume)))
        (d • (u.val.val : H1Target (μ:=tangentBorelVolume)))≤
      dist c d*dist (u.val.val : H1Target (μ:=tangentBorelVolume)) 0
    exact dist_pair_smul c d _

local instance energyRellich_pairBounded (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    IsBoundedSMul ℝ (Supported K hK × Supported K hK) where
  dist_smul_pair' c u v := by
    let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
      (u.1.val.val,u.2.val.val)
    let v₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
      (v.1.val.val,v.2.val.val)
    change dist (c • u₀) (c • v₀)≤dist c 0*dist u₀ v₀
    exact dist_smul_pair c u₀ v₀
  dist_pair_smul' c d u := by
    let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
      (u.1.val.val,u.2.val.val)
    change dist (c • u₀) (d • u₀)≤dist c d*dist u₀ 0
    exact dist_pair_smul c d u₀

variable {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
  (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})

def localEnergyTest : cubicThetaSmoothTests →ₗ[ℝ] cubicThetaLocalEnergySpace hφ hc hp :=
  ((cubicThetaLocalEnergyGraph hφ hc hp).restrictScalars ℝ).codRestrict
    ((cubicThetaLocalEnergySpace hφ hc hp).restrictScalars ℝ)
    (fun F => Submodule.le_topologicalClosure (cubicThetaLocalEnergyGraph hφ hc hp).range ⟨F,rfl⟩)

lemma localEnergyTest_norm (F : cubicThetaSmoothTests) :
    ‖localEnergyTest hφ hc hp F‖=‖cubicThetaLocalEnergyGraph hφ hc hp F‖ := rfl

lemma localEnergyTest_dense : DenseRange (localEnergyTest hφ hc hp) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range (localEnergyTest hφ hc hp)=
      Set.range (cubicThetaLocalEnergyGraph hφ hc hp) := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨localEnergyTest hφ hc hp F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

lemma localizedSupportedPair_bound : ∃ C, ∀ F : cubicThetaSmoothTests,
    ‖localizedSupportedPair hφ hc hp F‖≤C*‖localEnergyTest hφ hc hp F‖ := by
  obtain ⟨C,hC,hbound⟩ := localizedPair_bound hφ hc hp
  refine ⟨Real.sqrt C,fun F => ?_⟩
  have hs : ‖localizedSupportedPair hφ hc hp F‖^2≤C*‖localEnergyTest hφ hc hp F‖^2 := by
    rw [localizedSupportedPair_norm hφ hc hp F,localEnergyTest_norm hφ hc hp F]
    exact hbound F
  have he : (Real.sqrt C*‖localEnergyTest hφ hc hp F‖)^2=
      C*‖localEnergyTest hφ hc hp F‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  exact _root_.le_of_sq_le_sq (hs.trans_eq he.symm)
    (mul_nonneg (Real.sqrt_nonneg C) (_root_.norm_nonneg (localEnergyTest hφ hc hp F)))

def localEnergyToSupported : cubicThetaLocalEnergySpace hφ hc hp →L[ℝ]
    (Supported (tsupport φ) hc × Supported (tsupport φ) hc) :=
  @LinearMap.extendOfNorm ℝ ℝ (↥cubicThetaSmoothTests)
    (↥(cubicThetaLocalEnergySpace hφ hc hp))
    (↥(Supported (tsupport φ) hc) × ↥(Supported (tsupport φ) hc))
    inferInstance inferInstance (RingHom.id ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (by
      constructor
      · intro c u v
        let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (u.1.val.val,u.2.val.val)
        let v₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (v.1.val.val,v.2.val.val)
        change dist (c • u₀) (c • v₀)≤dist c 0*dist u₀ v₀
        exact dist_smul_pair c u₀ v₀
      · intro c d u
        let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (u.1.val.val,u.2.val.val)
        change dist (c • u₀) (d • u₀)≤dist c d*dist u₀ 0
        exact dist_pair_smul c d u₀) inferInstance inferInstance
    (@CompleteSpace.prod (Supported (tsupport φ) hc) (Supported (tsupport φ) hc)
      _ _ (supported_complete (tsupport φ) hc) (supported_complete (tsupport φ) hc))
    (localizedSupportedPair hφ hc hp) (localEnergyTest hφ hc hp)

lemma localEnergyToSupported_test (F : cubicThetaSmoothTests) :
    localEnergyToSupported hφ hc hp (localEnergyTest hφ hc hp F)=
      localizedSupportedPair hφ hc hp F :=
  @LinearMap.extendOfNorm_eq ℝ ℝ (↥cubicThetaSmoothTests)
    (↥(cubicThetaLocalEnergySpace hφ hc hp))
    (↥(Supported (tsupport φ) hc) × ↥(Supported (tsupport φ) hc))
    inferInstance inferInstance (RingHom.id ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (by
      constructor
      · intro c u v
        let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (u.1.val.val,u.2.val.val)
        let v₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (v.1.val.val,v.2.val.val)
        change dist (c • u₀) (c • v₀)≤dist c 0*dist u₀ v₀
        exact dist_smul_pair c u₀ v₀
      · intro c d u
        let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (u.1.val.val,u.2.val.val)
        change dist (c • u₀) (d • u₀)≤dist c d*dist u₀ 0
        exact dist_pair_smul c d u₀) inferInstance inferInstance
    (@CompleteSpace.prod (Supported (tsupport φ) hc) (Supported (tsupport φ) hc)
      _ _ (supported_complete (tsupport φ) hc) (supported_complete (tsupport φ) hc))
    (localizedSupportedPair hφ hc hp) (localEnergyTest hφ hc hp)
    (localEnergyTest_dense hφ hc hp)
    (localizedSupportedPair_bound hφ hc hp) F

def localEnergyInclusion : cubicThetaLocalEnergySpace hφ hc hp →L[ℝ] TangentComplexL2 :=
  (complexInclusion (tsupport φ) hc).comp (localEnergyToSupported hφ hc hp)

theorem localEnergyInclusion_compact : IsCompactOperator (localEnergyInclusion hφ hc hp) :=
  (complexInclusion_compact (tsupport φ) hc).comp_clm (localEnergyToSupported hφ hc hp)

end CubicFirstMoment.LocalSobolev

end

end OAI
