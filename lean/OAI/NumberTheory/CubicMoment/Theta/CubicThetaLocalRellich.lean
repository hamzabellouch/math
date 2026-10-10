import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSupportedTangent

namespace OAI

/-! The two supported real Sobolev components give a compact complex
L2 inclusion on every concrete compact coordinate set. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance localRellich_tangent_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance localRellich_tangent_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

abbrev Supported (K : Set (ℂ × ℝ)) (hK : IsCompact K) :=
  h1On (cubicThetaTangentCoordinates ⁻¹' K)
    (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable)

abbrev TangentComplexL2 := Lp ℂ 2 tangentBorelVolume

def realSupportedInclusion (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    Supported K hK →L[ℝ] Lp ℝ 2 tangentBorelVolume :=
  h1OnToL2 (cubicThetaTangentCoordinates ⁻¹' K)
    (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable)

def complexInclusion (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    (Supported K hK × Supported K hK) →L[ℝ] TangentComplexL2 :=
  ((Complex.ofRealCLM.compLpL 2 tangentBorelVolume).comp
    ((realSupportedInclusion K hK).comp (ContinuousLinearMap.fst ℝ _ _)))+
  Complex.I • ((Complex.ofRealCLM.compLpL 2 tangentBorelVolume).comp
    ((realSupportedInclusion K hK).comp (ContinuousLinearMap.snd ℝ _ _)))

theorem complexInclusion_compact (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    IsCompactOperator (complexInclusion K hK) := by
  have hc : IsCompactOperator (realSupportedInclusion K hK) := supported_inclusion_compact hK
  exact ((hc.comp_clm (ContinuousLinearMap.fst ℝ _ _)).clm_comp
      (Complex.ofRealCLM.compLpL 2 tangentBorelVolume)).add
    (((hc.comp_clm (ContinuousLinearMap.snd ℝ _ _)).clm_comp
      (Complex.ofRealCLM.compLpL 2 tangentBorelVolume)).smul Complex.I)

end CubicFirstMoment.LocalSobolev

end

end OAI
