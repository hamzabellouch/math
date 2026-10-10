import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactBorelRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIntegralQuotient

namespace OAI

/-! Compact sampling after a literal integral Mobius transformation.
The map acts on actual global L2 vectors and retains the cubic Borel phase. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCompactIntegral_measure (δ : SL(2,Eisenstein))
    {K : Set CubicThetaPoint} (hK : IsCompact K) :
    MeasurePreserving (fun p : CubicThetaPoint => δ • p)
      (cubicThetaPointMeasure.restrict K)
      (cubicThetaPointMeasure.restrict ((fun p : CubicThetaPoint => δ • p) '' K)) :=
  ⟨measurable_const_smul δ,cubicThetaSmul_map_restrict δ hK.measurableSet⟩

def cubicThetaCompactIntegralRestriction (δ : SL(2,Eisenstein))
    {K : Set CubicThetaPoint} (hK : IsCompact K) :
    CubicThetaGlobalL2 →L[ℂ] Lp ℂ 2 (cubicThetaPointMeasure.restrict K) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun p : CubicThetaPoint => δ • p)
    (cubicThetaCompactIntegral_measure δ hK)).toContinuousLinearMap.comp
      (cubicThetaCompactBorelRestriction (hK.image (continuous_const_smul δ)))

lemma cubicThetaCompactIntegralRestriction_coe (δ : SL(2,Eisenstein))
    {K : Set CubicThetaPoint} (hK : IsCompact K) (F : CubicThetaGlobalL2) :
    cubicThetaCompactIntegralRestriction δ hK F=ᵐ[cubicThetaPointMeasure.restrict K]
      (fun p => cubicThetaBorelLift F (δ • p)) := by
  have hp := cubicThetaCompactIntegral_measure δ hK
  have hB := cubicThetaCompactBorelRestriction_coe (hK.image (continuous_const_smul δ)) F
  have ht := hp.quasiMeasurePreserving.ae hB
  have hc := Lp.coeFn_compMeasurePreserving
    (cubicThetaCompactBorelRestriction (hK.image (continuous_const_smul δ)) F) hp
  exact hc.trans ht

lemma cubicThetaCompactIntegralRestriction_section (δ : SL(2,Eisenstein))
    {K : Set CubicThetaPoint} (hK : IsCompact K) (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    cubicThetaCompactIntegralRestriction δ hK (hF.toLp _)=ᵐ[cubicThetaPointMeasure.restrict K]
      (fun p => F.val (δ • p)) := by
  have hp := cubicThetaCompactIntegral_measure δ hK
  have hB := cubicThetaCompactBorelRestriction_section (hK.image (continuous_const_smul δ)) F hF
  have ht := hp.quasiMeasurePreserving.ae hB
  have hc := Lp.coeFn_compMeasurePreserving
    (cubicThetaCompactBorelRestriction (hK.image (continuous_const_smul δ)) (hF.toLp _)) hp
  exact hc.trans ht

end CubicFirstMoment

end

end OAI
