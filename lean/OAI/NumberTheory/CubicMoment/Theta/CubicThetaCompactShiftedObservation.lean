import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactShiftedFamily

namespace OAI

/-! Bounded scalar observations of the translated family and its actual residue. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

def cubicThetaCompactShiftedObservation (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) (T : Lp ℂ 2 (cubicThetaPointMeasure.restrict K)) (s : ℂ) : ℂ :=
  inner ℂ T (cubicThetaCompactShiftedFamily b hK s)

lemma cubicThetaCompactShiftedObservation_meromorphic (b : Eisenstein)
    {K : Set CubicThetaPoint} (hK : IsCompact K)
    (T : Lp ℂ 2 (cubicThetaPointMeasure.restrict K)) {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt (cubicThetaCompactShiftedObservation b hK T) s :=
  cubicThetaMeromorphic_clm (innerSL ℂ T) (cubicThetaCompactShiftedFamily_meromorphic b hK hs)

lemma cubicThetaCompactShiftedObservation_right (b : Eisenstein)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (hhigh : ∀ p∈K,1<p.val.2)
    (T : Lp ℂ 2 (cubicThetaPointMeasure.restrict K)) {s : ℂ} (hs : 3<s.re) :
    cubicThetaCompactShiftedObservation b hK T s=
      cubicThetaResidueScale*∫ p in K,star (T p)*cubicThetaEisenstein
        ((cubicThetaInversion 1 p.val).1+b,(cubicThetaInversion 1 p.val).2) s
        ∂cubicThetaPointMeasure := by
  rw [cubicThetaCompactShiftedObservation,L2.inner_def,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [cubicThetaCompactShiftedFamily_right b hK hhigh hs] with p hp
  rw [hp,RCLike.inner_apply]
  simp only [starRingEnd_apply]
  ring

lemma cubicThetaCompactShiftedObservation_residue (b : Eisenstein)
    {K : Set CubicThetaPoint} (hK : IsCompact K)
    (T : Lp ℂ 2 (cubicThetaPointMeasure.restrict K)) :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaCompactShiftedObservation b hK T s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (∫ p in K,star (T p)*cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)
        ∂cubicThetaPointMeasure)) := by
  have ht := ((innerSL ℂ T).continuous.tendsto _).comp
    (cubicThetaCompactShiftedFamily_residue b hK)
  have he : inner ℂ T
      (cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
        (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue))=
      ∫ p in K,star (T p)*cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)
        ∂cubicThetaPointMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [cubicThetaCompactShiftedResidue_model b hK] with p hp
    rw [hp,RCLike.inner_apply]
    simp only [starRingEnd_apply]
    ring
  simpa only [Function.comp_def,innerSL_apply_apply,inner_smul_right,
    cubicThetaCompactShiftedObservation,he] using ht

end CubicFirstMoment

end

end OAI
