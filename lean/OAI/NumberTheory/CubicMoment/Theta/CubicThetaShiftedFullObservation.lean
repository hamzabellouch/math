import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactIncomingTransform

namespace OAI

/-! The full translated-cusp observation, including the entire incoming
correction at low height. Its residue is unchanged. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaCompactShiftedFamily_remainder (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) {s : ℂ} (hs : 3<s.re) :
    cubicThetaCompactShiftedFamily b hK s=ᵐ[cubicThetaPointMeasure.restrict K]
      (fun p => cubicThetaResidueScale*cubicThetaArithmeticRemainder
        (cubicThetaShiftedInversion b • p).val s) := by
  have hF := cubicThetaCompactIntegralRestriction_section (cubicThetaShiftedInversion b) hK
    (cubicThetaArithmeticSection s (by linarith)) (cubicThetaArithmeticSection_memLp hs)
  have hscalar := Lp.coeFn_smul cubicThetaResidueScale
    (cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
      ((cubicThetaArithmeticSection_memLp hs).toLp _))
  rw [cubicThetaCompactShiftedFamily,map_smul,←cubicThetaArithmeticL2_eq_forcedResolvent hs]
  dsimp only [cubicThetaArithmeticL2]
  filter_upwards [hscalar,hF] with p hp hFp
  rw [hp]
  change cubicThetaResidueScale*_= _
  rw [hFp]
  rfl

def cubicThetaShiftedIncomingWindow (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) (s : ℂ) : ℂ :=
  ∫ p in cubicThetaShiftedWindow a d,star (cubicThetaShiftedFourierWeight h W p)*
    cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s
      ∂cubicThetaPointMeasure

def cubicThetaShiftedFullObservation (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K) (s : ℂ) : ℂ :=
  cubicThetaShiftedWindowObservation b h W a d hK s+
    cubicThetaResidueScale*cubicThetaShiftedIncomingWindow b h W a d s

lemma cubicThetaShiftedFullObservation_meromorphic (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    {a : ℝ} (ha : 0<a) (d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt (cubicThetaShiftedFullObservation b h W a d hK) s :=
  (cubicThetaShiftedWindowObservation_meromorphic b h W a d hK hs).add
    ((analyticAt_const.mul ((cubicThetaShiftedIncomingWindow_differentiable b h W ha d).analyticAt s)).meromorphicAt)

lemma cubicThetaShiftedIncomingWindow_integrable (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) (s : ℂ) :
    IntegrableOn (fun p => star (cubicThetaShiftedFourierWeight h W p)*
      cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s)
      (cubicThetaShiftedWindow a d) cubicThetaPointMeasure := by
  have hc := (cubicThetaShiftedFourierWeight_continuous h W).star.mul
    ((cubicThetaIncoming_point_continuous s).comp
      (continuous_const_smul (cubicThetaShiftedInversion b)))
  exact (hc.continuousOn.integrableOn_compact hK).mono_set hSK

lemma cubicThetaShiftedFullObservation_right (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) {s : ℂ} (hs : 3<s.re) :
    cubicThetaShiftedFullObservation b h W a d hK s=
      cubicThetaResidueScale*∫ p in cubicThetaShiftedWindow a d,
        star (cubicThetaShiftedFourierWeight h W p)*
          cubicThetaEisenstein (cubicThetaShiftedInversion b • p).val s
          ∂cubicThetaPointMeasure := by
  have hR := cubicThetaShiftedWindowTest_integrable h W a d hK hSK _ _
    (cubicThetaCompactShiftedFamily_remainder b hK hs)
  have hI := (cubicThetaShiftedIncomingWindow_integrable b h W a d hK hSK s).const_mul
    cubicThetaResidueScale
  rw [cubicThetaShiftedFullObservation,cubicThetaShiftedWindowObservation,
    cubicThetaCompactShiftedObservation,cubicThetaShiftedWindowTest_pairing h W a d hK hSK _ _
      (cubicThetaCompactShiftedFamily_remainder b hK hs),cubicThetaShiftedIncomingWindow,
    ←integral_const_mul,←integral_add hR hI,←integral_const_mul]
  apply setIntegral_congr_fun (cubicThetaShiftedWindow_measurable a d)
  intro p _
  dsimp only
  change star (cubicThetaShiftedFourierWeight h W p)*
      (cubicThetaResidueScale*(cubicThetaEisenstein (cubicThetaShiftedInversion b • p).val s-
        cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s))+
      cubicThetaResidueScale*(star (cubicThetaShiftedFourierWeight h W p)*
        cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s)=_
  ring

lemma cubicThetaShiftedFullObservation_residue (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    {a : ℝ} (ha : 0<a) (d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaShiftedFullObservation b h W a d hK s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (∫ p in cubicThetaShiftedWindow a d,
        star (cubicThetaShiftedFourierWeight h W p)*
          cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
            (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)
          ∂cubicThetaPointMeasure)) := by
  have hzero : Tendsto (fun s : ℂ => s-4/3) (𝓝[≠] (4/3:ℂ)) (𝓝 (0:ℂ)) := by
    have hc : ContinuousAt (fun s : ℂ => s-4/3) (4/3:ℂ) :=
      continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hi := (cubicThetaShiftedIncomingWindow_differentiable b h W ha d).continuous
    |>.continuousAt (x:=(4/3:ℂ))
  have hc : ContinuousAt (fun s : ℂ => cubicThetaResidueScale*
      cubicThetaShiftedIncomingWindow b h W a d s) (4/3:ℂ) := continuousAt_const.mul hi
  have hz := hzero.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have ht := (cubicThetaShiftedWindowObservation_residue b h W a d hK hSK).add hz
  simpa only [cubicThetaShiftedFullObservation,cubicThetaShiftedIncomingWindow,mul_add,
    zero_mul,add_zero] using ht

end CubicFirstMoment

end

end OAI
