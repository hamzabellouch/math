import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingCompactIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcedResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierMass

namespace OAI

/-! The genuine meromorphic Fourier observable at any positive cutoff.
Its incoming correction is entire and its residue is the actual global mass pairing. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaPositiveFourierObservable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (s : ℂ) : ℂ :=
  cubicThetaArithmeticDistribution (cubicThetaPositiveFourierProfileSection h W hε hW)
    (cubicThetaPositiveFourierProfileSection_compact h W hε hW) s+
  ∫ p,star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingEisenstein p.val s
    ∂cubicThetaPointMeasure

lemma cubicThetaPositiveFourierObservable_meromorphic (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt (cubicThetaPositiveFourierObservable h W hε hW) s :=
  (cubicThetaArithmeticDistribution_meromorphic _ _ hs).add
    (((cubicThetaIncomingCompactIntegral_differentiable h W hε hW).analyticAt s).meromorphicAt)

lemma cubicThetaIncoming_point_continuous (s : ℂ) :
    Continuous (fun p : CubicThetaPoint => cubicThetaIncomingEisenstein p.val s) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (((cubicThetaIncomingEisenstein_contDiffOn s).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)).continuousAt.comp
      continuous_subtype_val.continuousAt)

lemma cubicThetaPositiveFourierObservable_right (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {s : ℂ} (hs : 3<s.re) :
    cubicThetaPositiveFourierObservable h W hε hW s=
      ∫ p,star (cubicThetaFourierStripSeed h W p)*cubicThetaEisenstein p.val s
        ∂cubicThetaPointMeasure := by
  rw [cubicThetaPositiveFourierObservable,cubicThetaArithmeticDistribution_right _ _ hs,
    cubicThetaPositiveFourierProfile_pairing_integral h W hε hW]
  have hR := cubicThetaFourierStripSeed_pair_integrable h W hε hW
    (cubicThetaArithmeticSection s (by linarith))
  have hI := cubicThetaFourierStripSeed_mul_integrable h W hε hW _
    (cubicThetaIncoming_point_continuous s)
  rw [←integral_add hR hI]
  apply integral_congr_ae
  filter_upwards with p
  change star (cubicThetaFourierStripSeed h W p)*cubicThetaArithmeticRemainder p.val s+
    star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingEisenstein p.val s=_
  rw [cubicThetaArithmeticRemainder]
  ring

theorem cubicThetaPositiveFourierObservable_residue (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaPositiveFourierObservable h W hε hW s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
        (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))))) := by
  let P := cubicThetaPositiveFourierProfileL2 h W hε hW
  have ht := ((innerSL ℂ P).continuous.tendsto _).comp
    (cubicThetaForcedResolvent_residue (σ:=(4/3:ℝ)) (by norm_num) (by norm_num))
  have hd : Tendsto (fun s : ℂ => (s-4/3)*
      cubicThetaArithmeticDistribution (cubicThetaPositiveFourierProfileSection h W hε hW)
        (cubicThetaPositiveFourierProfileSection_compact h W hε hW) s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (inner ℂ P
        (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))))) := by
    simpa only [Function.comp_def,innerSL_apply_apply,inner_smul_right,
      Complex.ofReal_div,Complex.ofReal_ofNat,cubicThetaArithmeticDistribution,
      P,cubicThetaPositiveFourierProfileL2] using ht
  have hi := (cubicThetaIncomingCompactIntegral_differentiable h W hε hW).continuous
    |>.continuousAt (x:=(4/3:ℂ))
  have hzero : Tendsto (fun s : ℂ => s-4/3) (𝓝[≠] (4/3:ℂ)) (𝓝 (0:ℂ)) := by
    have hz : ContinuousAt (fun s : ℂ => s-4/3) (4/3:ℂ) :=
      continuousAt_id.sub_const _
    simpa only [sub_self] using hz.tendsto.mono_left nhdsWithin_le_nhds
  have hz' : Tendsto (fun s : ℂ => (s-4/3)*
      ∫ p,star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingEisenstein p.val s
        ∂cubicThetaPointMeasure) (𝓝[≠] (4/3:ℂ)) (𝓝 (0:ℂ)) := by
    simpa only [zero_mul] using hzero.mul (hi.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [cubicThetaPositiveFourierObservable,mul_add,add_zero,P] using hd.add hz'

end CubicFirstMoment

end

end OAI
