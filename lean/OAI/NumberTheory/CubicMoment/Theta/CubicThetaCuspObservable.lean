import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcedCusp

namespace OAI

/-! Bounded L2 observations of the actual continued cusp restriction.
Their initial values and residues are genuine hyperbolic strip integrals. -/
noncomputable section
open Filter Topology MeasureTheory
namespace CubicFirstMoment

def cubicThetaCuspObservable (T : CubicThetaStripL2) (s : ℂ) : ℂ :=
  inner ℂ T (cubicThetaForcedCusp s)

theorem cubicThetaCuspObservable_meromorphic (T : CubicThetaStripL2)
    {s : ℂ} (hs : 1<s.re) : MeromorphicAt (cubicThetaCuspObservable T) s :=
  cubicThetaMeromorphic_clm (innerSL ℂ T) (cubicThetaForcedCusp_meromorphic hs)

lemma cubicThetaCuspObservable_right (T : CubicThetaStripL2)
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaCuspObservable T s=
      ∫ p in cubicThetaCuspStrip 2, star (T p)*cubicThetaArithmeticRemainder p.val s
        ∂cubicThetaPointMeasure := by
  rw [cubicThetaCuspObservable,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cubicThetaForcedCusp_coe hs] with p hp
  rw [hp,RCLike.inner_apply]
  simp only [starRingEnd_apply]
  ring

theorem cubicThetaCuspObservable_residue_closed (T : CubicThetaStripL2)
    {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ))*cubicThetaCuspObservable T s)
      (𝓝[≠] (σ:ℂ))
      (𝓝 (inner ℂ T (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ)))) := by
  have h := ((innerSL ℂ T).continuous.tendsto _).comp (cubicThetaForcedCusp_residue_closed hσ hσ2)
  simpa only [Function.comp_def,innerSL_apply_apply,inner_smul_right,cubicThetaCuspObservable] using h

theorem cubicThetaCuspObservable_residue (T : CubicThetaStripL2)
    {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ))*cubicThetaCuspObservable T s)
      (𝓝[≠] (σ:ℂ))
      (𝓝 (inner ℂ T (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ)))) :=
  cubicThetaCuspObservable_residue_closed T hσ hσ2.le

end CubicFirstMoment

end

end OAI
