import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcedResidue

namespace OAI

/-! The actual arithmetic continuation restricted to the high cusp.
Both its meromorphic dependence and its initial pointwise representative
are retained in the L2 strip space. -/
noncomputable section
open Filter Topology MeasureTheory
namespace CubicFirstMoment

def cubicThetaArithmeticFiniteEnergy (s : ℂ) (hs : 3<s.re) : cubicThetaFiniteEnergySections :=
  ⟨cubicThetaArithmeticSection s (by linarith),
    cubicThetaArithmeticSectionFunction_contDiffOn_one (by linarith),
    cubicThetaArithmeticSection_memLp hs,cubicThetaArithmeticGradientRepresentative_memLp hs⟩

lemma cubicThetaArithmeticFiniteEnergy_embedding (s : ℂ) (hs : 3<s.re) :
    cubicThetaFiniteEnergyEmbedding (cubicThetaArithmeticFiniteEnergy s hs)=
      cubicThetaArithmeticEnergy s hs := rfl

def cubicThetaForcedCusp (s : ℂ) : CubicThetaStripL2 :=
  cubicThetaCuspRestriction (cubicThetaContinuedEnergyLift
    (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s))

lemma cubicThetaForcedEnergy_meromorphic {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt (fun w => cubicThetaContinuedEnergyLift
      (cubicThetaGlobalSpectralParameter w) (cubicThetaForcingL2 w)) s := by
  have hp : AnalyticAt ℂ cubicThetaGlobalSpectralParameter s :=
    analyticAt_const.sub (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
  have hA := (cubicThetaEnergyInverse_meromorphic
    (cubicThetaGlobalSpectralParameter_below_threshold hs)).comp_analyticAt hp
  have hF : AnalyticAt ℂ (fun w => cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 w)) s :=
    (cubicThetaGlobalInclusion.adjoint.analyticAt _).comp (f:=cubicThetaForcingL2) (x:=s)
      (cubicThetaForcingL2_analytic s)
  exact cubicThetaMeromorphic_apply hA hF

theorem cubicThetaForcedCusp_meromorphic {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt cubicThetaForcedCusp s :=
  cubicThetaMeromorphic_clm cubicThetaCuspRestriction (cubicThetaForcedEnergy_meromorphic hs)

lemma cubicThetaForcedCusp_right {s : ℂ} (hs : 3<s.re) :
    cubicThetaForcedCusp s=cubicThetaFiniteCuspRestriction (cubicThetaArithmeticFiniteEnergy s hs) := by
  rw [cubicThetaForcedCusp,← cubicThetaArithmeticEnergy_eq_continued hs,
    ← cubicThetaArithmeticFiniteEnergy_embedding s hs,cubicThetaCuspRestriction_finiteEnergy]

lemma cubicThetaForcedCusp_coe {s : ℂ} (hs : 3<s.re) :
    cubicThetaForcedCusp s =ᵐ[cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)]
      (fun p => cubicThetaArithmeticRemainder p.val s) := by
  rw [cubicThetaForcedCusp_right hs]
  exact (cubicThetaFiniteEnergy_strip_memLp (cubicThetaArithmeticFiniteEnergy s hs)).coeFn_toLp

theorem cubicThetaForcedCusp_residue_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) • cubicThetaForcedCusp s)
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ))) := by
  have h := (cubicThetaCuspRestriction.continuous.tendsto _).comp
    (cubicThetaForcedEnergy_residue_closed hσ hσ2)
  simpa only [Function.comp_def,map_smul,cubicThetaForcedCusp] using h

theorem cubicThetaForcedCusp_residue {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) • cubicThetaForcedCusp s)
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ))) :=
  cubicThetaForcedCusp_residue_closed hσ hσ2.le

end CubicFirstMoment

end

end OAI
