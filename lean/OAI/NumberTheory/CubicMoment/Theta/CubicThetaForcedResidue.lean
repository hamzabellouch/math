import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSpectralSimplePole
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticDistribution

namespace OAI

/-! The residue of the actual arithmetic continuation is an explicit
finite-dimensional spectral projection of its incoming forcing. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

def cubicThetaArithmeticResidueEnergy (σ : ℝ) : cubicThetaGlobalEnergySpace :=
  (cubicThetaGlobalSpectralParameter (σ:ℂ)/((2*σ-2:ℝ):ℂ)) •
    cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ))
      (cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (σ:ℂ)))

theorem cubicThetaForcedEnergy_residue_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) •
      cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s))
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaArithmeticResidueEnergy σ)) := by
  have hA := cubicThetaSpectralEnergyInverse_residue_closed hσ hσ2
  have hF : Tendsto (fun s : ℂ => cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 s))
      (𝓝[≠] (σ:ℂ))
      (𝓝 (cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (σ:ℂ)))) :=
    (cubicThetaGlobalInclusion.adjoint.continuous.continuousAt.comp
      (cubicThetaForcingL2_analytic (σ:ℂ)).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hc : Continuous (fun p :
      (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) × cubicThetaGlobalEnergySpace =>
      p.1 p.2) := continuous_fst.clm_apply continuous_snd
  have h := (hc.tendsto _).comp (hA.prodMk_nhds hF)
  simpa only [Function.comp_def,smul_apply,cubicThetaContinuedEnergyLift,
    cubicThetaArithmeticResidueEnergy] using h

theorem cubicThetaForcedEnergy_residue {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) •
      cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s))
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaArithmeticResidueEnergy σ)) :=
  cubicThetaForcedEnergy_residue_closed hσ hσ2.le

theorem cubicThetaForcedResolvent_residue_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) • cubicThetaForcedResolvent s)
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))) := by
  have h := (cubicThetaGlobalInclusion.continuous.tendsto _).comp
    (cubicThetaForcedEnergy_residue_closed hσ hσ2)
  have hu : ∀ᶠ s : ℂ in 𝓝[≠] (σ:ℂ),
      IsUnit (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter s)) :=
    (cubicThetaSpectralParameter_punctured hσ).eventually
      (cubicThetaEnergyPencil_eventually_unit (cubicThetaGlobalSpectralParameter_below_threshold
        (by simpa using hσ)))
  have he : (fun s : ℂ => cubicThetaGlobalInclusion ((s-(σ:ℂ)) •
      cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s)))=ᶠ[𝓝[≠] (σ:ℂ)]
      (fun s : ℂ => (s-(σ:ℂ)) • cubicThetaForcedResolvent s) := by
    filter_upwards [hu] with s hs
    rw [map_smul,cubicThetaContinuedEnergyLift_value hs]
    rfl
  exact h.congr' he

theorem cubicThetaForcedResolvent_residue {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) • cubicThetaForcedResolvent s)
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))) :=
  cubicThetaForcedResolvent_residue_closed hσ hσ2.le

lemma cubicThetaArithmeticResidueEnergy_kernel (σ : ℝ) :
    cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (σ:ℂ))
      (cubicThetaArithmeticResidueEnergy σ)=0 := by
  unfold cubicThetaArithmeticResidueEnergy
  rw [map_smul]
  have h := (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (σ:ℂ))).ker.starProjection_apply_mem
    (cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (σ:ℂ)))
  change cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (σ:ℂ))
    (cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ))
      (cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (σ:ℂ))))=0 at h
  rw [h,smul_zero]

lemma cubicThetaArithmeticResidueEnergy_weak (σ : ℝ) (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v)
      (cubicThetaGlobalEnergyGradient (cubicThetaArithmeticResidueEnergy σ))+
    ((σ:ℂ)*((σ:ℂ)-2))*inner ℂ (cubicThetaGlobalInclusion v)
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))=0 := by
  have h := cubicThetaEnergyPencil_inner (cubicThetaGlobalSpectralParameter (σ:ℂ))
    v (cubicThetaArithmeticResidueEnergy σ)
  rw [cubicThetaArithmeticResidueEnergy_kernel,inner_zero_right] at h
  simpa only [cubicThetaGlobalSpectralParameter,sub_sub_cancel] using h.symm

end CubicFirstMoment

end

end OAI
