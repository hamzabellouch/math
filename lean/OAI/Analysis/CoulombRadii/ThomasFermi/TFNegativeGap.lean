import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TfExtendNonneg

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology
noncomputable section
namespace Coulomb

def rawTFNegativeError (Φ ρ σ : Space → ℝ) : ℝ :=
  ∫ x, max ((∫ z, coulombKernel (x-z)*ρ z)-Φ x) 0*σ x

lemma rawTFNegativeError_congr_ae (Φ : Space → ℝ) {ρ σ ρ' σ' : Space → ℝ}
    (hρ : ρ =ᵐ[volume] ρ') (hσ : σ =ᵐ[volume] σ') :
    rawTFNegativeError Φ ρ σ=rawTFNegativeError Φ ρ' σ' := by
  have hp (x : Space) : (∫ z, coulombKernel (x-z)*ρ z)=∫ z, coulombKernel (x-z)*ρ' z :=
    integral_congr_ae (hρ.mono fun z hz => by simp only [hz])
  unfold rawTFNegativeError
  apply integral_congr_ae
  filter_upwards [hσ] with x hx
  rw [hp,hx]

lemma rawTFNegativeError_tfDensity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (hg : TFNonneg g) :
    rawTFNegativeError Φ (tfDensity Ω f) (tfDensity Ω g)=
      ∫ x in Ω, max (tfPotential f x-W x) 0*g x := by
  rw [rawTFNegativeError_congr_ae Φ (tfDensity_ae_tfExtend hΩ hf) (tfDensity_ae_tfExtend hΩ hg)]
  unfold rawTFNegativeError
  change (∫ x, max (tfPotential f x-Φ x) 0*tfExtend Ω g x)=_
  calc
    _ = ∫ x in Ω, max (tfPotential f x-Φ x) 0*g x := by
      rw [←integral_indicator hΩ]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x∈Ω <;> simp [tfExtend,hx]
    _ = _ := integral_congr_ae (hW.mono fun x hx => by rw [hx])

lemma raw_localTF_gap_identity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    coulombBilinear (fun x => tfDensity Ω f x-localTFDensity hΩ W x)
      (fun x => tfDensity Ω f x-localTFDensity hΩ W x)/2+
      rawTFBregman (localTFDensity hΩ W) (tfDensity Ω f)+
      rawTFNegativeError Φ (localTFDensity hΩ W) (tfDensity Ω f)=
    rawThomasFermiEnergy Φ (tfDensity Ω f)-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  unfold localTFDensity
  rw [coulombBilinear_tfDensity_sub hΩ (localTFMinimizer_nonneg hΩ W) hf,
    rawTFBregman_tfDensity hΩ (localTFMinimizer_nonneg hΩ W) hf,
    rawTFNegativeError_tfDensity hΩ Φ W hW (localTFMinimizer_nonneg hΩ W) hf,
    rawThomasFermiEnergy_tfDensity hΩ Φ W hW hf,
    rawThomasFermiEnergy_tfDensity hΩ Φ W hW (localTFMinimizer_nonneg hΩ W)]
  exact (tfEnergy_minimizer_expansion hΩ thomasFermiKineticConstant_pos W
    (localTFMinimizer_nonneg hΩ W) (fun _ hf => localTFMinimizer_minimizes hΩ W hf)).symm

lemma raw_localTF_gap_identity_density {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x = 0) :
    coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
      (fun x => σ x-localTFDensity hΩ W x)/2+
      rawTFBregman (localTFDensity hΩ W) σ+
      rawTFNegativeError Φ (localTFDensity hΩ W) σ=
    rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  have he := tfDensity_rawToTFLp hΩ hσ hp hs
  have hd : (fun x => tfDensity Ω (rawToTFLp σ hσ) x-localTFDensity hΩ W x) =ᵐ[volume]
      (fun x => σ x-localTFDensity hΩ W x) := he.sub EventuallyEq.rfl
  have H := raw_localTF_gap_identity hΩ Φ W hW (rawToTFLp_nonneg hσ hp)
  rwa [coulombBilinear_congr_ae hd hd,rawTFBregman_congr_ae EventuallyEq.rfl he,
    rawTFNegativeError_congr_ae Φ EventuallyEq.rfl he,rawThomasFermiEnergy_congr_ae Φ he] at H

lemma raw_localTF_refined_gap_density {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x = 0) :
    coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
      (fun x => σ x-localTFDensity hΩ W x)/2+
      rawTFNegativeError Φ (localTFDensity hΩ W) σ ≤
    rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  rw [←raw_localTF_gap_identity_density hΩ Φ W hW hσ hp hs]
  have he := tfDensity_rawToTFLp hΩ hσ hp hs
  have hb : 0 ≤ rawTFBregman (localTFDensity hΩ W) σ := by
    rw [←rawTFBregman_congr_ae EventuallyEq.rfl he]
    unfold localTFDensity
    rw [rawTFBregman_tfDensity hΩ (localTFMinimizer_nonneg hΩ W) (rawToTFLp_nonneg hσ hp)]
    exact mul_nonneg thomasFermiKineticConstant_pos.le
      (tfBregman_nonneg (localTFMinimizer_nonneg hΩ W) (rawToTFLp_nonneg hσ hp))
  linarith
end Coulomb
end

end
end

end OAI
