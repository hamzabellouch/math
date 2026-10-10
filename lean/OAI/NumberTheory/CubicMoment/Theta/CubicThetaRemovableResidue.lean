import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueVanishing

namespace OAI

/-! The proved vanishing residues give actual analytic extensions,
not only vanishing scalar observations. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaSimpleResidue_removable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a : ℂ} (hf : MeromorphicAt f a)
    (hlim : Tendsto (fun z : ℂ => (z-a) • f z) (𝓝[≠] a) (𝓝 0)) :
    ∃ g : ℂ → E, AnalyticAt ℂ g a ∧ f =ᶠ[𝓝[≠] a] g := by
  have hsub : AnalyticAt ℂ (fun z : ℂ => z-a) a := analyticAt_id.sub analyticAt_const
  have hm : MeromorphicAt (fun z : ℂ => (z-a) • f z) a := hsub.meromorphicAt.smul hf
  have ho := (tendsto_zero_iff_meromorphicOrderAt_pos hm).mp hlim
  change 0 < meromorphicOrderAt ((fun z : ℂ => z-a) • f) a at ho
  rw [meromorphicOrderAt_smul hsub.meromorphicAt hf,meromorphicOrderAt_id_sub_const] at ho
  apply hf.meromorphicOrderAt_nonneg_iff.mp
  cases h : meromorphicOrderAt f a with
  | top => simp
  | coe n =>
    rw [h] at ho
    have hp : (0:ℤ)<1+n := by exact_mod_cast ho
    have hn : (0:ℤ)≤n := by omega
    exact_mod_cast hn

theorem cubicThetaForcedEnergy_removable {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2)
    (hne : (σ:ℂ)≠4/3) :
    ∃ g : ℂ → cubicThetaGlobalEnergySpace, AnalyticAt ℂ g (σ:ℂ) ∧
      (fun s => cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter s)
        (cubicThetaForcingL2 s))=ᶠ[𝓝[≠] (σ:ℂ)] g := by
  apply cubicThetaSimpleResidue_removable (cubicThetaForcedEnergy_meromorphic (by simpa using hσ))
  have ht := cubicThetaForcedEnergy_residue hσ hσ2
  rwa [cubicThetaArithmeticResidueEnergy_vanishes hσ hσ2 hne] at ht

theorem cubicThetaForcedResolvent_removable {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2)
    (hne : (σ:ℂ)≠4/3) :
    ∃ g : ℂ → CubicThetaGlobalL2, AnalyticAt ℂ g (σ:ℂ) ∧
      cubicThetaForcedResolvent=ᶠ[𝓝[≠] (σ:ℂ)] g := by
  apply cubicThetaSimpleResidue_removable (cubicThetaForcedResolvent_meromorphic (by simpa using hσ))
  have ht := cubicThetaForcedResolvent_residue hσ hσ2
  simpa only [cubicThetaArithmeticResidueEnergy_vanishes hσ hσ2 hne,map_zero] using ht

end CubicFirstMoment

end

end OAI
