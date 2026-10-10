import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNonzeroSpectralResidue

namespace OAI

/-! The arithmetic family has an actual nonremovable pole at s=4/3,
with the residue belonging to the constructed global automorphic L2 space. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

theorem cubicThetaForcedResolvent_nonzero_residue :
    ∃ R : CubicThetaGlobalL2, R≠0 ∧
      Tendsto (fun s : ℂ => (s-4/3) • cubicThetaForcedResolvent s)
        (𝓝[≠] (4/3:ℂ)) (𝓝 R) := by
  refine ⟨cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)),
    cubicThetaArithmeticResidueValue_ne_zero,?_⟩
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
    cubicThetaForcedResolvent_residue (σ:=4/3) (by norm_num) (by norm_num)

theorem cubicThetaForcedResolvent_not_continuousAt :
    ¬ContinuousAt cubicThetaForcedResolvent (4/3:ℂ) := by
  intro hc
  obtain ⟨R,hR,hr⟩ := cubicThetaForcedResolvent_nonzero_residue
  have hs : Tendsto (fun s : ℂ => s-4/3) (𝓝[≠] (4/3:ℂ)) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℂ => s-4/3) (4/3:ℂ) :=
      continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun s : ℂ => (s-4/3) • cubicThetaForcedResolvent s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 0) := by
    simpa only [zero_smul] using hs.smul (hc.tendsto.mono_left nhdsWithin_le_nhds)
  exact hR (tendsto_nhds_unique hr hz)

end CubicFirstMoment

end

end OAI
