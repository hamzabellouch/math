import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinPlane
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! The derivative of an outgoing plane has exactly the differentiated Robin data. -/

open Filter Topology
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralRobin_parameter_column (U : ℂ → E₄)
    (M : ℂ → (ℂ × ℂ →L[ℂ] ℂ × ℂ)) (D : E₄) (M' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (z : ℂ)
    (hU : HasDerivAt U D z) (hM : HasDerivAt M M' z)
    (he : ∀ᶠ lam in 𝓝 z, spectralPhysicalDerivativeMap (U lam) = M lam (spectralPhysicalValueMap (U lam))) :
    spectralPhysicalDerivativeMap D = M z (spectralPhysicalValueMap D) + M' (spectralPhysicalValueMap (U z)) := by
  have hl := spectralPhysicalDerivativeMap.hasFDerivAt.comp_hasDerivAt z hU
  have hr := hM.clm_apply (spectralPhysicalValueMap.hasFDerivAt.comp_hasDerivAt z hU)
  have he' : (spectralPhysicalDerivativeMap ∘ U) =ᶠ[𝓝 z]
      (fun lam => M lam (spectralPhysicalValueMap (U lam))) := he
  have hh := hl.unique (hr.congr_of_eventuallyEq he')
  simpa only [Function.comp_def,add_comm] using hh

theorem spectralJetRobin_chain_plane (U V DU DV W₀ W : E₄) (a b : ℂ)
    (M' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hdet : spectralValueDet (spectralPhysicalValueMap U) (spectralPhysicalValueMap V) ≠ 0)
    (hW₀ : W₀ = a • U + b • V)
    (hDU : spectralPhysicalDerivativeMap DU = spectralJetRobin U V (spectralPhysicalValueMap DU) +
      M' (spectralPhysicalValueMap U))
    (hDV : spectralPhysicalDerivativeMap DV = spectralJetRobin U V (spectralPhysicalValueMap DV) +
      M' (spectralPhysicalValueMap V))
    (hW : spectralPhysicalDerivativeMap W = spectralJetRobin U V (spectralPhysicalValueMap W) +
      M' (spectralPhysicalValueMap W₀)) :
    ∃ c : ℂ × ℂ, W = a • DU + b • DV + (c.1 • U + c.2 • V) := by
  have he : spectralPhysicalDerivativeMap (W - (a • DU + b • DV)) =
      spectralJetRobin U V (spectralPhysicalValueMap (W - (a • DU + b • DV))) := by
    rw [map_sub,map_add,map_smul,map_smul,hW,hDU,hDV,hW₀]
    simp only [map_sub,map_add,map_smul,smul_add]
    abel
  obtain ⟨c,hc⟩ := (spectralJetRobin_plane U V (W - (a • DU + b • DV)) hdet).mp he
  refine ⟨c,?_⟩
  have hh := sub_eq_iff_eq_add.mp hc
  calc
    W = (c.1 • U + c.2 • V) + (a • DU + b • DV) := hh
    _ = _ := add_comm _ _

end DefocusingNLS

end OAI
