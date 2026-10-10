import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinDerivative

namespace OAI

/-! Analytic outgoing columns satisfy the derivative of their exact Robin plane. -/

open Filter Topology
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralJetRobin_column_derivatives (U V : ℂ → E₄) (z : ℂ)
    (hU : AnalyticAt ℂ U z) (hV : AnalyticAt ℂ V z)
    (hdet : spectralValueDet (spectralPhysicalValueMap (U z)) (spectralPhysicalValueMap (V z)) ≠ 0) :
    let M := fun lam => spectralJetRobin (U lam) (V lam)
    spectralPhysicalDerivativeMap (deriv U z) = M z (spectralPhysicalValueMap (deriv U z)) +
      deriv M z (spectralPhysicalValueMap (U z)) ∧
    spectralPhysicalDerivativeMap (deriv V z) = M z (spectralPhysicalValueMap (deriv V z)) +
      deriv M z (spectralPhysicalValueMap (V z)) := by
  let M := fun lam => spectralJetRobin (U lam) (V lam)
  have hM : HasDerivAt M (deriv M z) z := (spectralJetRobin_analyticAt U V z hU hV hdet).differentiableAt.hasDerivAt
  have hu := spectralPhysicalValueMap.continuous.continuousAt.comp hU.continuousAt
  have hv := spectralPhysicalValueMap.continuous.continuousAt.comp hV.continuousAt
  have hc : ContinuousAt (fun lam => spectralValueDet (spectralPhysicalValueMap (U lam))
      (spectralPhysicalValueMap (V lam))) z := (hu.fst.mul hv.snd).sub (hu.snd.mul hv.fst)
  have hn := hc.eventually (eventually_ne_nhds hdet)
  constructor
  · apply spectralRobin_parameter_column U M _ _ z hU.differentiableAt.hasDerivAt hM
    filter_upwards [hn] with lam hlam
    apply (spectralJetRobin_plane (U lam) (V lam) (U lam) hlam).mpr
    exact ⟨(1,0),by simp⟩
  · apply spectralRobin_parameter_column V M _ _ z hV.differentiableAt.hasDerivAt hM
    filter_upwards [hn] with lam hlam
    apply (spectralJetRobin_plane (U lam) (V lam) (V lam) hlam).mpr
    exact ⟨(0,1),by simp⟩

theorem spectralJetRobin_derivative_plane (U V : ℂ → E₄) (z : ℂ)
    (hU : AnalyticAt ℂ U z) (hV : AnalyticAt ℂ V z)
    (hdet : spectralValueDet (spectralPhysicalValueMap (U z)) (spectralPhysicalValueMap (V z)) ≠ 0)
    (a b : ℂ) (W₀ W : E₄) (hW₀ : W₀ = a • U z + b • V z)
    (hW : spectralPhysicalDerivativeMap W = spectralJetRobin (U z) (V z) (spectralPhysicalValueMap W) +
      deriv (fun lam => spectralJetRobin (U lam) (V lam)) z (spectralPhysicalValueMap W₀)) :
    ∃ c : ℂ × ℂ, W = a • deriv U z + b • deriv V z + (c.1 • U z + c.2 • V z) := by
  obtain ⟨hu,hv⟩ := spectralJetRobin_column_derivatives U V z hU hV hdet
  exact spectralJetRobin_chain_plane (U z) (V z) (deriv U z) (deriv V z) W₀ W a b _ hdet hW₀ hu hv hW

end DefocusingNLS

end OAI
