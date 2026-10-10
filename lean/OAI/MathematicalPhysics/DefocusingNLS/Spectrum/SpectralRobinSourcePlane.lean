import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinColumnDerivative

namespace OAI

/-! An outgoing homogeneous residual gives the differentiated outgoing boundary condition. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralJetRobin_chain_of_residual (U V DU DV W₀ W : E₄) (a b : ℂ)
    (M' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hW₀ : W₀=a • U+b • V)
    (hDU : spectralPhysicalDerivativeMap DU=spectralJetRobin U V (spectralPhysicalValueMap DU)+
      M' (spectralPhysicalValueMap U))
    (hDV : spectralPhysicalDerivativeMap DV=spectralJetRobin U V (spectralPhysicalValueMap DV)+
      M' (spectralPhysicalValueMap V))
    (hres : spectralPhysicalDerivativeMap (W-(a • DU+b • DV))=
      spectralJetRobin U V (spectralPhysicalValueMap (W-(a • DU+b • DV)))) :
    spectralPhysicalDerivativeMap W=spectralJetRobin U V (spectralPhysicalValueMap W)+
      M' (spectralPhysicalValueMap W₀) := by
  rw [map_sub,map_add,map_smul,map_smul,hDU,hDV] at hres
  simp only [map_sub,map_add,map_smul,smul_add] at hres
  rw [hW₀,map_add,map_smul,map_smul,map_add,map_smul,map_smul]
  linear_combination hres

theorem spectralJetRobin_parameter_chain_of_residual (U V : ℂ → E₄) (z : ℂ)
    (hU : AnalyticAt ℂ U z) (hV : AnalyticAt ℂ V z)
    (hdet : spectralValueDet (spectralPhysicalValueMap (U z)) (spectralPhysicalValueMap (V z)) ≠ 0)
    (a b : ℂ) (W₀ W : E₄) (hW₀ : W₀=a • U z+b • V z)
    (hres : ∃ c : ℂ × ℂ, W-(a • deriv U z+b • deriv V z)=c.1 • U z+c.2 • V z) :
    spectralPhysicalDerivativeMap W=spectralJetRobin (U z) (V z) (spectralPhysicalValueMap W)+
      deriv (fun lam => spectralJetRobin (U lam) (V lam)) z (spectralPhysicalValueMap W₀) := by
  obtain ⟨hp,hm⟩ := spectralJetRobin_column_derivatives U V z hU hV hdet
  exact spectralJetRobin_chain_of_residual _ _ _ _ _ _ a b _ hW₀ hp hm
    ((spectralJetRobin_plane _ _ _ hdet).2 hres)

end DefocusingNLS

end OAI
