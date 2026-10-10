import OAI.Probability.SLE.Loewner.InitialForwardRecovery
import OAI.Probability.SLE.Loewner.InitialInverseLimit
import OAI.Probability.SLE.Geometry.LocallyUniformEvaluation

namespace OAI

/-! Every inverse-chart limit covers the common final slit domain.
No convergence of the times, nor a boundary driving value, is assumed here. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem initialInverse_limit_covers_final_domain (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) :
    ∀ z∈upperHalfPlane \ range p, ∃ w∈upperHalfPlane, F w=z := by
  obtain ⟨φ,A,hφ,hA,hAlim⟩ := initialForwardCayley_subsequence p hi h0 hH t
  have hFsub := locallyUniform_reindex hlim hφ.tendsto_atTop
  intro z hz
  have hAz := initialForwardCayley_limit_interior p hi h0 hH hA hAlim z hz
  have hw : halfPlaneCayleyInv (A z)∈upperHalfPlane := halfPlaneCayleyInv_open hAz
  refine ⟨halfPlaneCayleyInv (A z),hw,?_⟩
  have hforward := initialForward_limit_tendsto p hi h0 hH hA hAlim hz
  have heval := locallyUniform_evaluation_tendsto isOpen_upperHalfPlane
    hF.continuousOn hFsub hw hforward
  have hconstant : Tendsto (fun n => initialInverseChart p hi h0 hH (t (φ n))
      (initialForwardChart p hi h0 hH (t (φ n)) z)) atTop (𝓝 z) := by
    have he : (fun n => initialInverseChart p hi h0 hH (t (φ n))
        (initialForwardChart p hi h0 hH (t (φ n)) z)) = (fun _ : ℕ => z) := by
      funext n
      exact initialInverse_forward_on_final p hi h0 hH (t (φ n)) hz
    rw [he]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique heval hconstant

end SLEExactGauge

end

end OAI
