import Mathlib
import OAI.Analysis.FreeWords.AmplifiedBlockModelDefinitions
import OAI.Analysis.FreeWords.AmplifiedCyclicApprox
import OAI.Analysis.FreeWords.CyclicApproxNet
import OAI.Analysis.FreeWords.MatrixPowerBlockLimits

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer KKMatrixExpectation KKHaarEndpoints Filter

open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_amplified_block_model : FiniteAmplifiedBlockModel (H := H) := by
  classical
  intro M τ hfac hdiff n hn K F E hF hE ε hε
  let τn := matrixTraceMap τ.map n
  let B := (numericalHom (A := ConcreteAlgebra M) n).range.toSubalgebra
  obtain ⟨u,hgood,hH,hC⟩ := cyclic_approx_net τn B (FullMatrixUnitary n)
    (finite_amplified_cyclic_approx M τ hfac hdiff hn)
  have hblocks := matrix_power_block_limits (A := ConcreteAlgebra M)
    (CyclicIndex τn B) atTop τ.map τ.normalized τ.tracial n hn u hH hC
  have hKsmall : ∀ᶠj in atTop,∀k∈K,k≠0 → ‖τn (u j^k).val‖<ε := by
    apply (Filter.eventually_all_finset K).2
    intro k hk
    by_cases hk0 : k=0
    · exact Eventually.of_forall (fun _ h => (h hk0).elim)
    · have hh := Metric.tendsto_nhds.mp (hH k hk0) ε hε
      simpa only [dist_zero_right] using hh.mono (fun j hj _ => hj)
  have hFsmall : ∀ᶠj in atTop,∀w∈F,‖τn (powerWord (u j) w)‖<ε := by
    apply (Filter.eventually_all_finset F).2
    intro w hw
    simpa only [dist_zero_right] using Metric.tendsto_nhds.mp (hC w (hF w hw).1 (hF w hw).2) ε hε
  have hEsmall : ∀ᶠj in atTop,∀z∈E,∀a b,
      ‖τ.map ((powerWord (u j) z.1*(u j^z.2).val) a b)‖<ε := by
    apply (Filter.eventually_all_finset E).2
    intro z hz
    apply Filter.eventually_all.2
    intro a
    apply Filter.eventually_all.2
    intro b
    simpa only [dist_zero_right] using Metric.tendsto_nhds.mp
      (hblocks z.1 (hE z hz).1 z.2 (hE z hz).2 a b) ε hε
  obtain ⟨j,hjK,hjF,hjE⟩ := (hKsmall.and (hFsmall.and hEsmall)).exists
  obtain ⟨d,hd,ρ,hρ,hU⟩ := hgood j
  exact ⟨d,hd,ρ,hρ,u j,hU,hjK,hjF,hjE⟩

end

end KKFreeLiftFrontier
end

end OAI
