import Mathlib
import OAI.Analysis.FreeWords.CyclicApproxNet
import OAI.Analysis.FreeWords.RelativeEndpointLimits
import OAI.Analysis.FreeWords.RelativeFiniteEndpointsDefinitions
import OAI.Analysis.FreeWords.ScalarFreeApprox

namespace OAI

noncomputable section

namespace KKRelativeEndpoints

noncomputable section

open Filter KKHaarEndpoints KKControlledConjugation KKRelativeMatrix

open KKTraceTransfer KKFreeLiftFrontier

open scoped Topology

variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem relative_finite_endpoints : RelativeFiniteEndpoints (H := H) := by
  classical
  intro M τ hF hD n F E hFdata hEdata ε hε
  have happ : FiniteCyclicApprox τ.map ⊤ (fun _ => True) := by
    intro K F hdata η hη
    obtain ⟨u,hK,hL⟩ := KKLocalPatching.finite_scalar_free_approximation M τ hF hD K F
      (fun w hw => (hdata w hw).1) (fun w hw z hz =>
        ⟨((hdata w hw).2 z hz).1,((hdata w hw).2 z hz).2.2⟩) η hη
    exact ⟨u,True.intro,hK,hL⟩
  obtain ⟨u,_,hH,hC⟩ := cyclic_approx_net τ.map ⊤ (fun _ => True) happ
  have hrel := relative_endpoint_limits (CyclicIndex τ.map ⊤) atTop τ.map u
    τ.normalized τ.tracial hH hC n
  have hsmallF : ∀ᶠj in atTop,∀w∈F,∀a b,‖τ.map (relativePair (u j) w a b)‖<ε := by
    apply (Filter.eventually_all_finset F).2
    intro w hw
    apply Filter.eventually_all.2
    intro a
    apply Filter.eventually_all.2
    intro b
    simpa only [dist_zero_right] using Metric.tendsto_nhds.mp
      ((hrel w (hFdata w hw).2).1 (hFdata w hw).1 a b) ε hε
  have hsmallE : ∀ᶠj in atTop,∀v∈E,∀a b,
      ‖τ.map ((relativePair (u j) v.1*amplifyConj n (u j) v.2) a b)‖<ε := by
    apply (Filter.eventually_all_finset E).2
    intro v hv
    apply Filter.eventually_all.2
    intro a
    apply Filter.eventually_all.2
    intro b
    simpa only [dist_zero_right] using Metric.tendsto_nhds.mp
      ((hrel v.1 (hEdata v hv).1).2 v.2 (hEdata v hv).2 a b) ε hε
  obtain ⟨j,hjF,hjE⟩ := (hsmallF.and hsmallE).exists
  exact ⟨u j,hjF,hjE⟩

end

end KKRelativeEndpoints
end

end OAI
