import Mathlib
import OAI.Analysis.FreeWords.TransportLimits
import OAI.Analysis.FreeWords.TransportTests

namespace OAI

noncomputable section

namespace KKFiniteTransport

noncomputable section

open KKTraceTransfer KKFreeLiftFrontier KKMatrixExpectation KKHaarEndpoints Filter

open scoped Matrix.Norms.Operator Topology ComplexOrder

variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M:VonNeumannAlgebra H}

attribute [local instance] concreteOrder concreteLE concretePreorder concreteSOR

theorem matrixTraceMap_continuous (τ:FaithfulNormalTrace M) (n:ℕ) :
    Continuous (matrixTraceMap τ.map n) := by
  change Continuous (fun x:MatrixAlgebra n M => (n:ℂ)⁻¹*∑i,τ.map (x i i))
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro i hi
  exact (map_continuous (tracePositive τ)).comp (by fun_prop)

theorem mixed_transport_limits (τ:FaithfulNormalTrace M) {n:ℕ} {I:Type*} (L:Filter I)
    (U:I → unitary (MatrixAlgebra n M))
    (ht:∀t:TransportTest τ n,Tendsto (fun j => testValue τ t (U j)) L (𝓝 0))
    (w:List (ℤ×MatrixAlgebra n M)) (hw:IsCenteredTest τ w) :
    Tendsto (fun j => mixedMoment τ (U j) w) L (𝓝 0) := by
  have hh := (matrixTraceMap_continuous τ n).tendsto 0 |>.comp (transport_limits τ L U ht w hw)
  simpa only [Function.comp_def,map_zero,matrixExpectation_trace τ.map τ.normalized n,
    mixedMoment,matrixTrace,matrixTraceMap_apply,powerWord] using hh

end

end KKFiniteTransport

namespace KKFreeLiftFrontier

noncomputable section

open KKFiniteTransport KKMatrixExpectation Filter

open scoped Topology

theorem finite_matrix_free_approximation : FiniteMatrixFreeApproximation := by
  classical
  intro H _ _ _ _ _ M τ hfac hdiff n hn F hF K ε hε
  obtain ⟨U,hgood,ht⟩ := KKFiniteMomentNet.finite_moment_net (FullMatrixUnitary n)
    (testValue τ) (finite_transport_tests M τ hfac hdiff n hn)
  have hsmallF : ∀ᶠj in atTop,∀w∈F,‖mixedMoment τ (U j) w‖<ε := by
    apply (Filter.eventually_all_finset F).2
    intro w hw
    simpa only [dist_zero_right] using Metric.tendsto_nhds.mp
      (mixed_transport_limits τ atTop U ht w (hF w hw)) ε hε
  have hsmallK : ∀ᶠj in atTop,∀k∈K,k≠0 → ‖matrixTrace τ n ((U j)^k).val‖<ε := by
    apply (Filter.eventually_all_finset K).2
    intro k hk
    by_cases hk0:k=0
    · subst k; exact Filter.Eventually.of_forall (by simp)
    · have hh := Metric.tendsto_nhds.mp (ht (.haar k hk0)) ε hε
      filter_upwards [hh] with j hj
      intro _
      simpa only [dist_zero_right,testValue,matrixTraceMap_apply,matrixTrace] using hj
  obtain ⟨j,hjF,hjK⟩ := (hsmallF.and hsmallK).exists
  obtain ⟨d,hd,ρ,hρ,hentry⟩ := hgood j
  exact ⟨d,hd,ρ,hρ,U j,hentry,hjK,hjF⟩

end

end KKFreeLiftFrontier
end

end OAI
