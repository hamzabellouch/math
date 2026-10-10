import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.DesignatedBranchSuccess
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoveryCandidates

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open Completion FiniteSampling
variable {n m H : ℕ} [PseudoMetricSpace (Fin n)]
variable (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
  (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
  (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n)
  (hn : n≤H) (hm : m≤H) (hH : 1≤H) (hp : s.leaves.length≤H)
  (r0 y0 : Fin n) (seed : Fin (tapeSize H)→Bool)
include hδ hSF hS hΔ hbound
lemma candidates_feasible : ∀ U∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed,
    U⊆F ∧ U.card=S.card ∧ U.Nonempty := by
  apply candidates_property
  · intro q
    exact BinaryZeroBranch.output_feasible δ hδ D F S hSF hS Δ hΔ hbound s _ q.val _
  · intro q c b
    exact BinaryObservableBranch.output_feasible δ hδ D F S hSF hS Δ hΔ hbound s _ _ q.val c.val r0 y0 _
lemma result_feasible : result δ D F S Δ s hn hm hH hp r0 y0 seed⊆F ∧
    (result δ D F S Δ s hn hm hH hp r0 y0 seed).card=S.card ∧
    (result δ D F S Δ s hn hm hH hp r0 y0 seed).Nonempty := by
  exact BinaryMetricBest.best_property δ D S _ _ ⟨hSF,rfl,hS⟩
    (candidates_feasible δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed)
lemma result_cost_le_zero (q : Fin (n+1)) :
    realCost D (result δ D F S Δ s hn hm hH hp r0 y0 seed)≤
      realCost D (zero δ D F S Δ s hn hH hp seed q) :=
  BinaryMetricBest.realCost_le_mem δ hδ D S hS _
    (fun U hU=>(candidates_feasible δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed U hU).2.2)
    _ (zero_mem δ D F S Δ s hn hm hH hp r0 y0 seed q)
lemma result_cost_le_positive (q c : Fin (n+1)) (b : Fin m) :
    realCost D (result δ D F S Δ s hn hm hH hp r0 y0 seed)≤
      realCost D (positive δ D F S Δ s hn hm hp r0 y0 seed q c b) :=
  BinaryMetricBest.realCost_le_mem δ hδ D S hS _
    (fun U hU=>(candidates_feasible δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed U hU).2.2)
    _ (positive_mem δ D F S Δ s hn hm hH hp r0 y0 seed q c b)
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
