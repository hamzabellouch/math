import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralRecoverySemantics
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoveryFeasible

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open Completion Sampling.Comparison
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
variable (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
  (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ)
  (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n)
  (sample : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
  (complete : Fin (BinaryRecovery.tapeSize (n+1))→Bool)
include hδ hSF hS hbound
lemma optionOutput_feasible (w : Option (RationalSampling.State n)) :
    optionOutput δ D F S Δ m hm r0 y0 complete w⊆F ∧
    (optionOutput δ D F S Δ m hm r0 y0 complete w).card=S.card ∧
    (optionOutput δ D F S Δ m hm r0 y0 complete w).Nonempty := by
  cases w with
  | none=>exact ⟨hSF,rfl,hS⟩
  | some s=>
    unfold optionOutput
    simp only [Option.elim_some]
    split_ifs with hp
    · exact BinaryRecovery.result_feasible δ hδ D F S hSF hS Δ (by positivity) hbound s _ _ _ hp r0 y0 complete
    · exact ⟨hSF,rfl,hS⟩
lemma candidates_feasible : ∀ U∈candidates δ D F S Δ P m hm r0 y0 sample complete,
    U⊆F ∧ U.card=S.card ∧ U.Nonempty := by
  intro U hU
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hU
  exact optionOutput_feasible δ hδ D F S hSF hS Δ hbound m hm r0 y0 complete _
lemma result_feasible : result δ D F S Δ P m hm r0 y0 sample complete⊆F ∧
    (result δ D F S Δ P m hm r0 y0 sample complete).card=S.card ∧
    (result δ D F S Δ P m hm r0 y0 sample complete).Nonempty :=
  BinaryMetricBest.best_property δ D S _ _ ⟨hSF,rfl,hS⟩
    (candidates_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 sample complete)
lemma result_cost_le_prefix (i : Fin (2*m+1)) :
    realCost D (result δ D F S Δ P m hm r0 y0 sample complete)≤
      realCost D (optionOutput δ D F S Δ m hm r0 y0 complete (stateAt δ D F S Δ P m sample i)) :=
  BinaryMetricBest.realCost_le_mem δ hδ D S hS _
    (fun U hU=>(candidates_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 sample complete U hU).2.2)
    _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
lemma result_cost_le_start : realCost D (result δ D F S Δ P m hm r0 y0 sample complete)≤realCost D S := by
  rw [←BinaryMetricCost.cost_cast δ hδ D S hS,←BinaryMetricCost.cost_cast δ hδ D _
    (result_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 sample complete).2.2]
  exact_mod_cast BinaryMetricBest.cost_le_self δ D S (candidates δ D F S Δ P m hm r0 y0 sample complete)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
