import OAI.Probability.SwitchChain.Definitions
import OAI.Probability.SwitchChain.HavelConnectivity
import OAI.Probability.SwitchChain.MainFromGap
import OAI.Probability.SwitchChain.ActualTripleSquare
import OAI.Probability.SwitchChain.LocalGapEndgame
import OAI.Probability.SwitchChain.PairDisjointAssembly
import OAI.Probability.SwitchChain.PairActualAffine
import OAI.Probability.SwitchChain.PairEqualityBudgetUnordered

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315

theorem switch_chain_main :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → ((∃ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h ≤ 2 * n ^ 8) ∧ (stateCount n d = 1 → (MixedAt n d 0 ∧ ∀ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h = 0)) ∧ (1 < stateCount n d → hasSpectralGapAtLeast n d ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))) := by
  intro n d hn hd hgraph
  apply switch_chain_main_of_spectralGap n d hn
  intro hmany
  apply PairResampling.spectralGap_of_triples_and_disjoint hn hgraph
    PairResampling.tripleGenerator_square
  intro f
  exact PairResampling.disjoint_sum_nonneg_of_named_interaction_budget f
    (fun i j k l h => PairEquality.actual_named_interaction i j k l h f)
    (fun a _ => PairEquality.pair_projection_budget a f)

theorem switch_chain_tv_bound :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → 1 < stateCount n d → ∀ (t : Nat) (G : GraphState n d), tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 * Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  intro n d hn hd hgraph hmany t G
  exact switch_chain_tv_bound_of_spectralGap n d hn
    ((switch_chain_main n d hn hd hgraph).2.2 hmany) t G

theorem switch_connectivity :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → ∀ G H : GraphState n d, Relation.ReflTransGen (SwitchStep n d) G H := by
  intro n d _ _ _ G H
  exact switch_connectivity_direct n d G H

end Problem315

end

end OAI
