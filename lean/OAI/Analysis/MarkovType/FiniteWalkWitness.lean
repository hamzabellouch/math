import OAI.Analysis.MarkovType.OrderedNorm
import OAI.Analysis.MarkovType.MarkedChains

namespace OAI

namespace MarkovSuperreflexivity

structure FiniteWalkWitness (N : OrderedNorm) (n : ℕ) where
  State : Type
  Edge : Type
  stateFintype : Fintype State
  edgeFintype : Fintype Edge
  chain : @FiniteMarkedChain State Edge stateFintype edgeFintype
  coordinateBound : ℕ
  label : Edge → C00
  odd : ∀ e, label (chain.rev e) = -label e
  support_bound : ∀ e k, coordinateBound ≤ k → label e k = 0
  unit : ∀ e, N (label e) = 1
  escape : (3 : ℝ) / 20 ≤
    @markedProb State Edge stateFintype edgeFintype chain n
      (fun ω => (n : ℝ) / 24 ≤ N (edgeSum label ω))

end MarkovSuperreflexivity

end OAI
