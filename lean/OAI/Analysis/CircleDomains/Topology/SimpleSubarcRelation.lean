import OAI.Analysis.CircleDomains.Probability.SimpleArcMeasurability
import OAI.Analysis.CircleDomains.Probability.TerminalPathMeasurability

namespace OAI

/-! The actual Borel relation used to select simple subarcs, including
the endpoint equalities and containment in the original path image. -/

open Set Function MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def simpleSubarcRelation : Set (C(PathTime, X) × C(PathTime, X)) :=
  {p | Injective p.2 ∧ p.2 ⊥ = p.1 ⊥ ∧ p.2 ⊤ = p.1 ⊤ ∧ range p.2 ⊆ range p.1}

variable [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_simpleSubarcRelation :
    MeasurableSet (simpleSubarcRelation (X := X)) := by
  have hs : IsClosed {p : C(PathTime, X) × C(PathTime, X) | p.2 ⊥ = p.1 ⊥} :=
    isClosed_eq ((continuous_eval_const ⊥).comp continuous_snd)
      ((continuous_eval_const ⊥).comp continuous_fst)
  have ht : IsClosed {p : C(PathTime, X) × C(PathTime, X) | p.2 ⊤ = p.1 ⊤} :=
    isClosed_eq ((continuous_eval_const ⊤).comp continuous_snd)
      ((continuous_eval_const ⊤).comp continuous_fst)
  exact (measurableSet_injective_paths.preimage measurable_snd).inter
    (hs.measurableSet.inter (ht.measurableSet.inter isClosed_path_image_containment.measurableSet))

theorem measurableSet_simpleTerminalArcRelation (V : Set X) (hV : IsOpen V) :
    MeasurableSet {p : C(PathTime, X) × C(PathTime, X) |
      (terminalPath p.1 (lastEntryTime p.1 V), p.2) ∈ simpleSubarcRelation} :=
  measurableSet_simpleSubarcRelation.preimage
    (((measurable_lastEntryPath V hV).comp measurable_fst).prodMk measurable_snd)

end CircleDomainRigidity

end OAI
