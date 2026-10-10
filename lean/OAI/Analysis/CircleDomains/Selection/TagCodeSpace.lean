import OAI.Analysis.CircleDomains.Selection.TagValidity
import OAI.Analysis.CircleDomains.Selection.ResidualConstraints
import OAI.Analysis.CircleDomains.Topology.PathEndpoints

namespace OAI

/-! Standard Borel ambient codes and Borel simultaneous tag rules. -/

open Set MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

instance : IsCompletelyMetrizableSpace TagSlot := by
  let : ∀ n : ℕ, IsCompletelyMetrizableSpace (TagParameters n) := fun _ => by infer_instance
  let : IsCompletelyMetrizableSpace TagData := by infer_instance
  change IsCompletelyMetrizableSpace (Unit ⊕ TagData)
  infer_instance

instance : PolishSpace TagSlot := by infer_instance

variable {X : Type*} [MetricSpace X]

def TagRules (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) : Prop :=
  ∀ k : ℕ, (Γ.1, Γ.2 k) ∈ validTagShape ∧
    (Γ.1, Γ.2 k) ∈ tagContainment H ∧ Γ.2 k ∉ tagTupleExcluded N

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_tagRules {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i))
    {N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (hN : ∀ n l, MeasurableSet (N n l)) :
    MeasurableSet {Γ : TaggedPath X | TagRules H N Γ} := by
  simp only [TagRules, ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  have hc : Continuous (fun Γ : TaggedPath X => (Γ.1, Γ.2 k)) :=
    continuous_fst.prodMk ((continuous_apply k).comp continuous_snd)
  exact ((isOpen_validTagShape.measurableSet).preimage hc.measurable).inter
    (((isClosed_tagContainment hH).measurableSet.preimage hc.measurable).inter
      ((measurableSet_tagTupleExcluded hN).compl.preimage
        (((continuous_apply k).comp continuous_snd).measurable)))

instance [CompleteSpace X] [SecondCountableTopology X] : StandardBorelSpace (TaggedPath X) := by
  let : PolishSpace C(PathTime, X) := by infer_instance
  infer_instance

theorem standardBorel_tagRuleCodes [CompleteSpace X] [SecondCountableTopology X]
    {H : ℕ → Set (UnitAddCircle × X)} (hH : ∀ i, IsClosed (H i))
    {N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (hN : ∀ n l, MeasurableSet (N n l)) :
    StandardBorelSpace {Γ : TaggedPath X | TagRules H N Γ} :=
  (measurableSet_tagRules hH hN).standardBorel

end CircleDomainRigidity

end

end OAI
