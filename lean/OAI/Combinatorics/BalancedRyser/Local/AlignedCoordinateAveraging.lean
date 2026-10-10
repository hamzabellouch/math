import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalProduct
import OAI.Combinatorics.BalancedRyser.Probability.UnusedOffsetAveraging

namespace OAI

namespace Balanced.Local.AlignedGlobal

open TupleAlignment AlignedUnused UniformConditionalProduct

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditionedOffsetProbability_le_of_freeCoordinate_fibers {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) (R : Finset (Fin b))
    (hD : (RootChildPartition.dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (E : MergedPairs F → Prop) (β : ℝ)
    (h : ∀ u : UnusedArray P a,
      ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure
        {x | E ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u)).1}).toReal ≤ β) :
    conditionedOffsetProbability (Aligned P a bits p) E ≤ β := by
  rw [conditioned_probability_eq_uniform_coordinates P hκ R hD a ha bits p E]
  have hs := uniform_map_equiv
    (Equiv.prodComm (UnusedArray P a) (FreeIndex P R → F))
  rw [← hs, PMF.toOuterMeasure_map_apply, uniform_product_eq_bind]
  apply UnusedOffsetIncidence.bind_probability_le
  intro u
  rw [PMF.toOuterMeasure_map_apply]
  exact h u

end
end Balanced.Local.AlignedGlobal

end OAI
