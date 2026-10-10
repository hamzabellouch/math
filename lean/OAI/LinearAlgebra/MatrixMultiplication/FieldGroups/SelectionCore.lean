import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.SelectionParameters
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitData
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.OrdinarySelection

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupSelection

open MatrixMultiplication.Foundation AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldScheduledYield AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

def orbitPrefactor (allocation : Allocation) (sigma : Placement) : ℕ :=
  3 * (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick)
    allocation + 1) ^ AllFieldGroupOrbitCount.groupDegree K tick sigma

theorem data_orbits_card_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement)
    (e : AllFieldGroupOrbitData.Targets (K := K) (tick := tick) allocation m sigma) :
    ((AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m ε sigma).orbits e).card ≤
      orbitPrefactor (K := K) (tick := tick) allocation sigma *
        (m + 1) ^ AllFieldGroupOrbitCount.groupDegree K tick sigma := by
  have hb := AllFieldGroupOrbitData.orbits_card_le allocation m ε sigma e
  unfold orbitPrefactor
  unfold AllFieldGroupOrbitCount.groupOrbitPrefactor at hb
  exact_mod_cast hb

theorem data_coarse_injective (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) :
    Function.Injective
      (AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m ε sigma).coarse :=
  AllFieldGroupOrbitData.coarse_injective allocation m sigma

structure Selected (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) (slack : ℝ) where
  sample : JointCoarseHashing.Sample
    (AllFieldGroupOrbitData.Pos (K := K) (tick := tick) allocation m sigma)
    (JointOrdinarySelection.hashLevel
      (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
  targets : Finset (AllFieldGroupOrbitData.Targets
    (K := K) (tick := tick) allocation m sigma)
  card_targets : targets.card =
    ⌊Real.exp ((m : ℝ) * (nativeCapacity (K := K) (tick := tick) allocation - slack))⌋₊
  good : ∀ e ∈ targets,
    (AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma).Good
      (JointOrdinarySelection.hashLevel
        (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
      (JointOrdinarySelection.hashSet
        (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
      (m : ℝ) e sample
  distinct_first : ∀ e ∈ targets, ∀ f ∈ targets, e ≠ f →
    (AllFieldGroupOrbitData.coarse (K := K) (tick := tick) allocation m sigma e).1 ≠
      (AllFieldGroupOrbitData.coarse (K := K) (tick := tick) allocation m sigma f).1

end MatrixMultiplication.AllFieldGroupSelection

end

end OAI
