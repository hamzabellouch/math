import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.CycleFTC
import OAI.Geometry.CAT0Fillings.Prism.TimeAction

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory Measure Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
lemma prismFamily_boundary_cycle {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T) (hz : IsCycle T)
    (C : ℕ → IntegerChart X (k+1)) (hs : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π)
    (b : ℝ × X → ℝ) (π : Fin (k+1) → ℝ × X → ℝ) (hab : Admissible b π) :
    boundarySucc (prismFamily C) b π =
      T (fun x => b (1,x)) (fun j x => π j (1,x)) -
      T (fun x => b (0,x)) (fun j x => π j (0,x)) := by
  let v : Fin (k+2) → ℝ × X → ℝ := Matrix.vecCons b π
  have hV : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (v i) := by
    intro i
    exact Fin.cases hab.1.1 (fun j => hab.2 j) i
  choose K hK using hV
  let L : ℝ≥0 := ∑ i, K i
  have hL i : LipschitzWith L (v i) :=
    (hK i).weaken (Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ i))
  obtain ⟨μ,hfin,hμ,hformula⟩ := prismFamily_action_one hT C hs heq v L hL
  let : IsFiniteMeasure μ := hfin
  rw [boundarySucc,ite_eq_left hab,hformula]
  exact hT.cycle_time_FTC hrect hz μ hμ v L hL 0 1

end CAT0Fillings
namespace CAT0Fillings
namespace CurrentOperations
attribute [local instance] Classical.propDecidable

universe u

variable {X : Type u} {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

end CurrentOperations
end CAT0Fillings

end
end

end OAI
