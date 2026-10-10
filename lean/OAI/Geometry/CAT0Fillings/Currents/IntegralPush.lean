import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.PushBoundary
import OAI.Geometry.CAT0Fillings.Charts.Postcompose

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory
open CurrentOperations

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X]
lemma integerRectifiable_push_of_bilipschitz {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {f : X → Y} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hfJ : AntilipschitzWith J f) :
    IntegerRectifiable (pushCurrent f T) := by
  classical
  obtain ⟨C,hdis,hC,hm,heq⟩ := hT
  choose L U hL hU using fun i => (C i).bilipschitz
  let D : ℕ → IntegerChart Y k := fun i => (C i).postcompose hf (hfJ.comp (hU i))
  have hDaction (i : ℕ) : (D i).action = pushCurrent f (C i).action :=
    (C i).postcompose_action hf (hfJ.comp (hU i))
  have hD (i : ℕ) : IsMetricCurrent (D i).action := by
    rw [hDaction]
    exact pushCurrent_isMetricCurrent (hC i) hf
  refine ⟨D,?_,hD,?_,?_⟩
  · intro i j hij
    change Disjoint ((C i).postcompose hf _).image ((C j).postcompose hf _).image
    rw [(C i).postcompose_image,(C j).postcompose_image]
    exact (Set.disjoint_image_iff hfJ.injective).mpr (hdis hij)
  · apply (hm.mul_left ((K : ℝ)^k)).of_nonneg_of_le
    · intro i
      exact mass_nonneg (D i).action
    · intro i
      rw [hDaction]
      exact mass_pushCurrent_le (hC i) hf
  · intro b π
    by_cases h : Admissible b π
    · rw [pushCurrent_apply f T h,heq]
      exact tsum_congr (fun i => by rw [hDaction,pushCurrent_apply f (C i).action h])
    · rw [show pushCurrent f T b π = 0 from ite_eq_right h]
      symm
      calc
        (∑' i, (D i).action b π) = ∑' (_i : ℕ), (0 : ℝ) :=
          tsum_congr (fun i => (hD i).offDomain b π h)
        _ = 0 := tsum_zero

lemma integral_push_of_bilipschitz {k : ℕ} {T : Functional X k}
    (hT : IsIntegral k T) {f : X → Y} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hfJ : AntilipschitzWith J f) :
    IsIntegral k (pushCurrent f T) := by
  cases k with
  | zero => exact ⟨pushCurrent_isMetricCurrent hT.1 hf,
      integerRectifiable_push_of_bilipschitz hT.2 hf hfJ⟩
  | succ k =>
    refine ⟨pushCurrent_isMetricCurrent hT.1 hf,
      integerRectifiable_push_of_bilipschitz hT.2.1 hf hfJ,?_,?_⟩
    · rw [pushCurrent_boundarySucc T hf]
      exact pushCurrent_isMetricCurrent hT.2.2.1 hf
    · rw [pushCurrent_boundarySucc T hf]
      exact integerRectifiable_push_of_bilipschitz hT.2.2.2 hf hfJ

end CAT0Fillings

end
end

end OAI
