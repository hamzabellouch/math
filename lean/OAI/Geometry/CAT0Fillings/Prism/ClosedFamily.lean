import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.PushBoundary
import OAI.Geometry.CAT0Fillings.Prism.Boundary
import OAI.Geometry.CAT0Fillings.Prism.ClosedCylinder

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
open Set MeasureTheory CurrentOperations
open scoped NNReal ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
noncomputable def closedPrismFamily (C : ℕ → IntegerChart X k) :
    Functional (ClosedCylinder X) (k+1) := pushCurrent cylinderClamp (prismFamily C)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma closedPrismFamily_action (C : ℕ → IntegerChart X k) (b : ClosedCylinder X → ℝ)
    (π : Fin (k+1) → ClosedCylinder X → ℝ) :
    closedPrismFamily C b π = ∑' i, (C i).closedPrism.action b π := by
  simp_rw [IntegerChart.closedPrism_action]
  by_cases hab : Admissible b π
  · simp only [closedPrismFamily,pushCurrent_apply _ _ hab,prismFamily]
  · simp only [closedPrismFamily,pushCurrent,ite_eq_right hab,tsum_zero]

lemma closedPrismFamily_current (C : ℕ → IntegerChart X k)
    (hs : Summable (fun i => mass (C i).action)) : IsMetricCurrent (closedPrismFamily C) :=
  pushCurrent_isMetricCurrent (prismFamily_current C hs) cylinderClamp_lipschitz

lemma closedPrismFamily_rectifiable (C : ℕ → IntegerChart X k)
    (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hs : Summable (fun i => mass (C i).action)) : IntegerRectifiable (closedPrismFamily C) := by
  refine ⟨fun i => (C i).closedPrism,fun i j hij => (C i).closedPrism_image_disjoint (hd hij),
    fun i => (C i).closedPrism.action_isMetricCurrent,?_,closedPrismFamily_action C⟩
  exact (hs.mul_left (k+1:ℝ)).of_nonneg_of_le
    (fun i => mass_nonneg _) (fun i => (C i).mass_closedPrism_le)

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma closedPrismFamily_boundary_cycle {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T) (hz : boundarySucc T = 0)
    (C : ℕ → IntegerChart X (k+1)) (hs : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π)
    (b : ClosedCylinder X → ℝ) (π : Fin (k+1) → ClosedCylinder X → ℝ)
    (hab : Admissible b π) :
    boundarySucc (closedPrismFamily C) b π =
      T (fun x => b (⟨1,by constructor <;> norm_num⟩,x))
        (fun j x => π j (⟨1,by constructor <;> norm_num⟩,x)) -
      T (fun x => b (⟨0,by constructor <;> norm_num⟩,x))
        (fun j x => π j (⟨0,by constructor <;> norm_num⟩,x)) := by
  rw [closedPrismFamily,pushCurrent_boundarySucc _ cylinderClamp_lipschitz,
    pushCurrent_apply _ _ hab,
    prismFamily_boundary_cycle hT hrect hz C hs heq _ _
      (admissible_comp hab cylinderClamp_lipschitz)]
  simp only [Function.comp_apply,cylinderClamp,projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num),
    projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1)
    (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)]

end CAT0Fillings

end
end

end OAI
