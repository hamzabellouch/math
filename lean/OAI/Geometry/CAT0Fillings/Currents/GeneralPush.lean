import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.FullRank
import OAI.Geometry.CAT0Fillings.Slicing.RectifiableCoarea
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
open Set MeasureTheory Filter BorelRestriction CurrentOperations
open scoped Topology

namespace IntegerChart
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [Nonempty X] [Nonempty Y] {k : ℕ} (C : IntegerChart X k)
theorem push_integerRectifiable (hC : IsMetricCurrent C.action)
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IntegerRectifiable (pushCurrent f C.action) := by
  classical
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨t,J,hts,ht,hd,hbilip,hzero⟩ :=
    MetricDifferentiation.exists_lipschitz_chart_decomposition C.borel C.bounded.measure_lt_top.ne (hf.comp hL)
  let E i := C.paramExtended '' t i
  have hE i : MeasurableSet (E i) := C.measurableSet_paramExtended_image (ht i) (hts i)
  have hEd : Pairwise (fun i j => Disjoint (E i) (E j)) :=
    fun i j hij => C.paramExtended_disjoint_images (hts i) (hts j) (hd hij)
  let R i := C.restrictDomain (ht i) (hts i)
  have hR i : IsMetricCurrent (R i).action := C.restrictDomain_isMetricCurrent _ _ hC
  have hRact i : (R i).action = restrictCurrent hC (E i) := C.restrictDomain_action _ _ hC
  let D i := (R i).postcompose hf (hbilip i).2
  have hDact i : (D i).action = pushCurrent f (R i).action := (R i).postcompose_action hf (hbilip i).2
  have hD i : IsMetricCurrent (D i).action := by rw [hDact]; exact pushCurrent_isMetricCurrent (hR i) hf
  have hRs : Summable (fun i => mass (R i).action) := by
    simp_rw [hRact]
    exact summable_restriction_mass hC E hE hEd
  have hDs : Summable (fun i => mass (D i).action) := by
    apply (hRs.mul_left ((K : ℝ)^k)).of_nonneg_of_le (fun i => mass_nonneg _)
    intro i
    rw [hDact]
    exact mass_pushCurrent_le (hR i) hf
  have heq : pushCurrent f C.action = fun b π => ∑' i, (D i).action b π := by
    funext b π
    by_cases hab : Admissible b π
    · simp_rw [hDact,pushCurrent_apply f _ hab,hRact]
      rw [←restrictCurrent_iUnion hC E hE hEd,
        ←C.restrictMultiplicity_action hC (MeasurableSet.iUnion hE)]
      rw [action,action,ite_eq_left (admissible_comp hab hf),ite_eq_left (admissible_comp hab hf)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem C.borel,hzero π hab.2] with z hz hzeroz
      change (C.multiplicity z : ℝ)*C.scalar (b ∘ f) z*C.jacobian (fun i => π i ∘ f) z =
        ↑((C.paramExtended ⁻¹' ⋃ i, E i).indicator C.multiplicity z)*
          C.scalar (b ∘ f) z*C.jacobian (fun i => π i ∘ f) z
      by_cases hzi : z ∈ ⋃ i, t i
      · have him : z ∈ C.paramExtended ⁻¹' ⋃ i, E i := by
          obtain ⟨i,hi⟩ := mem_iUnion.mp hzi
          exact mem_iUnion.mpr ⟨i,⟨z,hi,rfl⟩⟩
        rw [indicator_of_mem him]
      · have hj : C.jacobian (fun i => π i ∘ f) z = 0 := hzeroz hzi
        rw [hj,mul_zero,mul_zero]
    · rw [(pushCurrent_isMetricCurrent hC hf).offDomain b π hab]
      symm
      calc (∑' i, (D i).action b π) = ∑' (_i : ℕ), (0 : ℝ) :=
              tsum_congr fun i => (hD i).offDomain b π hab
        _ = 0 := tsum_zero
  rw [heq]
  exact integerRectifiable_chartSum D hD hDs

end IntegerChart
end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter CurrentOperations

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [Nonempty X] [Nonempty Y] {k : ℕ}

theorem integerRectifiable_push {T : Functional X k} (hT : IntegerRectifiable T)
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IntegerRectifiable (pushCurrent f T) := by
  classical
  obtain ⟨C,hd,hC,hCS,heq⟩ := hT
  have hP i : IsMetricCurrent (pushCurrent f (C i).action) := pushCurrent_isMetricCurrent (hC i) hf
  have hPI i : IntegerRectifiable (pushCurrent f (C i).action) := (C i).push_integerRectifiable (hC i) hf
  have hPS : Summable (fun i => mass (pushCurrent f (C i).action)) :=
    (hCS.mul_left ((K : ℝ)^k)).of_nonneg_of_le (fun i => mass_nonneg _) (fun i => mass_pushCurrent_le (hC i) hf)
  have hEq : pushCurrent f T = (fun b π => ∑' i, pushCurrent f (C i).action b π) := by
    funext b π
    by_cases hab : Admissible b π
    · simp_rw [pushCurrent_apply f _ hab]
      exact heq _ _
    · simp only [pushCurrent,ite_eq_right hab,tsum_zero]
  rw [hEq]
  exact integerRectifiable_tsum hP hPI hPS

theorem integral_push {T : Functional X k} (hT : IsIntegral k T)
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IsIntegral k (pushCurrent f T) := by
  cases k with
  | zero => exact ⟨pushCurrent_isMetricCurrent hT.1 hf,integerRectifiable_push hT.2 hf⟩
  | succ k =>
    refine ⟨pushCurrent_isMetricCurrent hT.1 hf,integerRectifiable_push hT.2.1 hf,?_,?_⟩
    · rw [pushCurrent_boundarySucc T hf]
      exact pushCurrent_isMetricCurrent hT.2.2.1 hf
    · rw [pushCurrent_boundarySucc T hf]
      exact integerRectifiable_push hT.2.2.2 hf

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

end
end

end OAI
