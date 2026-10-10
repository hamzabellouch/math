import OAI.Analysis.CircleDomains.Topology.PathImageCount
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace OAI

/-! The finite intersection measure of a random path with a closed set.
Closed incidence tests suffice for measurability of the whole measure.
Paths with infinitely many intersections are discarded; they form a null
set whenever the expected total intersection count is finite. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem pathImageCount_eq_count (E : Set X) (hE : MeasurableSet E)
    (γ : C(PathTime, X)) :
    pathImageCount E γ = Measure.count (range γ ∩ E) := by
  have hs : MeasurableSet (range γ ∩ E) :=
    (isCompact_range γ.continuous).isClosed.measurableSet.inter hE
  rw [pathImageCount, Measure.count, Measure.sum_apply _ hs]
  congr 1
  funext x
  rw [Measure.dirac_apply' x hs]
  by_cases hx : x ∈ range γ ∩ E <;> simp [hx]

def pathIntersectionMeasure (H : Set X) (γ : C(PathTime, X)) : Measure X :=
  if pathImageCount H γ < ∞ then Measure.count.restrict (range γ ∩ H) else 0

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem pathIntersectionMeasure_finite (H : Set X) (hH : IsClosed H)
    (γ : C(PathTime, X)) : IsFiniteMeasure (pathIntersectionMeasure H γ) := by
  constructor
  by_cases h : pathImageCount H γ < ∞
  · simpa only [pathIntersectionMeasure, ite_eq_left h, Measure.restrict_apply_univ,
      ← pathImageCount_eq_count H hH.measurableSet γ] using h
  · simp [pathIntersectionMeasure, h]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem pathIntersectionMeasure_apply (H : Set X) (hH : IsClosed H)
    (E : Set X) (hE : MeasurableSet E)
    (γ : C(PathTime, X)) :
    pathIntersectionMeasure H γ E =
      if pathImageCount H γ < ∞ then pathImageCount (H ∩ E) γ else 0 := by
  by_cases h : pathImageCount H γ < ∞
  · rw [pathIntersectionMeasure, ite_eq_left h, ite_eq_left h, Measure.restrict_apply hE]
    rw [pathImageCount_eq_count (H ∩ E)]
    · congr 1
      ext x
      simp only [mem_inter_iff, and_comm, and_left_comm, and_assoc]
    · exact hH.measurableSet.inter hE
  · simp [pathIntersectionMeasure, h]

theorem measurable_pathIntersectionMeasure (H : Set X) (hH : IsClosed H) :
    Measurable (pathIntersectionMeasure H) := by
  let : ∀ γ : C(PathTime, X), IsFiniteMeasure (pathIntersectionMeasure H γ) :=
    pathIntersectionMeasure_finite H hH
  apply Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
  · intro E hE
    simp_rw [pathIntersectionMeasure_apply H hH E hE.measurableSet]
    exact Measurable.ite ((measurable_pathImageCount hH) measurableSet_Iio)
      (measurable_pathImageCount (hH.inter hE)) measurable_const
  · simp_rw [pathIntersectionMeasure_apply H hH univ MeasurableSet.univ,
      inter_univ]
    exact Measurable.ite ((measurable_pathImageCount hH) measurableSet_Iio)
      (measurable_pathImageCount hH) measurable_const

def meanPathIntersectionMeasure (H : Set X) (μ : Measure C(PathTime, X)) : Measure X :=
  μ.bind (pathIntersectionMeasure H)

theorem meanPathIntersectionMeasure_apply (H : Set X) (hH : IsClosed H)
    (μ : Measure C(PathTime, X))
    (hfinite : (∫⁻ γ, pathImageCount H γ ∂μ) < ∞)
    (E : Set X) (hE : MeasurableSet E) :
    meanPathIntersectionMeasure H μ E = ∫⁻ γ, pathImageCount (H ∩ E) γ ∂μ := by
  rw [meanPathIntersectionMeasure,
    Measure.bind_apply hE (measurable_pathIntersectionMeasure H hH).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_lt_top (measurable_pathImageCount hH) hfinite.ne] with γ hγ
  rw [pathIntersectionMeasure_apply H hH E hE, ite_eq_left hγ]

theorem meanPathIntersectionMeasure_finite (H : Set X) (hH : IsClosed H)
    (μ : Measure C(PathTime, X))
    (hfinite : (∫⁻ γ, pathImageCount H γ ∂μ) < ∞) :
    IsFiniteMeasure (meanPathIntersectionMeasure H μ) := by
  constructor
  simpa only [meanPathIntersectionMeasure_apply H hH μ hfinite univ MeasurableSet.univ,
    inter_univ] using hfinite

theorem meanPathIntersectionMeasure_apply_subset (H : Set X) (hH : IsClosed H)
    (μ : Measure C(PathTime, X))
    (hfinite : (∫⁻ γ, pathImageCount H γ ∂μ) < ∞)
    (E : Set X) (hE : MeasurableSet E) (hEH : E ⊆ H) :
    meanPathIntersectionMeasure H μ E = ∫⁻ γ, pathImageCount E γ ∂μ := by
  rw [meanPathIntersectionMeasure_apply H hH μ hfinite E hE,
    inter_eq_right.mpr hEH]

theorem meanPathIntersectionMeasure_map_null
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (a : Y → C(PathTime, X)) (ha : Measurable a)
    (H : Set X) (hH : IsClosed H) (E : Set X) (hE : MeasurableSet E)
    (hmiss : ∀ᵐ y ∂μ, Disjoint (range (a y) ∩ H) E) :
    meanPathIntersectionMeasure H (μ.map a) E = 0 := by
  have hm : Measurable (fun γ => pathIntersectionMeasure H γ E) :=
    (Measure.measurable_coe hE).comp (measurable_pathIntersectionMeasure H hH)
  rw [meanPathIntersectionMeasure, Measure.bind_apply hE
    (measurable_pathIntersectionMeasure H hH).aemeasurable,
    lintegral_map hm ha]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hmiss] with y hy
  by_cases h : pathImageCount H (a y) < ∞
  · rw [pathIntersectionMeasure, ite_eq_left h, Measure.restrict_apply hE]
    have he : E ∩ (range (a y) ∩ H) = ∅ := hy.symm.eq_bot
    rw [he, measure_empty]
    rfl
  · simp [pathIntersectionMeasure, h]

end CircleDomainRigidity

end

end OAI
