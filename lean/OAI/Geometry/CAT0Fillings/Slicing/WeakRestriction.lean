import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.NormalRestriction

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

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
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable
open BorelCoefficients BorelRestriction MassMeasure

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {k : ℕ}

end CAT0Fillings

open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter SmoothCutoff BorelCoefficients BorelRestriction MassMeasure Foundations
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

noncomputable def levelBarrier (a : ℝ≥0) (t : ℝ) (u : X → ℝ) (x : X) : ℝ :=
  1-profile a 0 |u x-t|

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelBarrier_bounds (a : ℝ≥0) (t : ℝ) (u : X → ℝ) (x : X) :
    0 ≤ levelBarrier a t u x ∧ levelBarrier a t u x ≤ 1 := by
  have hp := profile_bounds a 0 |u x-t|
  dsimp only [levelBarrier]
  constructor <;> linarith [hp.1,hp.2]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelBarrier_boundedLip {u : X → ℝ} (hu : BoundedLip u) (a : ℝ≥0) (t : ℝ) :
    BoundedLip (levelBarrier a t u) := by
  obtain ⟨K,hK⟩ := hu.1
  have hv : BoundedLip (fun x => |u x-t|) := by
    obtain ⟨M,hM⟩ := hu.2
    refine ⟨⟨K,?_⟩, M+|t|, fun x => ?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq]
      calc
        _ ≤ |(u x-t)-(u y-t)| := abs_abs_sub_abs_le_abs_sub _ _
        _ = dist (u x) (u y) := by rw [Real.dist_eq]; congr 1; ring
        _ ≤ K*dist x y := hK.dist_le_mul x y
    · rw [abs_abs]
      exact (abs_sub (u x) t).trans (by linarith [hM x])
  have h := (BoundedLip.const (X := X) 1).add
    ((profile_comp_boundedLip hv a 0).const_mul (-1))
  change BoundedLip (fun x => 1-profile a 0 |u x-t|)
  simpa only [Function.comp_def,neg_one_mul,sub_eq_add_neg] using h

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma profile_error_le_levelBarrier (a : ℝ≥0) (t : ℝ) (u : X → ℝ) (x : X) :
    |profile a t (u x)-({x | t < u x}.indicator (fun _ => (1:ℝ)) x)| ≤
      levelBarrier a t u x := by
  by_cases hx : t < u x
  · rw [indicator_of_mem (show x ∈ {x | t < u x} from hx),abs_of_nonpos (by linarith [(profile_bounds a t (u x)).2])]
    dsimp only [levelBarrier,profile]
    rw [abs_of_pos (sub_pos.mpr hx),sub_zero]
    linarith
  · rw [indicator_of_notMem (show x ∉ {x | t < u x} from hx),profile_zero a (le_of_not_gt hx),sub_self,abs_zero]
    exact (levelBarrier_bounds a t u x).1

omit [CompactSpace X] in
lemma levelBarrier_integral_tendsto (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ) (ht : μ {x | u x = t} = 0) :
    Tendsto (fun n : ℕ => ∫ x, levelBarrier ((n:ℝ≥0)+1) t u x ∂μ) atTop (𝓝 0) := by
  have hne : ∀ᵐ x ∂μ, u x ≠ t := by simpa only [ae_iff,not_not] using ht
  have hpt : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => levelBarrier ((n:ℝ≥0)+1) t u x) atTop (𝓝 0) := by
    filter_upwards [hne] with x hx
    have hpos : 0 < |u x-t| := abs_pos.mpr (sub_ne_zero.mpr hx)
    have hp : Tendsto (fun n : ℕ => profile ((n:ℝ≥0)+1) 0 |u x-t|) atTop (𝓝 1) := by
      simpa only [indicator_of_mem (show |u x-t| ∈ Ioi 0 from hpos)] using profile_sequence_tendsto 0 |u x-t|
    simpa only [levelBarrier,sub_self] using (tendsto_const_nhds (x := (1:ℝ))).sub hp
  have hdom (n : ℕ) : ∀ᵐ x ∂μ, ‖levelBarrier ((n:ℝ≥0)+1) t u x‖ ≤ (1:ℝ) := by
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (levelBarrier_bounds _ _ _ _).1]
      exact (levelBarrier_bounds _ _ _ _).2
  have hh := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ => (1:ℝ)) (fun n => (levelBarrier_boundedLip hu _ t).continuous.aestronglyMeasurable)
    (integrable_const _) hdom hpt
  simpa only [integral_zero] using hh

lemma restrictCurrent_apply_of_controls {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {E : Set X} (hE : MeasurableSet E) {b : X → ℝ} {π : Fin k → X → ℝ}
    (hab : Admissible b π) :
    restrictCurrent hT E b π = borelAction μ hT (E.indicator b) π := by
  rw [restrictCurrent_apply hT E hab]
  exact borelAction_independent _ hT (currentMassMeasure_controls hT) hμ
    ((integrable_boundedLip _ hab.1).indicator hE)
    ((integrable_boundedLip _ hab.1).indicator hE) π hab.2

lemma restriction_profile_error_bound {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {u : X → ℝ} (hu : BoundedLip u) (a : ℝ≥0) (t : ℝ)
    {b : X → ℝ} (hb : BoundedLip b) (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) (M : ℝ) (hM : ∀ x, |b x| ≤ M) :
    |restrictCurrent hT {x | t < u x} b π - T (fun x => profile a t (u x)*b x) π| ≤
      ((∏ i, (K i : ℝ))*M) * ∫ x, levelBarrier a t u x ∂μ := by
  have hab : Admissible b π := ⟨hb,fun i => ⟨K i,hK i⟩⟩
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
  have hpb : BoundedLip (fun x => profile a t (u x)*b x) := (profile_comp_boundedLip hu a t).mul hb
  rw [restrictCurrent_apply_of_controls hT μ hμ hE hab,
    ←borelAction_eq μ hT hμ ⟨hpb,hab.2⟩]
  apply (borelAction_difference_bound μ hT hμ ((integrable_boundedLip μ hb).indicator hE)
    (integrable_boundedLip μ hpb) π K hK).trans
  have hi : ∫ x, |({x | t < u x}.indicator b x)-profile a t (u x)*b x| ∂μ ≤
      M*∫ x, levelBarrier a t u x ∂μ := by
    rw [←integral_const_mul]
    apply integral_mono ((integrable_boundedLip μ hb).indicator hE |>.sub
      (integrable_boundedLip μ hpb) |>.abs)
      ((integrable_boundedLip μ (levelBarrier_boundedLip hu a t)).const_mul M)
    intro x
    have he : ({x | t < u x}.indicator b x)-profile a t (u x)*b x =
        (profile a t (u x)-({x | t < u x}.indicator (fun _ => (1:ℝ)) x)) * (-b x) := by
      by_cases hx : t < u x <;> simp [hx]
      ring
    change |({x | t < u x}.indicator b x)-profile a t (u x)*b x| ≤ M*levelBarrier a t u x
    rw [he,abs_mul,abs_neg,mul_comm]
    exact mul_le_mul (hM x) (profile_error_le_levelBarrier a t u x) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hM x))
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)

theorem restrictCurrent_weak_tendsto {ι : Type*} {l : Filter ι} {k : ℕ}
    {Ts : ι → Functional X k} {T : Functional X k}
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hT : IsMetricCurrent T)
    (μs : ι → FiniteMeasure X) (μ : FiniteMeasure X)
    (hμs : ∀ j, Controls (Ts j) (μs j)) (hμ : Controls T μ)
    (hμlim : Tendsto μs l (𝓝 μ))
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π)))
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ) (ht : (μ : Measure X) {x | u x = t} = 0)
    (b : X → ℝ) (π : Fin k → X → ℝ) :
    Tendsto (fun j => restrictCurrent (hTs j) {x | t < u x} b π) l
      (𝓝 (restrictCurrent hT {x | t < u x} b π)) := by
  by_cases hab : Admissible b π
  swap
  · simp only [restrictCurrent,ite_eq_right hab]
    exact tendsto_const_nhds
  choose K hK using hab.2
  obtain ⟨M,hM⟩ := hab.1.2
  let C := (∏ i, (K i : ℝ)) * max M 0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (x : X) : |b x| ≤ max M 0 := (hM x).trans (le_max_left _ _)
  let P (n : ℕ) (U : Functional X k) := U (fun x => profile ((n:ℝ≥0)+1) t (u x)*b x) π
  let A (n : ℕ) (ν : FiniteMeasure X) := C*∫ x, levelBarrier ((n:ℝ≥0)+1) t u x ∂(ν : Measure X)
  have hA : Tendsto (fun n => A n μ) atTop (𝓝 0) := by
    simpa only [A,mul_zero] using (levelBarrier_integral_tendsto (μ : Measure X) hu t ht).const_mul C
  have hAlim (n : ℕ) : Tendsto (fun j => A n (μs j)) l (𝓝 (A n μ)) := by
    let f : C(X,ℝ) := ⟨levelBarrier ((n:ℝ≥0)+1) t u,(levelBarrier_boundedLip hu _ t).continuous⟩
    exact ((FiniteMeasure.continuous_integral_continuousMap f).tendsto μ |>.comp hμlim).const_mul C
  have hbT (n : ℕ) : dist (restrictCurrent hT {x | t < u x} b π) (P n T) ≤ A n μ :=
    restriction_profile_error_bound hT μ hμ hu _ t hab.1 π K hK _ hbound
  have hbTs (n : ℕ) (j : ι) : dist (restrictCurrent (hTs j) {x | t < u x} b π) (P n (Ts j)) ≤ A n (μs j) :=
    restriction_profile_error_bound (hTs j) (μs j) (hμs j) hu _ t hab.1 π K hK _ hbound
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n,hn⟩ := ((hA.eventually (gt_mem_nhds (show (0:ℝ) < ε/4 by positivity))).exists)
  have he1 : ∀ᶠ j in l, A n (μs j) < ε/3 :=
    (hAlim n).eventually (gt_mem_nhds (show A n μ < ε/3 by linarith))
  have he2 : ∀ᶠ j in l, dist (P n (Ts j)) (P n T) < ε/3 :=
    Metric.tendsto_nhds.mp (hlim _ _) (ε/3) (by positivity)
  filter_upwards [he1,he2] with j hj1 hj2
  have htri := dist_triangle (restrictCurrent (hTs j) {x | t < u x} b π) (P n (Ts j)) (P n T)
  have htri2 := dist_triangle (restrictCurrent (hTs j) {x | t < u x} b π) (P n T)
    (restrictCurrent hT {x | t < u x} b π)
  have hb := hbT n
  rw [dist_comm] at hb
  linarith [hbTs n j]

end CAT0Fillings.Slicing

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
