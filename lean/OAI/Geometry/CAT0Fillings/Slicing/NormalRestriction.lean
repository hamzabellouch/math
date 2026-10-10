import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.DomainRestriction
import OAI.Geometry.CAT0Fillings.Currents.Composition
import OAI.Geometry.CAT0Fillings.Slicing.Profiles
import OAI.Geometry.CAT0Fillings.Slicing.StripMass

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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter BorelCoefficients BorelRestriction MassMeasure SmoothCutoff
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
lemma controls_from_bounded_measures {ι : Type*} {l : Filter ι} [NeBot l]
    {k : ℕ} {Ts : ι → Functional X k} {T : Functional X k}
    (μs : ι → Measure X) [∀ j, IsFiniteMeasure (μs j)] (M : ℝ≥0)
    (hb : ∀ j, (μs j).real univ ≤ M) (hc : ∀ j, Controls (Ts j) (μs j))
    (hlim : ∀ b π, Admissible b π → Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls T μ := by
  let νs : ι → FiniteMeasure X := fun j => ⟨μs j,inferInstance⟩
  have hb' : ∀ j, νs j ∈ {ν : FiniteMeasure X | ν.mass ≤ M} := by
    intro j
    apply NNReal.coe_le_coe.mp
    exact hb j
  obtain ⟨ν,_,hcluster⟩ :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace X M).exists_mapClusterPt_of_frequently
      (l := l) (Eventually.of_forall hb').frequently
  let l' := comap νs (𝓝 ν) ⊓ l
  have hl' : NeBot l' := neBot_inf_comap_iff_map'.mpr hcluster
  let := hl'
  have hν : Tendsto νs l' (𝓝 ν) := tendsto_iff_comap.mpr inf_le_left
  exact ⟨ν,inferInstance,controls_of_weak_limits hν hc
    (fun b π h => (hlim b π h).mono_left inf_le_right)⟩

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma profile_comp_boundedLip {u : X → ℝ} (hu : BoundedLip u)
    (a : ℝ≥0) (t : ℝ) : BoundedLip (profile a t ∘ u) := by
  obtain ⟨K,hK⟩ := hu.1
  obtain ⟨C,hC⟩ := exists_profile_bounds
  refine ⟨⟨_,(hC a t).1.comp hK⟩,1,fun x => ?_⟩
  change |profile a t (u x)| ≤ 1
  rw [abs_of_nonneg (profile_bounds a t (u x)).1]
  exact (profile_bounds a t (u x)).2

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma dprofile_comp_boundedLip {u : X → ℝ} (hu : BoundedLip u)
    (a : ℝ≥0) (t : ℝ) : BoundedLip (dprofile a t ∘ u) := by
  obtain ⟨K,hK⟩ := hu.1
  obtain ⟨C,hC⟩ := exists_profile_bounds
  refine ⟨⟨_,(hC a t).2.1.comp hK⟩,(C*a:ℝ≥0),fun x => ?_⟩
  exact (hC a t).2.2 (u x)

lemma profile_L1_tendsto (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ}
    (hu : BoundedLip u) (t : ℝ) :
    Tendsto (fun n : ℕ => ∫ x, |profile ((n:ℝ≥0)+1) t (u x) -
      ({x | t < u x}.indicator (fun _ => (1:ℝ)) x)| ∂μ) atTop (𝓝 0) := by
  let E : Set X := {x | t < u x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hu.continuous.measurable
  have hI : Integrable (E.indicator (fun _ : X => (1:ℝ))) μ :=
    (integrable_const _).indicator hE
  have hP (n : ℕ) : Integrable (fun x => profile ((n:ℝ≥0)+1) t (u x)) μ :=
    integrable_boundedLip μ (profile_comp_boundedLip hu _ t)
  have hpt (x : X) : Tendsto (fun n : ℕ => profile ((n:ℝ≥0)+1) t (u x)) atTop
      (𝓝 (E.indicator (fun _ => (1:ℝ)) x)) := by
    simpa only [E,indicator_apply,mem_Ioi,mem_ofPred_eq] using profile_sequence_tendsto t (u x)
  have hdom (n : ℕ) : ∀ᵐ x ∂μ,
      ‖|profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x|‖ ≤ (2:ℝ) := by
    filter_upwards [] with x
    have hp := profile_bounds ((n:ℝ≥0)+1) t (u x)
    have hi : 0 ≤ E.indicator (fun _ => (1:ℝ)) x ∧ E.indicator (fun _ => (1:ℝ)) x ≤ 1 := by
      by_cases hx : x ∈ E <;> simp [hx]
    simpa only [Real.norm_eq_abs,abs_abs] using
      (abs_le.mpr (show -2 ≤ profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x ∧
        profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x ≤ 2 from by
          constructor <;> linarith [hp.1,hp.2,hi.1,hi.2]))
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => |profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x|)
    (f := fun _ => (0:ℝ)) (fun _ => (2:ℝ))
    (fun n => ((hP n).sub hI).abs.aestronglyMeasurable) (integrable_const _) hdom
    (Eventually.of_forall fun x => by
      simpa only [sub_self,abs_zero] using ((hpt x).sub (tendsto_const_nhds (x := E.indicator (fun _ => (1:ℝ)) x))).abs)
  simpa only [integral_zero] using h

lemma profile_boundary_tendsto {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) {u : X → ℝ} (hu : BoundedLip u) (t : ℝ)
    (b : X → ℝ) (π : Fin k → X → ℝ) (hab : Admissible b π) :
    Tendsto (fun n : ℕ => boundarySucc (weightedCurrent (currentMassMeasure hT) hT
      (profile ((n:ℝ≥0)+1) t ∘ u)) b π) atTop
      (𝓝 (boundarySucc (restrictCurrent hT {x | t < u x}) b π)) := by
  let μ := currentMassMeasure hT
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
  have hcons : Admissible (fun _ : X => (1:ℝ)) (Matrix.vecCons b π) :=
    ⟨BoundedLip.const 1,fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩
  simp only [boundarySucc,ite_eq_left hab,weightedCurrent,ite_eq_left hcons,mul_one,
    restrictCurrent,Function.comp_apply]
  exact borelAction_tendsto μ hT (currentMassMeasure_controls hT)
    ((integrable_const _).indicator hE)
    (fun n => integrable_boundedLip μ (profile_comp_boundedLip hu _ t))
    (profile_L1_tendsto μ hu t) (Matrix.vecCons b π) hcons.2

theorem ae_finite_boundary_restrict_cycle {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T) (hz : IsCycle T)
    {u : X → ℝ} (hu : BoundedLip u) :
    ∀ᵐ t : ℝ, ∃ ν : Measure X, IsFiniteMeasure ν ∧
      Controls (boundarySucc (restrictCurrent hT {x | t < u x})) ν := by
  let μ := currentMassMeasure hT
  obtain ⟨K,hK⟩ := hu.1
  obtain ⟨C,hC⟩ := exists_profile_bounds
  filter_upwards [ae_bounded_strip_subsequence μ hu.continuous.measurable] with t ht
  obtain ⟨j,M,hj,hM⟩ := ht
  let a : ℕ → ℝ≥0 := fun n => (j n:ℝ≥0)+1
  let E : ℕ → Set X := fun n => {x | t ≤ u x ∧ u x ≤ t+(a n:ℝ)⁻¹}
  have hE (n) : MeasurableSet (E n) :=
    (measurableSet_le measurable_const hu.continuous.measurable).inter
      (measurableSet_le hu.continuous.measurable measurable_const)
  let ν : ℕ → Measure X := fun n => (K*(C*a n)) • μ.restrict (E n)
  have hνfin : ∀ n, IsFiniteMeasure (ν n) := fun _ => inferInstance
  let := hνfin
  apply controls_from_bounded_measures (l := atTop) ν (K*C*M)
    (Ts := fun n => boundarySucc (weightedCurrent μ hT (profile (a n) t ∘ u)))
  · intro n
    have hen : ν n univ ≤ (K*C*M:ℝ≥0) := by
      calc
        ν n univ = (K*C:ℝ≥0) * stripMass μ u (a n) t := by
          simp only [ν,E,stripMass,Measure.smul_apply,Measure.restrict_apply_univ]
          simp only [ENNReal.smul_def,smul_eq_mul,ENNReal.coe_mul]
          ring
        _ ≤ (K*C:ℝ≥0) * (M:ℝ≥0∞) := mul_le_mul_right (hM n) _
        _ = (K*C*M:ℝ≥0) := by simp only [ENNReal.coe_mul]
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top hen).trans_eq (by simp)
  · intro n
    exact weightedCurrent_comp_boundary_controls hT hrect hz μ (currentMassMeasure_controls hT)
      hu hK (profile_hasDerivAt (a n) t) (profile_comp_boundedLip hu _ t)
      (dprofile_comp_boundedLip hu _ t) (hE n) (fun x => (hC (a n) t).2.2 (u x))
      (fun x hx => dprofile_zero (by dsimp [a]; positivity) hx)
  · intro b π hab
    exact (profile_boundary_tendsto hT hu t b π hab).comp hj

theorem ae_normal_restrict_cycle [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T) (hz : IsCycle T)
    {u : X → ℝ} (hu : BoundedLip u) :
    ∀ᵐ t : ℝ, IsMetricCurrent (restrictCurrent hT {x | t < u x}) ∧
      IntegerRectifiable (restrictCurrent hT {x | t < u x}) ∧
      IsMetricCurrent (boundarySucc (restrictCurrent hT {x | t < u x})) := by
  filter_upwards [ae_finite_boundary_restrict_cycle hT hrect hz hu] with t ht
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
  have hR := restrictCurrent_isMetricCurrent hT hE
  have hrectR := integerRectifiable_restrict hT hrect hE
  exact ⟨hR,hrectR,boundary_isMetricCurrent_of_finiteMass hR hrectR ht⟩

end CAT0Fillings.Slicing
open Set MeasureTheory Filter
open scoped Topology NNReal

end

end OAI
