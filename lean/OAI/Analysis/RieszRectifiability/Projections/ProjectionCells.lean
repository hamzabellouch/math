import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.DyadicBoxes
import OAI.Analysis.RieszRectifiability.Limits.WeakCellMass

namespace OAI

/-!
# Measures on parametrized boxes

Restricting Lebesgue measure to a finite box and pushing it forward through a
parametrization defines the associated box-plane measure. Its finite-measure
packaging allows these parametrized cells to enter weak-convergence arguments.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

def boxPlaneMeasure (I : Box ι) (e : (ι → ℝ) → X) : Measure X :=
  (volume.restrict (I : Set (ι → ℝ))).map e

instance (I : Box ι) (e : (ι → ℝ) → X) : IsFiniteMeasure (boxPlaneMeasure I e) := by
  let : IsFiniteMeasure (volume.restrict (I : Set (ι → ℝ))) :=
    isFiniteMeasure_restrict.mpr (I.measure_coe_lt_top volume).ne
  unfold boxPlaneMeasure
  infer_instance

def boxPlaneFiniteMeasure (I : Box ι) (e : (ι → ℝ) → X) : FiniteMeasure X :=
  ⟨boxPlaneMeasure I e, inferInstance⟩

theorem boxPlaneMeasure_univ (I : Box ι) (e : (ι → ℝ) → X) (he : Measurable e) :
    boxPlaneMeasure I e univ = (volume : Measure (ι → ℝ)) I := by
  rw [boxPlaneMeasure, Measure.map_apply he MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

theorem boxPlaneFiniteMeasure_ne_zero (I : Box ι) (e : (ι → ℝ) → X)
    (he : Measurable e) : boxPlaneFiniteMeasure I e ≠ 0 := by
  intro h
  have heq : boxPlaneMeasure I e = 0 :=
    congrArg (fun ν : FiniteMeasure X => (ν : Measure X)) h
  have hv : (volume : Measure (ι → ℝ)).real I = 0 := by
    rw [Measure.real, ← boxPlaneMeasure_univ I e he, heq]
    simp
  exact (box_volume_real_pos I).ne' hv

theorem boxPlaneMeasure_preimage (I : Box ι) (e : (ι → ℝ) → X) (π : X → ι → ℝ)
    (he : Measurable e) (hπ : Measurable π) (hleft : LeftInverse π e)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) :
    boxPlaneMeasure I e (π ⁻¹' s) = (volume : Measure (ι → ℝ)) (s ∩ I) := by
  rw [boxPlaneMeasure, Measure.map_apply he (hs.preimage hπ)]
  have hp : e ⁻¹' (π ⁻¹' s) = s := by
    ext x
    simp only [mem_preimage, hleft x]
  rw [hp, Measure.restrict_apply hs]

def dyadicProjectionCell (I : Box ι) (π : X → ι → ℝ) (k : ℕ)
    (J : DyadicBoxIndex I k) : Set X := π ⁻¹' dyadicBoxCell I k J

theorem dyadicProjectionCell_measurable (I : Box ι) (π : X → ι → ℝ)
    (hπ : Measurable π) (k : ℕ) (J : DyadicBoxIndex I k) :
    MeasurableSet (dyadicProjectionCell I π k J) :=
  (dyadicBoxCell_measurable I k J).preimage hπ

omit [MeasurableSpace X] in
theorem dyadicProjectionCell_disjoint (I : Box ι) (π : X → ι → ℝ) (k : ℕ) :
    Pairwise (Disjoint on dyadicProjectionCell I π k) := by
  intro J P hne
  apply Set.disjoint_left.mpr
  intro x hxJ hxP
  exact Set.disjoint_left.mp (dyadicBoxCell_disjoint I k hne) hxJ hxP

omit [MeasurableSpace X] in
theorem dyadicProjectionCell_cover (I : Box ι) (π : X → ι → ℝ) (k : ℕ) :
    (⋃ J : DyadicBoxIndex I k, dyadicProjectionCell I π k J) = π ⁻¹' (I : Set (ι → ℝ)) := by
  simp only [dyadicProjectionCell, ← preimage_iUnion, dyadicBoxCell_cover]

theorem dyadicProjectionCell_mass (I : Box ι) (e : (ι → ℝ) → X) (π : X → ι → ℝ)
    (he : Measurable e) (hπ : Measurable π) (hleft : LeftInverse π e)
    (k : ℕ) (J : DyadicBoxIndex I k) :
    (boxPlaneMeasure I e).real (dyadicProjectionCell I π k J) =
      (volume : Measure (ι → ℝ)).real I * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι := by
  have hJI : (J.val : Set (ι → ℝ)) ⊆ I :=
    (dyadicBoxPartition I k).le_of_mem J.property
  rw [Measure.real, dyadicProjectionCell, boxPlaneMeasure_preimage I e π he hπ hleft
    _ (dyadicBoxCell_measurable I k J)]
  change ((volume : Measure (ι → ℝ)) ((J.val : Set (ι → ℝ)) ∩ I)).toReal = _
  rw [inter_eq_left.mpr hJI]
  exact dyadicBoxPartition_volume I k J.val J.property

theorem boxPlaneMeasure_ae_coordinates (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (he : Measurable e) (hπ : Measurable π) (hleft : LeftInverse π e) :
    ∀ᵐ x ∂boxPlaneMeasure I e, π x ∈ I := by
  apply (ae_map_iff he.aemeasurable (I.measurableSet_coe.preimage hπ)).mpr
  filter_upwards [self_mem_ae_restrict I.measurableSet_coe] with x hx
  simpa only [hleft x] using! hx

theorem dyadicProjectionCell_cover_ae (I : Box ι) (π : X → ι → ℝ)
    (μ : Measure X) (hcoords : ∀ᵐ x ∂μ, π x ∈ I) (k : ℕ) :
    ∀ᵐ x ∂μ, x ∈ ⋃ J : DyadicBoxIndex I k, dyadicProjectionCell I π k J := by
  rw [dyadicProjectionCell_cover]
  exact hcoords

variable [MetricSpace X] [BorelSpace X]

theorem dyadicProjectionCell_null_frontier (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (he : Continuous e) (hπ : Continuous π) (hleft : LeftInverse π e)
    (k : ℕ) (J : DyadicBoxIndex I k) :
    boxPlaneMeasure I e (frontier (dyadicProjectionCell I π k J)) = 0 := by
  apply measure_mono_null (hπ.frontier_preimage_subset (dyadicBoxCell I k J))
  rw [boxPlaneMeasure_preimage I e π he.measurable hπ.measurable hleft
    _ isClosed_frontier.measurableSet]
  exact measure_mono_null inter_subset_left (box_frontier_volume_zero J.val)

omit [MeasurableSpace X] [BorelSpace X] in

theorem dyadicProjectionCell_dist_reference (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (k : ℕ) (J : DyadicBoxIndex I k) (x : X)
    (hx : x ∈ dyadicProjectionCell I π k J)
    (hheight : dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k) :
    dist x (e J.val.upper) ≤ (1 + (K : ℝ) * boxWidthBound I) * (1 / 2 : ℝ) ^ k := by
  have hp := dyadicBoxPartition_dist_upper_le I k J.val J.property (π x) hx
  calc
    dist x (e J.val.upper) ≤ dist x (e (π x)) + dist (e (π x)) (e J.val.upper) :=
      dist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) ^ k + (K : ℝ) * (boxWidthBound I * (1 / 2 : ℝ) ^ k) :=
      add_le_add hheight ((he.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left hp K.coe_nonneg))
    _ = _ := by ring

theorem boxPlaneMeasure_ae_section (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (he : Continuous e) (hπ : Continuous π) (hleft : LeftInverse π e) :
    ∀ᵐ x ∂boxPlaneMeasure I e, e (π x) = x := by
  apply (ae_map_iff he.measurable.aemeasurable
    (isClosed_eq (he.comp hπ) continuous_id).measurableSet).mpr
  exact Filter.Eventually.of_forall (fun x => congrArg e (hleft x))

omit [BorelSpace X] in
theorem dyadicProjectionCell_ae_dist_reference (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (hπ : Measurable π) (K : ℝ≥0) (he : LipschitzWith K e)
    (μ : Measure X) (k : ℕ)
    (hheight : ∀ᵐ x ∂μ, dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k)
    (J : DyadicBoxIndex I k) :
    ∀ᵐ x ∂μ.restrict (dyadicProjectionCell I π k J),
      dist x (e J.val.upper) ≤ (1 + (K : ℝ) * boxWidthBound I) * (1 / 2 : ℝ) ^ k := by
  filter_upwards [ae_restrict_of_ae hheight,
    self_mem_ae_restrict (dyadicProjectionCell_measurable I π hπ k J)] with x hxh hxc
  exact dyadicProjectionCell_dist_reference I e π K he k J x hxc hxh

omit [BorelSpace X] in
theorem dyadicProjectionCell_ae_diameter (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (hπ : Measurable π) (K : ℝ≥0) (he : LipschitzWith K e)
    (μ : Measure X) (k : ℕ)
    (hheight : ∀ᵐ x ∂μ, dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k)
    (J : DyadicBoxIndex I k) :
    ∀ᵐ x ∂μ.restrict (dyadicProjectionCell I π k J),
      ∀ᵐ y ∂μ.restrict (dyadicProjectionCell I π k J),
        dist x y ≤ (2 * (1 + (K : ℝ) * boxWidthBound I)) * (1 / 2 : ℝ) ^ k := by
  have href := dyadicProjectionCell_ae_dist_reference I e π hπ K he μ k hheight J
  filter_upwards [href] with x hx
  filter_upwards [href] with y hy
  have ht := dist_triangle x (e J.val.upper) y
  rw [dist_comm (e J.val.upper) y] at ht
  linarith

variable [Nonempty X]

theorem dyadicProjectionCell_mass_tendsto (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (he : Continuous e) (hπ : Continuous π) (hleft : LeftInverse π e)
    (μ : ℕ → FiniteMeasure X) (hweak : Tendsto μ atTop (𝓝 (boxPlaneFiniteMeasure I e)))
    (k : ℕ) (J : DyadicBoxIndex I k) :
    Tendsto (fun j => (μ j : Measure X).real (dyadicProjectionCell I π k J)) atTop
      (𝓝 ((volume : Measure (ι → ℝ)).real I * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι)) := by
  have h := finiteMeasure_cell_mass_tendsto μ (boxPlaneFiniteMeasure I e) hweak
    (boxPlaneFiniteMeasure_ne_zero I e he.measurable) (dyadicProjectionCell I π k J)
    (dyadicProjectionCell_null_frontier I e π he hπ hleft k J)
  change Tendsto _ _ (𝓝 ((boxPlaneMeasure I e).real (dyadicProjectionCell I π k J))) at h
  rwa [dyadicProjectionCell_mass I e π he.measurable hπ.measurable hleft k J] at h

theorem dyadicProjectionCell_eventual_mass_lower (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (he : Continuous e) (hπ : Continuous π) (hleft : LeftInverse π e)
    (μ : ℕ → FiniteMeasure X) (hweak : Tendsto μ atTop (𝓝 (boxPlaneFiniteMeasure I e)))
    (k : ℕ) :
    ∀ᶠ j in atTop, ∀ J : DyadicBoxIndex I k,
      ((volume : Measure (ι → ℝ)).real I / 2) * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι ≤
        (μ j : Measure X).real (dyadicProjectionCell I π k J) := by
  apply Filter.eventually_all.mpr
  intro J
  have hpos : 0 < (volume : Measure (ι → ℝ)).real I *
      ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι :=
    mul_pos (box_volume_real_pos I) (by positivity)
  have h := (dyadicProjectionCell_mass_tendsto I e π he hπ hleft μ hweak k J).eventually
    (lt_mem_nhds (show ((volume : Measure (ι → ℝ)).real I / 2) *
      ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι <
      (volume : Measure (ι → ℝ)).real I * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι by
        nlinarith))
  exact h.mono (fun _ hj => hj.le)

end

end RieszRectifiability

end OAI
