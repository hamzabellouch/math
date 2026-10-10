import OAI.GroupTheory.PolycyclicRecognition.Analysis.LowerPacking
import Mathlib.Topology.Maps.Proper.Basic

namespace OAI

/-! # Lower packing on a fixed Cartan slice

A finite net in the ambient group pulls back to a cover of the nilpotent
parameter set. Conjugation preserving Haar makes the mass of every pulled-back
ball independent of the slice position. This is the fixed-position part of
the manuscript's lower packing argument, with no assumption on an image's
absolute continuity or multiplicity.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal

/-- A net of an image gives a lower cardinality bound whenever the preimage
of each covering ball has uniformly bounded mass. The source set need not be
measurable. -/
theorem exists_separated_image_net_volume_bound
    {N G : Type*} [MeasurableSpace N] [PseudoMetricSpace G]
    (μ : Measure N) (f : N → G) {S : Set N}
    (hS : TotallyBounded (f '' S)) {r : ℝ} (hr : 0 < r) (C : ℝ≥0∞)
    (hball : ∀ y ∈ f '' S, μ (f ⁻¹' closedBall y r) ≤ C) :
    ∃ t : Finset G, (↑t : Set G) ⊆ f '' S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      μ S ≤ (t.card : ℝ≥0∞) * C := by
  classical
  obtain ⟨t, ht, hsep, hcover⟩ := exists_separated_net_of_totallyBounded hS hr
  refine ⟨t, ht, hsep, ?_⟩
  calc
    μ S ≤ μ (⋃ y ∈ t, f ⁻¹' closedBall y r) := measure_mono (by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hcover (f x) ⟨x, hx, rfl⟩
      exact mem_iUnion₂.mpr ⟨y, hy, hxy⟩)
    _ ≤ ∑ y ∈ t, μ (f ⁻¹' closedBall y r) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ t, C := Finset.sum_le_sum (fun y hy => hball y (ht hy))
    _ = (t.card : ℝ≥0∞) * C := by simp [nsmul_eq_mul]

variable {N D G : Type*} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MetricSpace G] [IsIsometricSMul G G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)

omit [MeasurableSpace N] in
/-- Compute the entire fiber of an ambient ball on a fixed slice. The
identity-neighborhood in the nilpotent group is conjugated, then translated. -/
theorem fixedSlice_ball_preimage
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (d : D) (v : N) (r : ℝ) :
    (fun u : N => x * ι u * κ d) ⁻¹' closedBall (x * ι v * κ d) r =
      (fun n => v * φ d n) '' (ι ⁻¹' closedBall (1 : G) r) := by
  ext u
  constructor
  · intro hu
    let n := φ d⁻¹ (v⁻¹ * u)
    have hn : φ d n = v⁻¹ * u := by simp [n]
    refine ⟨n, ?_, ?_⟩
    · change dist (ι n) 1 ≤ r
      have he : (x * ι v * κ d) * ι n = x * ι u * κ d := by
        have hc := hconj d n
        rw [hn] at hc
        have hh : κ d * ι n = ι (v⁻¹ * u) * κ d := by
          rw [hc]
          simp only [mul_assoc, inv_mul_cancel, mul_one]
        calc
          (x * ι v * κ d) * ι n = x * ι v * (κ d * ι n) := by simp only [mul_assoc]
          _ = x * ι v * (ι (v⁻¹ * u) * κ d) := by rw [hh]
          _ = x * ι u * κ d := by simp [mul_assoc]
      have hd := dist_mul_left (x * ι v * κ d) (ι n) 1
      rw [he, mul_one] at hd
      exact hd ▸ hu
    · simp [hn]
  · rintro ⟨n, hn, rfl⟩
    change dist (x * ι (v * φ d n) * κ d) (x * ι v * κ d) ≤ r
    rw [map_mul, hconj]
    have he : x * (ι v * (κ d * ι n * (κ d)⁻¹)) * κ d =
        (x * ι v * κ d) * ι n := by group
    rw [he]
    calc
      dist ((x * ι v * κ d) * ι n) (x * ι v * κ d) = dist (ι n) 1 := by
        simpa only [mul_one] using dist_mul_left (x * ι v * κ d) (ι n) 1
      _ ≤ r := hn

variable [MeasurableMul N]

/-- Haar mass of a slice ball depends only on its radius. In particular it
does not grow with the Cartan position or the center of the ball. -/
theorem fixedSlice_ball_measure
    (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (d : D) (v : N) (r : ℝ) :
    μ ((fun u : N => x * ι u * κ d) ⁻¹' closedBall (x * ι v * κ d) r) =
      μ (ι ⁻¹' closedBall (1 : G) r) := by
  rw [fixedSlice_ball_preimage ι κ φ hconj]
  let e : N ≃ᵐ N :=
    { toEquiv :=
        { toFun := fun n => v * φ d n
          invFun := fun n => φ d⁻¹ (v⁻¹ * n)
          left_inv := by intro n; simp
          right_inv := by intro n; simp }
      measurable_toFun := (measurable_const_mul v).comp (hφ d).measurable
      measurable_invFun := (hφ d⁻¹).measurable.comp (measurable_const_mul v⁻¹) }
  have hmp : MeasurePreserving e μ μ := (measurePreserving_mul_left μ v).comp (hφ d)
  change μ (e '' _) = _
  have hm := hmp.measure_preimage_equiv (e '' (ι ⁻¹' closedBall (1 : G) r))
  rw [Set.preimage_image_eq _ e.injective] at hm
  exact hm.symm

/-- The fixed-position lower packing estimate. The only volume constant is
the Haar mass of the identity ball pulled back to the nilpotent subgroup. -/
theorem exists_fixedSlice_separated_net
    (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (d : D) (S : Set N)
    (hS : TotallyBounded ((fun u : N => x * ι u * κ d) '' S))
    {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset G, (↑t : Set G) ⊆ (fun u : N => x * ι u * κ d) '' S ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → r < dist a b) ∧
      μ S ≤ (t.card : ℝ≥0∞) * μ (ι ⁻¹' closedBall (1 : G) r) := by
  apply exists_separated_image_net_volume_bound μ _ hS hr
  rintro y ⟨v, _, rfl⟩
  exact (fixedSlice_ball_measure ι κ φ μ hφ hconj x d v r).le

variable [TopologicalSpace N] [ContinuousMul G]

omit [IsIsometricSMul G G] [MeasurableMul N] [ContinuousMul G] in
/-- A closed subgroup realization gives a finite packing constant at every
fixed radius, since the ambient metric is proper. -/
theorem fixedSlice_packing_constant_lt_top
    [ProperSpace G] (μ : Measure N) [IsFiniteMeasureOnCompacts μ]
    (hι : Topology.IsClosedEmbedding ι) (r : ℝ) :
    μ (ι ⁻¹' closedBall (1 : G) r) < ⊤ :=
  (hι.isProperMap.isCompact_preimage (isCompact_closedBall 1 r)).measure_lt_top

/-- Any subset of a compact parameter set satisfies the fixed-slice lower
packing bound. Its image need not be measurable. -/
theorem exists_fixedSlice_separated_net_of_compact
    (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hι : Continuous ι) (x : G) (d : D) {K S : Set N}
    (hK : IsCompact K) (hS : S ⊆ K) {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset G, (↑t : Set G) ⊆ (fun u : N => x * ι u * κ d) '' S ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → r < dist a b) ∧
      μ S ≤ (t.card : ℝ≥0∞) * μ (ι ⁻¹' closedBall (1 : G) r) := by
  apply exists_fixedSlice_separated_net ι κ φ μ hφ hconj x d S
  · exact ((hK.image ((continuous_const.mul hι).mul continuous_const)).totallyBounded).subset
      (image_mono hS)
  · exact hr

end PolycyclicRecognition

end

end OAI
