import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CountableSignedLimits
import OAI.Analysis.RieszRectifiability.Projections.ProjectionCompactness

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem exists_countable_projection_limits {ι X : Type*} [Fintype ι]
    [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [Nonempty X]
    (I : ℕ → Box ι) (e : (ι → ℝ) → X) (π : X → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e)
    (μ : ℕ → ℕ → FiniteMeasure X)
    (hweak : ∀ H, Tendsto (μ H) atTop (𝓝 (boxPlaneFiniteMeasure (I H) e)))
    (hcoords : ∀ H j, ∀ᵐ x ∂(μ H j : Measure X), π x ∈ I H)
    (hheight : ∀ H k : ℕ, ∀ᶠ j in atTop,
      ∀ᵐ x ∂(μ H j : Measure X), dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k)
    (w : ℕ → ℕ → X → ℝ) (hw : ∀ H j, MemLp (w H j) 2 (μ H j : Measure X))
    (B E : ℕ → ℝ) (hB : ∀ H j, (∫ x, w H j x ^ 2 ∂(μ H j : Measure X)) ≤ B H)
    (henergy : ∀ H j, Integrable
      (fun q : X × X => fractionalPairEnergy (Fintype.card ι) (w H j) q.1 q.2)
      ((μ H j : Measure X).prod (μ H j : Measure X)))
    (hE : ∀ H j, (∫ q : X × X, fractionalPairEnergy (Fintype.card ι) (w H j) q.1 q.2
      ∂(μ H j : Measure X).prod (μ H j : Measure X)) ≤ E H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ∀ H, Lp ℝ 2 (boxPlaneMeasure (I H) e),
      (∀ H, Tendsto (fun j => ∫ x, w H (φ j) x ^ 2 ∂(μ H (φ j) : Measure X)) atTop
        (𝓝 (‖v H‖ ^ 2))) ∧
      ∀ H (ψ : X → ℝ) (L : ℝ≥0), LipschitzWith L ψ →
        MemLp ψ 2 (boxPlaneMeasure (I H) e) → (∀ j, MemLp ψ 2 (μ H (φ j) : Measure X)) →
        Tendsto (fun j => ∫ x, w H (φ j) x * ψ x ∂(μ H (φ j) : Measure X)) atTop
          (𝓝 (∫ x, v H x * ψ x ∂boxPlaneMeasure (I H) e)) := by
  let ν : ℕ → Measure X := fun H => boxPlaneMeasure (I H) e
  let s : ∀ H k, DyadicBoxIndex (I H) k → Set X := fun H => dyadicProjectionCell (I H) π
  let a : ℕ → ℝ := fun H => 2 * (1 + (K : ℝ) * boxWidthBound (I H))
  let c : ℕ → ℝ := fun H => (volume : Measure (ι → ℝ)).real (I H) / 2
  let δ : ℕ → ℕ → ℝ := fun H k =>
    (a H ^ (Fintype.card ι + 1) / (2 * c H) * (1 / 2 : ℝ) ^ k) * E H
  have ha : ∀ H, 0 ≤ a H := by
    intro H
    dsimp [a]
    positivity [boxWidthBound_nonneg (I H)]
  have hc : ∀ H, 0 < c H := fun H => half_pos (box_volume_real_pos (I H))
  have hδ : ∀ H, Tendsto (δ H) atTop (𝓝 0) := by
    intro H
    simpa only [mul_zero, zero_mul] using!
      (dyadic_box_scale_tendsto_zero.const_mul (a H ^ (Fintype.card ι + 1) / (2 * c H))).mul_const (E H)
  have hs : ∀ H k J, MeasurableSet (s H k J) :=
    fun H k J => dyadicProjectionCell_measurable (I H) π hπ.measurable k J
  have hd : ∀ H k, Pairwise (Disjoint on s H k) := fun H => dyadicProjectionCell_disjoint (I H) π
  have hcover : ∀ H k j, ∀ᵐ x ∂(μ H j : Measure X), x ∈ ⋃ J, s H k J :=
    fun H k j => dyadicProjectionCell_cover_ae (I H) π _ (hcoords H j) k
  have hboundary : ∀ H k J, ν H (frontier (s H k J)) = 0 :=
    fun H k J => dyadicProjectionCell_null_frontier (I H) e π he.continuous hπ hleft k J
  have hν : ∀ H, boxPlaneFiniteMeasure (I H) e ≠ 0 :=
    fun H => boxPlaneFiniteMeasure_ne_zero (I H) e he.continuous.measurable
  have hm : ∀ H k J, Tendsto (fun j => (μ H j : Measure X).real (s H k J)) atTop
      (𝓝 ((ν H).real (s H k J))) :=
    fun H k J => finiteMeasure_cell_mass_tendsto (μ H) (boxPlaneFiniteMeasure (I H) e)
      (hweak H) (hν H) (s H k J) (hboundary H k J)
  have hmpos : ∀ H k J, 0 < (ν H).real (s H k J) := by
    intro H k J
    change 0 < (boxPlaneMeasure (I H) e).real (dyadicProjectionCell (I H) π k J)
    rw [dyadicProjectionCell_mass (I H) e π he.continuous.measurable hπ.measurable hleft]
    exact mul_pos (box_volume_real_pos (I H)) (by positivity)
  have hinter : ∀ H k l J P, Tendsto (fun j => (μ H j : Measure X).real (s H k J ∩ s H l P))
      atTop (𝓝 ((ν H).real (s H k J ∩ s H l P))) :=
    fun H k l J P => finiteMeasure_cell_intersection_mass_tendsto (μ H)
      (boxPlaneFiniteMeasure (I H) e) (hweak H) (hν H) (s H k J) (s H l P)
      (hboundary H k J) (hboundary H l P)
  have hmass : ∀ H k, ∀ᶠ j in atTop, ∀ J : DyadicBoxIndex (I H) k,
      c H * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι ≤ (μ H j : Measure X).real (s H k J) :=
    fun H => dyadicProjectionCell_eventual_mass_lower (I H) e π he.continuous hπ hleft
      (μ H) (hweak H)
  have happrox : ∀ H k, ∀ᶠ j in atTop,
      (∫ x, (w H j x - partitionMean (μ H j : Measure X) (s H k) (w H j) x) ^ 2
        ∂(μ H j : Measure X)) ≤ δ H k := by
    intro H k
    filter_upwards [hmass H k, hheight H k] with j hjmass hjheight
    have hb := partition_error_le_scale_times_energy_ae (μ H j : Measure X) (s H k)
      (hs H k) (hd H k) (Fintype.card ι) (w H j) (hw H j) (a H) ((1 / 2 : ℝ) ^ k) (c H)
      (ha H) (by positivity) (hc H) hjmass
      (dyadicProjectionCell_ae_diameter (I H) e π hπ.measurable K he _ k hjheight) (henergy H j)
    rw [Measure.restrict_eq_self_of_ae_mem (hcover H k j)] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (hE H j)
      (mul_nonneg (div_nonneg (pow_nonneg (ha H) _) (by positivity)) (by positivity)))
  let D : ℕ → ℝ := fun H => 1 + (K : ℝ) * boxWidthBound (I H)
  have hD : ∀ H, 0 ≤ D H := by
    intro H
    dsimp [D]
    positivity [boxWidthBound_nonneg (I H)]
  have hrzero : ∀ H, Tendsto (fun k : ℕ => D H * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    intro H
    simpa only [mul_zero] using! dyadic_box_scale_tendsto_zero.const_mul (D H)
  have htotal : ∀ H, ∀ᶠ j in atTop, (μ H j : Measure X).real univ ≤ (ν H).real univ + 1 := by
    intro H
    have ht : Tendsto (fun j => (μ H j : Measure X).real univ) atTop (𝓝 ((ν H).real univ)) :=
      NNReal.continuous_coe.continuousAt.tendsto.comp (hweak H).mass
    exact (ht.eventually (gt_mem_nhds (by linarith : (ν H).real univ <
      (ν H).real univ + 1))).mono (fun _ hj => hj.le)
  have hcoverν : ∀ H k, ∀ᵐ x ∂ν H, x ∈ ⋃ J, s H k J :=
    fun H k => dyadicProjectionCell_cover_ae (I H) π (ν H)
      (boxPlaneMeasure_ae_coordinates (I H) e π he.continuous.measurable hπ.measurable hleft) k
  have hcellν : ∀ H k J, ∀ᵐ x ∂(ν H).restrict (s H k J),
      dist x (e J.val.upper) ≤ D H * (1 / 2 : ℝ) ^ k := by
    intro H k J
    apply dyadicProjectionCell_ae_dist_reference (I H) e π hπ.measurable K he (ν H) k _ J
    filter_upwards [boxPlaneMeasure_ae_section (I H) e π he.continuous hπ hleft] with x hx
    rw [hx, dist_self]
    positivity
  apply exists_common_localized_signed_limits (fun H j => (μ H j : Measure X)) ν
    (fun H => DyadicBoxIndex (I H)) s hs hd w hw B hB hm hmpos hinter δ hδ happrox hcover hcoverν
    (fun _ _ J => e J.val.upper) (fun H k => D H * (1 / 2 : ℝ) ^ k)
    (fun H _ => mul_nonneg (hD H) (by positivity)) hrzero (fun H => (ν H).real univ + 1)
    htotal _ hcellν
  intro H k
  filter_upwards [hheight H k] with j hj
  exact dyadicProjectionCell_ae_dist_reference (I H) e π hπ.measurable K he _ k hj

end

end RieszRectifiability

end OAI
