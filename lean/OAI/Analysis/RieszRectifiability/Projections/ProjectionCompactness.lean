import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.ProjectionCells
import OAI.Analysis.RieszRectifiability.Limits.LipschitzMomentConvergence
import OAI.Analysis.RieszRectifiability.Nets.CellEnergyAE

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X] [MetricSpace X]
  [BorelSpace X] [Nonempty X]

theorem exists_projection_limit_with_moments
    (I : Box ι) (e : (ι → ℝ) → X) (π : X → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e)
    (μ : ℕ → FiniteMeasure X)
    (hweak : Tendsto μ atTop (𝓝 (boxPlaneFiniteMeasure I e)))
    (hcoords : ∀ j, ∀ᵐ x ∂(μ j : Measure X), π x ∈ I)
    (hheight : ∀ k : ℕ, ∀ᶠ j in atTop,
      ∀ᵐ x ∂(μ j : Measure X), dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k)
    (w : ℕ → X → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j : Measure X))
    (B E : ℝ) (hB : ∀ j, (∫ x, w j x ^ 2 ∂(μ j : Measure X)) ≤ B)
    (henergy : ∀ j, Integrable
      (fun p : X × X => fractionalPairEnergy (Fintype.card ι) (w j) p.1 p.2)
      ((μ j : Measure X).prod (μ j : Measure X)))
    (hE : ∀ j, (∫ p : X × X, fractionalPairEnergy (Fintype.card ι) (w j) p.1 p.2
      ∂(μ j : Measure X).prod (μ j : Measure X)) ≤ E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : Lp ℝ 2 (boxPlaneMeasure I e),
      Tendsto (fun j => ∫ x, w (φ j) x ^ 2 ∂(μ (φ j) : Measure X)) atTop (𝓝 (‖v‖ ^ 2)) ∧
      ∀ (ψ : X → ℝ) (L : ℝ≥0), LipschitzWith L ψ →
        MemLp ψ 2 (boxPlaneMeasure I e) → (∀ j, MemLp ψ 2 (μ (φ j) : Measure X)) →
        Tendsto (fun j => ∫ x, w (φ j) x * ψ x ∂(μ (φ j) : Measure X)) atTop
          (𝓝 (∫ x, v x * ψ x ∂boxPlaneMeasure I e)) := by
  let ν : Measure X := boxPlaneMeasure I e
  let s : ∀ k, DyadicBoxIndex I k → Set X := dyadicProjectionCell I π
  let a : ℝ := 2 * (1 + (K : ℝ) * boxWidthBound I)
  let c : ℝ := (volume : Measure (ι → ℝ)).real I / 2
  let δ : ℕ → ℝ := fun k => (a ^ (Fintype.card ι + 1) / (2 * c) * (1 / 2 : ℝ) ^ k) * E
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity [boxWidthBound_nonneg I]
  have hc : 0 < c := half_pos (box_volume_real_pos I)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using!
      (dyadic_box_scale_tendsto_zero.const_mul (a ^ (Fintype.card ι + 1) / (2 * c))).mul_const E
  have hs : ∀ k J, MeasurableSet (s k J) :=
    fun k J => dyadicProjectionCell_measurable I π hπ.measurable k J
  have hd : ∀ k, Pairwise (Disjoint on s k) := dyadicProjectionCell_disjoint I π
  have hcover : ∀ k j, ∀ᵐ x ∂(μ j : Measure X), x ∈ ⋃ J, s k J :=
    fun k j => dyadicProjectionCell_cover_ae I π (μ j : Measure X) (hcoords j) k
  have hboundary : ∀ k J, ν (frontier (s k J)) = 0 :=
    fun k J => dyadicProjectionCell_null_frontier I e π he.continuous hπ hleft k J
  have hν : boxPlaneFiniteMeasure I e ≠ 0 :=
    boxPlaneFiniteMeasure_ne_zero I e he.continuous.measurable
  have hm : ∀ k J, Tendsto (fun j => (μ j : Measure X).real (s k J)) atTop
      (𝓝 (ν.real (s k J))) :=
    fun k J => finiteMeasure_cell_mass_tendsto μ (boxPlaneFiniteMeasure I e)
      hweak hν (s k J) (hboundary k J)
  have hmpos : ∀ k J, 0 < ν.real (s k J) := by
    intro k J
    change 0 < (boxPlaneMeasure I e).real (dyadicProjectionCell I π k J)
    rw [dyadicProjectionCell_mass I e π he.continuous.measurable hπ.measurable hleft]
    exact mul_pos (box_volume_real_pos I) (by positivity)
  have hinter : ∀ k l J P, Tendsto (fun j => (μ j : Measure X).real (s k J ∩ s l P))
      atTop (𝓝 (ν.real (s k J ∩ s l P))) :=
    fun k l J P => finiteMeasure_cell_intersection_mass_tendsto μ (boxPlaneFiniteMeasure I e)
      hweak hν (s k J) (s l P) (hboundary k J) (hboundary l P)
  have hmass : ∀ k, ∀ᶠ j in atTop, ∀ J : DyadicBoxIndex I k,
      c * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι ≤ (μ j : Measure X).real (s k J) :=
    dyadicProjectionCell_eventual_mass_lower I e π he.continuous hπ hleft μ hweak
  have happrox : ∀ k, ∀ᶠ j in atTop,
      (∫ x, (w j x - partitionMean (μ j : Measure X) (s k) (w j) x) ^ 2
        ∂(μ j : Measure X)) ≤ δ k := by
    intro k
    filter_upwards [hmass k, hheight k] with j hjmass hjheight
    have hb := partition_error_le_scale_times_energy_ae (μ j : Measure X) (s k)
      (hs k) (hd k) (Fintype.card ι) (w j) (hw j) a ((1 / 2 : ℝ) ^ k) c ha
      (by positivity) hc hjmass
      (dyadicProjectionCell_ae_diameter I e π hπ.measurable K he _ k hjheight) (henergy j)
    rw [Measure.restrict_eq_self_of_ae_mem (hcover k j)] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (hE j)
      (mul_nonneg (div_nonneg (pow_nonneg ha _) (by positivity)) (by positivity)))
  obtain ⟨φ, hφ, b, hb, v, hv⟩ := exists_subsequence_partition_L2_limit
    (fun j => (μ j : Measure X)) ν (DyadicBoxIndex I) s hs hd w hw B hB
    hm hmpos hinter δ hδ happrox
  refine ⟨φ, hφ, v, ?_, ?_⟩
  · apply partition_approximation_second_moments_tendsto
      (fun j => (μ (φ j) : Measure X)) ν (DyadicBoxIndex I) s hs hd
      (fun j => w (φ j)) (fun j => hw (φ j))
      (fun j k J => cellMean ((μ (φ j) : Measure X).restrict (s k J)) (w (φ j)))
      b hb (fun k J => (hm k J).comp hφ.tendsto_atTop) δ hδ _ v hv
    intro k
    simpa only [partitionMean_eq_finiteStep] using! hφ.tendsto_atTop.eventually (happrox k)
  · intro ψ L hLip hψ hψj
    let D : ℝ := 1 + (K : ℝ) * boxWidthBound I
    have hD : 0 ≤ D := by
      dsimp [D]
      positivity [boxWidthBound_nonneg I]
    have hrzero : Tendsto (fun k : ℕ => D * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
      simpa only [mul_zero] using! dyadic_box_scale_tendsto_zero.const_mul D
    have htotal : Tendsto (fun j => (μ j : Measure X).real univ) atTop (𝓝 (ν.real univ)) :=
      NNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
    have htotalBound : ∀ᶠ j in atTop, (μ j : Measure X).real univ ≤ ν.real univ + 1 :=
      (htotal.eventually (gt_mem_nhds (by linarith : ν.real univ < ν.real univ + 1))).mono
        (fun _ hj => hj.le)
    have hpos : ∀ k, ∀ᶠ j in atTop, ∀ J : DyadicBoxIndex I k,
        (μ (φ j) : Measure X).real (s k J) ≠ 0 := by
      intro k
      filter_upwards [hφ.tendsto_atTop.eventually (hmass k)] with j hj
      intro J
      exact (lt_of_lt_of_le (mul_pos hc (by positivity)) (hj J)).ne'
    have hcoverν : ∀ k, ∀ᵐ x ∂ν, x ∈ ⋃ J, s k J :=
      fun k => dyadicProjectionCell_cover_ae I π ν
        (boxPlaneMeasure_ae_coordinates I e π he.continuous.measurable hπ.measurable hleft) k
    have hcellν : ∀ k J, ∀ᵐ x ∂ν.restrict (s k J),
        dist x (e J.val.upper) ≤ D * (1 / 2 : ℝ) ^ k := by
      intro k J
      apply dyadicProjectionCell_ae_dist_reference I e π hπ.measurable K he ν k _ J
      filter_upwards [boxPlaneMeasure_ae_section I e π he.continuous hπ hleft] with x hx
      rw [hx, dist_self]
      positivity
    apply lipschitz_partition_signed_moment_tendsto (fun j => (μ (φ j) : Measure X)) ν
      (DyadicBoxIndex I) s hs hd (fun k j => hcover k (φ j)) hcoverν
      (fun j => w (φ j)) (fun j => hw (φ j)) B (fun j => hB (φ j)) b hb
      (fun k J => (hm k J).comp hφ.tendsto_atTop) hpos v hv
      (fun _ J => e J.val.upper) (fun k => D * (1 / 2 : ℝ) ^ k)
      (fun _ => mul_nonneg hD (by positivity)) hrzero (ν.real univ + 1)
      (hφ.tendsto_atTop.eventually htotalBound) _ hcellν ψ L hLip hψ
      hψj
    intro k
    filter_upwards [hφ.tendsto_atTop.eventually (hheight k)] with j hj
    exact dyadicProjectionCell_ae_dist_reference I e π hπ.measurable K he _ k hj

end

end RieszRectifiability

end OAI
