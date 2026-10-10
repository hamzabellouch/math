import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.PlaneBoxGrowth
import OAI.Analysis.RieszRectifiability.Projections.ProjectionCompactness
import OAI.Analysis.RieszRectifiability.Limits.SingularCompactness

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem exists_projection_limit_with_singular_pairings {d : ℕ} (p : ℕ)
    (I : Box (Fin (p + 1))) (e : (Fin (p + 1) → ℝ) → Ambient d)
    (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π)
    (hleft : LeftInverse π e) (μ : ℕ → FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 (boxPlaneFiniteMeasure I e)))
    (C : ℝ) (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j : Measure (Ambient d)))
    (hcoords : ∀ j, ∀ᵐ x ∂(μ j : Measure (Ambient d)), π x ∈ I)
    (hheight : ∀ k : ℕ, ∀ᶠ j in atTop,
      ∀ᵐ x ∂(μ j : Measure (Ambient d)), dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k)
    (w : ℕ → Ambient d → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j : Measure (Ambient d)))
    (hwm : ∀ j, Measurable (w j))
    (B E : ℝ) (hB : ∀ j, (∫ x, w j x ^ 2 ∂(μ j : Measure (Ambient d))) ≤ B)
    (henergy : ∀ j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      ((μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))))
    (hE : ∀ j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) (w j) q.1 q.2
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) ≤ E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : Lp ℝ 2 (boxPlaneMeasure I e),
      Tendsto (fun j => ∫ x, w (φ j) x ^ 2 ∂(μ (φ j) : Measure (Ambient d))) atTop
        (𝓝 (‖v‖ ^ 2)) ∧
      Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) v q.1 q.2)
        ((boxPlaneMeasure I e).prod (boxPlaneMeasure I e)) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) v q.1 q.2
        ∂(boxPlaneMeasure I e).prod (boxPlaneMeasure I e)) ≤ E ∧
      ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
        Tendsto (fun j => ∫ q : Ambient d × Ambient d,
          fractionalBilinear (p + 1) (w (φ j)) ψ q.1 q.2
          ∂(μ (φ j) : Measure (Ambient d)).prod (μ (φ j) : Measure (Ambient d))) atTop
          (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v ψ q.1 q.2
            ∂(boxPlaneMeasure I e).prod (boxPlaneMeasure I e))) := by
  obtain ⟨φ, hφ, v, hsecond, hmoment⟩ := exists_projection_limit_with_moments
    I e π K he hπ.continuous hleft μ hweak hcoords hheight w hw B E hB
    (by simpa only [Fintype.card_fin] using! henergy)
    (by simpa only [Fintype.card_fin] using! hE)
  let ν : FiniteMeasure (Ambient d) := boxPlaneFiniteMeasure I e
  let s : ∀ k, DyadicBoxIndex I k → Set (Ambient d) := dyadicProjectionCell I π
  let D : ℝ := 1 + (K : ℝ) * boxWidthBound I
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity [boxWidthBound_nonneg I]
  have hrzero : Tendsto (fun k : ℕ => D * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using! dyadic_box_scale_tendsto_zero.const_mul D
  have hs : ∀ k J, MeasurableSet (s k J) :=
    fun k J => dyadicProjectionCell_measurable I π hπ.continuous.measurable k J
  have hd : ∀ k, Pairwise (Disjoint on s k) := dyadicProjectionCell_disjoint I π
  have hcover : ∀ k j, ∀ᵐ x ∂(μ (φ j) : Measure (Ambient d)), x ∈ ⋃ J, s k J :=
    fun k j => dyadicProjectionCell_cover_ae I π _ (hcoords (φ j)) k
  have hcoverν : ∀ k, ∀ᵐ x ∂(ν : Measure (Ambient d)), x ∈ ⋃ J, s k J :=
    fun k => dyadicProjectionCell_cover_ae I π _
      (boxPlaneMeasure_ae_coordinates I e π he.continuous.measurable
        hπ.continuous.measurable hleft) k
  have hcell : ∀ k, ∀ᶠ j in atTop, ∀ J : DyadicBoxIndex I k,
      ∀ᵐ x ∂(μ (φ j) : Measure (Ambient d)).restrict (s k J),
        dist x (e J.val.upper) ≤ D * (1 / 2 : ℝ) ^ k := by
    intro k
    filter_upwards [hφ.tendsto_atTop.eventually (hheight k)] with j hj
    exact dyadicProjectionCell_ae_dist_reference I e π hπ.continuous.measurable K he _ k hj
  have hcellν : ∀ k J, ∀ᵐ x ∂(ν : Measure (Ambient d)).restrict (s k J),
      dist x (e J.val.upper) ≤ D * (1 / 2 : ℝ) ^ k := by
    intro k J
    apply dyadicProjectionCell_ae_dist_reference I e π hπ.continuous.measurable K he _ k _ J
    filter_upwards [boxPlaneMeasure_ae_section I e π he.continuous hπ.continuous hleft] with x hx
    rw [hx, dist_self]
    positivity
  have hν : ν ≠ 0 := boxPlaneFiniteMeasure_ne_zero I e he.continuous.measurable
  have hmass : ∀ k J, Tendsto (fun j => (μ (φ j) : Measure (Ambient d)).real (s k J)) atTop
      (𝓝 ((ν : Measure (Ambient d)).real (s k J))) := by
    intro k J
    exact (finiteMeasure_cell_mass_tendsto μ ν hweak hν (s k J)
      (dyadicProjectionCell_null_frontier I e π he.continuous hπ.continuous hleft k J)).comp
        hφ.tendsto_atTop
  have htotal : Tendsto (fun j => (μ j : Measure (Ambient d)).real univ) atTop
      (𝓝 ((ν : Measure (Ambient d)).real univ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
  have heventual : ∀ᶠ j in atTop, |(μ j : Measure (Ambient d)).real univ| ≤
      (ν : Measure (Ambient d)).real univ + 1 := by
    filter_upwards [htotal.eventually (gt_mem_nhds
      (by linarith : (ν : Measure (Ambient d)).real univ <
        (ν : Measure (Ambient d)).real univ + 1))] with j hj
    simpa only [abs_of_nonneg measureReal_nonneg] using! hj.le
  obtain ⟨T, hT⟩ := bounded_of_eventually_abs_le
    (fun j => (μ j : Measure (Ambient d)).real univ)
    ((ν : Measure (Ambient d)).real univ + 1) heventual
  have htotalM : ∀ j, (μ (φ j) : Measure (Ambient d)).real univ ≤ max T B := by
    intro j
    exact (le_abs_self _).trans ((hT (φ j)).trans (le_max_left _ _))
  have hsecondM : ∀ j, (∫ x, w (φ j) x ^ 2 ∂(μ (φ j) : Measure (Ambient d))) ≤ max T B :=
    fun j => (hB (φ j)).trans (le_max_right _ _)
  have hgν : GlobalUpperGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1))
      (ν : Measure (Ambient d)) := by
    simpa only [Fintype.card_fin] using! boxPlaneMeasure_upper_growth I e π
      he.continuous.measurable Q hπ hleft
  obtain ⟨hvE, hvEbound, hsingular⟩ := singular_compactness_of_weak_moments p
    (max C ((2 * (Q : ℝ)) ^ (p + 1))) (fun j => μ (φ j)) ν
    (hweak.comp hφ.tendsto_atTop)
    (fun j => (hg (φ j)).mono_constant (le_max_left _ _))
    (hgν.mono_constant (le_max_right _ _)) (fun j => w (φ j)) v
    (fun j => hw (φ j)) (fun j => hwm (φ j)) (Lp.memLp v) (Lp.stronglyMeasurable v).measurable
    (DyadicBoxIndex I) s hs hd hcover hcoverν (fun _ J => e J.val.upper)
    (fun k => D * (1 / 2 : ℝ) ^ k) (fun _ => mul_nonneg hD (by positivity)) hrzero
    hcell hcellν hmass (max T B) htotalM hsecondM hmoment
    (fun j => henergy (φ j)) E (fun j => hE (φ j))
  exact ⟨φ, hφ, v, hsecond, hvE, hvEbound, hsingular⟩

end

end RieszRectifiability

end OAI
