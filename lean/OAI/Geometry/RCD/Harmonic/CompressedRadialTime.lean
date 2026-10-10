import OAI.Geometry.RCD.Harmonic.RadialTime
import OAI.Geometry.RCD.Transport.OptimalRadialTime
import OAI.Geometry.RCD.Harmonic.RadialDensityEnvelope

namespace OAI

/-! # Small-time radial contraction with uniform path compression

The prescribed marginal retains the sharp small-time density bound.
Replacing the intervening transport by a bounded-compression plan preserves
that marginal and, by optimal cost rigidity, its radial displacement.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal

namespace RegularPointCoordinates

noncomputable def radialPathBudget (K : ℝ) (n : ℕ) (κ D : ℝ) (C₀ : ℝ≥0∞) : ℝ≥0∞ :=
  compressionBudget K n (6 * D) (C₀ * ENNReal.ofReal (1 + 2 ^ n * Real.exp (κ * D ^ 2 / 6)))

theorem radialPathBudget_ne_top (K : ℝ) (n : ℕ) (κ D : ℝ) {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) :
    radialPathBudget K n κ D C₀ ≠ ∞ :=
  compressionBudget_ne_top K n _ (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.exists_compressed_radial_time {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K) (ν₀ : ProbabilityMeasure X)
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (h0 : (ν₀ : Measure X) ≤ C₀ • hausdorff n X)
    (p : X) {R D : ℝ} (hR : 0 < R) (hRD : R < D)
    (hs0 : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ R)
    (t : Time) (ht : 0 < (t : ℝ)) (ht1 : (t : ℝ) ≤ 1 / 2) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      π.map (fun γ => γ 0) = (ν₀ : Measure X) ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π ∧
      (∀ s : Time, π.map (fun γ => γ s) ≤ radialPathBudget K n κ D C₀ • hausdorff n X) ∧
      π.map (fun γ => γ 1) ≤
        (C₀ * ENNReal.ofReal (radialContractionDensity n κ D t)) • hausdorff n X ∧
      ∀ᵐ γ ∂π, dist (γ 0) (γ 1) = (t : ℝ) * dist (γ 0) p ∧
        dist (γ 1) p = (1 - (t : ℝ)) * dist (γ 0) p ∧
        dist (γ 0) p = dist (γ 0) (γ 1) + dist (γ 1) p := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  have ht1' : (t : ℝ) < 1 := by linarith
  obtain ⟨q, hq, hq0, hq1, hqm⟩ := hX.exists_radial_time_plan hn hκ hK ν₀ hC₀ h0
    p hR hRD hs0 t ht1'
  let η : Measure X := (q.map (fun γ => γ t) : Measure X)
  let M := 1 + 2 ^ n * Real.exp (κ * D ^ 2 / 6)
  let A := C₀ * ENNReal.ofReal M
  have hA : A ≠ ∞ := ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top
  have hM : 1 ≤ M := by
    have hh : 0 ≤ (2 : ℝ) ^ n * Real.exp (κ * D ^ 2 / 6) := by positivity
    dsimp only [M]
    linarith
  have hb0 : (ν₀ : Measure X) ≤ A • μ := by
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal M := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hM
    have hh : C₀ ≤ A := by simpa only [mul_one] using mul_le_mul_right hone C₀
    intro S
    exact (h0 S).trans (mul_le_mul_left hh (μ S))
  have hb1 : η ≤ A • μ := by
    have hle : radialContractionDensity n κ D t ≤ M :=
      (radialContractionDensity_le n hκ t.2.1 ht1).trans (by dsimp [M]; linarith)
    intro S
    exact (hqm S).trans (mul_le_mul_left
      (mul_le_mul_right (ENNReal.ofReal_le_ofReal hle) C₀) (μ S))
  have hη : ∀ᵐ x ∂η, dist x p ≤ 3 * D := by
    change ∀ᵐ x ∂(q.map (fun γ => γ t) : Measure X), dist x p ≤ 3 * D
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff (measurable_path_eval t).aemeasurable
      (measurableSet_le (measurable_id.dist measurable_const) measurable_const)).mpr
    exact hq.mono fun _ hγ => hγ.2 t
  have hs0' : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ 3 * D :=
    hs0.mono fun _ hx => by linarith
  obtain ⟨π, hπ, hg, hp, hi, hcomp⟩ := hX.exists_bounded_entropy_plan K n hn
    (ν₀ : Measure X) η hA hb0 hb1 p (by linarith : 0 ≤ 3 * D) hs0' hη
  let := hπ
  have hq1' : (q : Measure C(Time, X)).map (fun γ => γ 1) = Measure.dirac p := by
    have hh := congrArg (fun ν : ProbabilityMeasure X => (ν : Measure X)) hq1
    change (q.map (fun γ => γ 1) : Measure X) = Measure.dirac p at hh
    simpa only [ProbabilityMeasure.toMeasure_map] using hh
  have hq0' : (q : Measure C(Time, X)).map (fun γ => γ 0) = (ν₀ : Measure X) := by
    have hh := congrArg (fun ν : ProbabilityMeasure X => (ν : Measure X)) hq0
    simpa only [ProbabilityMeasure.toMeasure_map] using hh
  have hp' : IsOptimalCoupling ((q : Measure C(Time, X)).map (fun γ => γ 0))
      ((q : Measure C(Time, X)).map (fun γ => γ t)) (π.map (fun γ => (γ 0, γ 1))) := by
    rw [hq0']
    exact hp
  have he := optimalPlan_endpoints _ _ π hp
  refine ⟨π, hπ, he.1, hg,
    (memLp_two_iff_integrable_sq
      ((measurable_path_eval 0).dist (measurable_path_eval 1)).aestronglyMeasurable).mpr hi,
    ?_, he.2 ▸ hqm, ?_⟩
  · intro s
    simpa only [radialPathBudget, A, M, show 2 * (3 * D) = 6 * D by ring] using (hcomp s).1
  · exact optimal_radial_time (q : Measure C(Time, X)) p (by linarith : 0 ≤ 3 * D)
      hq hq1' t ht ht1' π hi hp'

end RegularPointCoordinates

end OAI
