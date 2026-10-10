import OAI.Probability.SLE.Geometry.MeasurableBoundaryRestart
import OAI.Probability.SLE.Loewner.FreshTipMapOut

namespace OAI

/-! Physical open-tube support after an actual finite first-height stop.
Simple continuation routes are mapped out by the actual Loewner chart;
their positive fresh-law probabilities transfer through the measurable
boundary restart, including all parameter-boundary visits. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def stoppedPhysicalTube {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ) (τ : Ω → ℝ≥0)
    (O W : Set ℂ) : Set Ω :=
  {ω | ∃ T : ℝ≥0, 0 < T ∧ MapsTo (fun t => γ ω (τ ω + t)) (Icc 0 T) O ∧
    γ ω (τ ω + T) ∈ W}

theorem measurableSet_stoppedPhysicalTube
    {Ω : Type*} [MeasurableSpace Ω]
    (γ : Ω → ℝ≥0 → ℂ) (hγ : ∀ ω, Continuous (γ ω))
    (hγm : ∀ t, Measurable (fun ω => γ ω t))
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (O W : Set ℂ) (hO : IsOpen O) (hW : IsOpen W) :
    MeasurableSet (stoppedPhysicalTube γ τ O W) := by
  let p (ω : Ω) : C(ℝ≥0, ℂ) :=
    ⟨fun t => γ ω (τ ω + t), (hγ ω).comp (continuous_const.add continuous_id)⟩
  have hj : Measurable (fun x : ℝ≥0 × Ω => γ x.2 x.1) :=
    measurable_uncurry_of_continuous_of_measurable hγ hγm
  have hp : Measurable p := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact hj.comp ((hτ.add_const t).prodMk measurable_id)
  exact (measurableSet_pathTubeEvent hO hW).preimage hp

theorem conditional_stopped_physical_tube_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (hboundary : PublishedLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (O W : Set ℂ) (hO : IsOpen O) (hW : IsOpen W) (E : Set Ω)
    (hfresh : ∀ ω ∈ E, 0 < τ ω ∧ 0 < (γ ω (τ ω)).im ∧
      ∀ u : ℝ≥0, u < τ ω → (γ ω u).im < (γ ω (τ ω)).im)
    (hroutes : ∀ ω ∈ E, ∃ w : ℂ, ∃ p : Path (γ ω (τ ω)) w,
      Function.Injective p ∧
      (∀ t, t ≠ 0 → p t ∈ survivingDomain (γ ω) (τ ω)) ∧
      range p ⊆ O ∧ w ∈ W) :
    ∀ᵐ ω ∂P, ω ∈ E →
      0 < P⁻[(stoppedPhysicalTube γ τ O W).indicator (fun _ => 1) |
        hτ.measurableSpace] ω := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Φ, Fb, hΦm, hΦ, hFbm, hFb, hFb0, hlaw, hfull⟩ :=
    source_measurable_boundary_restart κ hκ hκ8 B hB hm hc γ G F hw hboundary τ hτ
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  let Y := fun ω => Φ (sourceRestartDriverPath B hc τ ω)
  have hgm : Measurable gp := by
    have he : gp = Φ ∘ sourceDriverPath B hc := funext fun ω => (hΦ ω).symm
    rw [he]
    exact hΦm.comp (source_path_measurable (sourceDriverPath B hc) hm)
  have hYm : Measurable Y := hΦm.comp (source_path_measurable _ (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hc
      (stopping_time_measurable_nnreal hτ))))
  let O' : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' O
  let W' : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' W
  have hO' : IsOpen O' := OnePoint.isOpenEmbedding_coe.isOpenMap _ hO
  have hW' : IsOpen W' := OnePoint.isOpenEmbedding_coe.isOpenMap _ hW
  have hgeometry : ∀ ω ∈ E, ∃ z : ℂ, ∃ p : Path (0 : ℂ) z,
      Function.Injective p ∧
      ∃ hpH : ∀ t, t ≠ 0 → p t ∈ upperHalfPlane,
        (∀ t, Fb ω ⟨p t, by
          by_cases ht : t = 0
          · simp [ht, closedHalfPlane]
          · exact (show 0 < (p t).im from hpH t ht).le⟩ ∈ O') ∧
        Fb ω ⟨z, by simpa using
          (show 0 < (p 1).im from hpH 1 (by norm_num)).le⟩ ∈ W' := by
    intro ω hω
    obtain ⟨hτpos, hheight, hfirst⟩ := hfresh ω hω
    obtain ⟨w, p, hp, hpD, hpO, hwW⟩ := hroutes ω hω
    obtain ⟨q, hq, hqH, hqback⟩ := (hw ω).map_out_access_at_first_height
      (continuous_const.mul (hc ω)) (τ ω) hτpos hheight hfirst w p hp hpD
    refine ⟨_, q, hq, hqH, ?_, ?_⟩
    · intro t
      by_cases ht : t = 0
      · subst t
        simpa only [Path.source, hFb0] using
          (mem_image_of_mem ((↑) : ℂ → OnePoint ℂ) (hpO (mem_range_self 0)))
      · rw [hFb ω _ (hqH t ht), hqback t ht]
        exact mem_image_of_mem ((↑) : ℂ → OnePoint ℂ) (hpO (mem_range_self t))
    · rw [hFb ω _ (by simpa only [Path.target] using hqH 1 (by norm_num))]
      have he := hqback 1 (by norm_num)
      simp only [Path.target] at he
      rw [he]
      exact mem_image_of_mem ((↑) : ℂ → OnePoint ℂ) hwW
  have hpositive := conditional_random_boundary_tube_positive P
    hτ.measurableSpace hτ.measurableSpace_le Y gp hYm hgm hlaw
    (fun ω => (hw ω).2.2.1) hsupport Fb hFbm O' W' hO' hW' E hgeometry
  let C : Set Ω := {ω | (Fb ω).comp (liftClosedPath (Y ω)) ∈ pathTubeEventIn O' W'}
  have hsubset : ∀ᵐ ω ∂P, ω ∈ C → ω ∈ stoppedPhysicalTube γ τ O W := by
    filter_upwards [hfull] with ω hω hC
    obtain ⟨T, hT, htrace, hend⟩ := hC
    have hmap (t : ℝ≥0) {S : Set ℂ}
        (ht : Fb ω (liftClosedPath (Y ω) t) ∈ ((↑) : ℂ → OnePoint ℂ) '' S) :
        γ ω (τ ω + t) ∈ S := by
      obtain ⟨z, hz, he⟩ := ht
      have he' : z = γ ω (τ ω + t) := OnePoint.coe_injective (he.trans (hω t).symm)
      exact he' ▸ hz
    exact ⟨T, hT, fun t ht => hmap t (htrace ht), hmap T hend⟩
  have hmono : C.indicator (fun _ => (1 : ℝ≥0∞)) ≤ᵐ[P]
      (stoppedPhysicalTube γ τ O W).indicator (fun _ => 1) := by
    filter_upwards [hsubset] with ω hω
    by_cases hC : ω ∈ C
    · simp only [indicator_of_mem hC, indicator_of_mem (hω hC), le_refl]
    · simp only [indicator_of_notMem hC, zero_le]
  filter_upwards [hpositive, condLExp_mono (mΩ := hτ.measurableSpace) hmono] with ω hp hm hω
  exact (hp hω).trans_le hm

end SLEExactGauge

end

end OAI
