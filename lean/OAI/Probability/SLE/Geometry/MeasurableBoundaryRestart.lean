import OAI.Probability.SLE.Geometry.RandomBoundaryTubes
import OAI.Probability.SLE.Geometry.StoppedBoundaryRestart

namespace OAI

/-! The actual stopped trace law with a past-measurable boundary chart.
The identity holds at all future times, including boundary visits, for the
same chart family used in random continuation events. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem source_measurable_boundary_restart
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (hpublished : PublishedLoewnerBoundaryExtension)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ), ∃ Fb : Ω → C(closedHalfPlane, OnePoint ℂ),
      Measurable Φ ∧
      (∀ ω, Φ (sourceDriverPath B hc ω) = sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
      Measurable[hτ.measurableSpace] Fb ∧
      (∀ ω (z : closedHalfPlane), z.1 ∈ upperHalfPlane →
        Fb ω z = (F ω (τ ω) (z + (Real.sqrt κ * B (τ ω) ω : ℝ)) : OnePoint ℂ)) ∧
      (∀ ω, Fb ω ⟨0, by simp [closedHalfPlane]⟩ = (γ ω (τ ω) : OnePoint ℂ)) ∧
      (∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
        (P.restrict A).map (fun ω => Φ (sourceRestartDriverPath B hc τ ω)) =
          P A • P.map (sourceTracePath γ (fun ω => (hw ω).1))) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        (γ ω (τ ω + t) : OnePoint ℂ) =
          Fb ω (liftClosedPath (Φ (sourceRestartDriverPath B hc τ ω)) t) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Φ, hΦm, hΦ, hlaw⟩ := sourceStoppedTraceLaw κ hκ hκ8 B hB hm hc γ G F hw
  obtain ⟨Fb, hFbm, hFb, hFb0⟩ := source_stopped_boundaryPath_measurable
    hpublished B hm hc κ γ G F hw τ hτ
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  have hgm : Measurable gp := by
    have he : gp = fun ω => Φ (sourceDriverPath B hc ω) := funext fun ω => (hΦ ω).symm
    rw [he]
    exact hΦm.comp (source_path_measurable (sourceDriverPath B hc) hm)
  have hSLE : IsOrdinaryChordalSLE κ γ P := by
    refine ⟨fun t => (continuous_eval_const t).measurable.comp hgm, B, hB, ?_⟩
    exact Eventually.of_forall fun ω => ⟨G ω, F ω, hw ω⟩
  have hgood := StoppedBoundaryRestart.ordinarySLE_ae_goodBoundaryPath
    hκ hκ8 γ (fun ω => (hw ω).1) hSLE
  have hgoodLaw : ∀ᵐ p ∂P.map gp, StoppedBoundaryRestart.GoodBoundaryPath p :=
    (ae_map_iff hgm.aemeasurable StoppedBoundaryRestart.measurableSet_goodBoundaryPath).mpr hgood
  let rp := sourceRestartDriverPath B hc τ
  have hrm : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hc
      (stopping_time_measurable_nnreal hτ)))
  have hrestartLaw : P.map (fun ω => Φ (rp ω)) = P.map gp := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using
      (hlaw τ hτ).1 univ MeasurableSet.univ
  have hgoodRestart : ∀ᵐ ω ∂P, StoppedBoundaryRestart.GoodBoundaryPath (Φ (rp ω)) := by
    rw [← hrestartLaw] at hgoodLaw
    exact (ae_map_iff (hΦm.comp hrm).aemeasurable
      StoppedBoundaryRestart.measurableSet_goodBoundaryPath).mp hgoodLaw
  refine ⟨Φ, Fb, hΦm, hΦ, hFbm, hFb, hFb0, (hlaw τ hτ).1, ?_⟩
  filter_upwards [hgoodRestart, (hlaw τ hτ).2] with ω hgoodω heq
  let Fext : ℂ → OnePoint ℂ := fun z =>
    if hz : z ∈ closedHalfPlane then Fb ω ⟨z, hz⟩ else OnePoint.infty
  have hFc : ContinuousOn Fext closedHalfPlane := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert (Fb ω).continuous using 1
    funext z
    change Fext z = Fb ω z
    dsimp only [Fext]
    rw [dite_eq_left z.2]
  have hfull : ∀ t : ℝ≥0, (γ ω (τ ω + t) : OnePoint ℂ) = Fext (Φ (rp ω) t) := by
    apply StoppedBoundaryRestart.extend_restart_identity (Φ (rp ω))
      (fun t => γ ω (τ ω + t)) ((hw ω).1.comp (continuous_const.add continuous_id))
      Fext hFc hgoodω
    intro t ht
    have hz : Φ (rp ω) t ∈ closedHalfPlane :=
      (show 0 < (Φ (rp ω) t).im from ht).le
    simp only [Fext, dite_eq_left hz]
    rw [hFb ω ⟨Φ (rp ω) t, hz⟩ ht, heq t ht]
  intro t
  rw [hfull t]
  have hz : Φ (rp ω) t ∈ closedHalfPlane := hgoodω.2 t
  simp only [Fext, dite_eq_left hz]
  congr 1
  apply Subtype.ext
  exact (liftClosedPath_apply _ hgoodω.2 t).symm

end SLEExactGauge

end

end OAI
