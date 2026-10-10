import OAI.Probability.SLE.Geometry.FiniteDensityAtPast
import OAI.Probability.SLE.Gauge.DenseRadiusGap
import OAI.Probability.SLE.InverseMoments

namespace OAI

/-! The exact density on a finite stopped past at a live radius state.
The deeper finite-centered law has the original Green density there. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem exists_finiteDensity_at_radius_state
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B
      (fun _t => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u q : ℝ) (hu : 0 ≤ u) (hq : 0 < q)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (hlive : ∀ ω ∈ E, z ∈ survivingDomain (γ ω) (τ ω))
    (hbase : ∀ ω ∈ E, fullRadius (G ω) (τ ω) z = (2 * z.im) * Real.exp (-u)) :
    ∃ M : Ω → ℝ≥0∞, Measurable[hτ.measurableSpace] M ∧
      (∀ ω, M ω ≠ ∞) ∧
      (∀ᵐ ω ∂P, ω ∈ E → M ω = ENNReal.ofReal
        (greenDensity κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (τ ω) z /
          initialGreen κ z)) ∧
      ∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
        (∫⁻ ω in A ∩ E, M ω ∂P) = finiteCenteredLaw P κ B γ G z (u + q) (A ∩ E) := by
  obtain ⟨V, Z, _, hZi, _, hZb, _, hVstop, hsource, _⟩ :=
    exists_physical_green_stopping_regular hB hBm hc hB0 κ hκ hκ8 γ G F
      (Eventually.of_forall hw) z hz (u + q) (by linarith)
  let C : Ω → ℝ := P[Z | hτ.measurableSpace]
  let M : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (C ω / initialGreen κ z)
  have hCm : Measurable[hτ.measurableSpace] C := stronglyMeasurable_condExp.measurable
  have he : P.withDensity (fun ω => ENNReal.ofReal (Z ω / initialGreen κ z)) =
      finiteCenteredLaw P κ B γ G z (u + q) := by
    apply withDensity_congr_ae
    filter_upwards [hsource] with ω hω
    rw [hω.2]
  refine ⟨M, ENNReal.measurable_ofReal.comp (hCm.div_const _),
    fun _ => ENNReal.ofReal_ne_top, ?_, ?_⟩
  · filter_upwards [hVstop τ hτ, hsource] with ω hVω hsrc hωE
    have hbefore := (hw ω).before_deeper_radius_level ((hc ω).const_mul _) z u q hu hq
      (τ ω) (hlive ω hωE) (hbase ω hωE)
    change ENNReal.ofReal (C ω / _) = _
    rw [show C ω = V (τ ω) ω from hVω.symm, hsrc.1 (τ ω), physicalStoppedGreen,
      ite_eq_right (not_le.mpr hbefore)]
  · intro A hA
    rw [← he]
    exact (normalizedDensity_measure_at_past P hτ.measurableSpace hτ.measurableSpace_le
      Z C hZi (Eventually.of_forall (fun ω => (hZb ω).1)) Filter.EventuallyEq.rfl
      (initialGreen κ z) (initialGreen_pos κ z hz) (A ∩ E) (hA.inter hE)).symm

end SLEExactGauge

end

end OAI
