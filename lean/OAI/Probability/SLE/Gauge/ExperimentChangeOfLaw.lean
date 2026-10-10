import OAI.Probability.SLE.Gauge.RandomPassageBounds
import OAI.Probability.SLE.InverseMoments

namespace OAI

/-! The finite centered law pays a uniform cost for an actual successful
experiment whose marked-point angle stays positive. Its finite completion
stop is used before the conformal-radius cutoff. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma greenDensity_lower_of_angle
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (T : ℝ≥0) (hT : z ∈ survivingDomain γ T)
    {s : ℝ} (hs : 0 ≤ s)
    (hangle : s ≤ Real.sin (Complex.arg (G T z - (U T : ℂ)))) :
    s ^ greenExponent κ * initialGreen κ z ≤ greenDensity κ U γ G T z := by
  have hR := hw.fullRadius_positive hU T z hT
  have hR0 := hw.fullRadius_initial hU z (survivingDomain_antitone γ zero_le hT)
  have hdec : fullRadius G T z ≤ 2 * z.im := by
    rw [← hR0]
    exact hw.radius_le_of_domain_subset hU T 0 (survivingDomain_antitone γ zero_le) z hT
  have hinit : initialGreen κ z ≤ (2 * z.im) ^ (-codimension κ) := by
    unfold initialGreen
    exact mul_le_of_le_one_right (Real.rpow_nonneg (mul_nonneg (by norm_num) hT.1.1.le) _)
      (Real.rpow_le_one (by
        rw [Complex.sin_arg]
        exact div_nonneg hT.1.1.le (norm_nonneg _))
        (Real.sin_le_one _) (greenExponent_pos κ hκ hκ8).le)
  have hp : (2 * z.im) ^ (-codimension κ) ≤ (fullRadius G T z) ^ (-codimension κ) :=
    Real.rpow_le_rpow_of_nonpos hR hdec (neg_nonpos.mpr (codimension_pos κ hκ8).le)
  have ha : s ^ greenExponent κ ≤
      (Real.sin (Complex.arg (G T z - (U T : ℂ)))) ^ greenExponent κ :=
    Real.rpow_le_rpow hs hangle (greenExponent_pos κ hκ hκ8).le
  rw [greenDensity, ite_eq_left hT]
  calc
    _ ≤ s ^ greenExponent κ * (2 * z.im) ^ (-codimension κ) :=
      mul_le_mul_of_nonneg_left hinit (Real.rpow_nonneg hs _)
    _ ≤ (Real.sin (Complex.arg (G T z - (U T : ℂ)))) ^ greenExponent κ *
        (fullRadius G T z) ^ (-codimension κ) :=
      mul_le_mul ha hp (Real.rpow_nonneg (mul_nonneg (by norm_num) hT.1.1.le) _) (Real.rpow_nonneg
        (hs.trans hangle) _)
    _ = _ := mul_comm _ _

/-- An event observed at a finite experiment stop transfers to the finite
radius law using its actual Green density there. -/
theorem finiteCenteredLaw_experiment_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B
      (fun _t => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (E : Set Ω) (hE : MeasurableSet[hσ.measurableSpace] E)
    (s : ℝ) (hs : 0 ≤ s)
    (hsuccess : ∀ᵐ ω ∂P, ω ∈ E →
      (σ ω : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u ∧
      z ∈ survivingDomain (γ ω) (σ ω) ∧
      s ≤ Real.sin (Complex.arg (G ω (σ ω) z - (Real.sqrt κ * B (σ ω) ω : ℂ)))) :
    ENNReal.ofReal (s ^ greenExponent κ) * P E ≤ finiteCenteredLaw P κ B γ G z u E := by
  obtain ⟨M, Z, _, hZi, _, hZb, _, hMstop, hsource, _⟩ :=
    exists_physical_green_stopping_regular hB hBm hBc hB0 κ hκ hκ8 γ G F hw z hz u hu
  have hbound : ∀ᵐ ω ∂P, ω ∈ E →
      s ^ greenExponent κ * initialGreen κ z ≤ M (σ ω) ω := by
    filter_upwards [hw, hsource, hsuccess] with ω hω hsrc hsucc hωE
    obtain ⟨hbefore, hlive, hangle⟩ := hsucc hωE
    rw [hsrc.1 (σ ω), physicalStoppedGreen, ite_eq_right (not_le.mpr hbefore)]
    exact greenDensity_lower_of_angle ((hBc ω).const_mul _) hω κ hκ hκ8 z
      (σ ω) hlive hs (by simpa only [Complex.ofReal_mul] using hangle)
  have h := normalizedDensity_event_lower_bound_of_condExp P hσ.measurableSpace
    hσ.measurableSpace_le Z (fun ω => M (σ ω) ω) hZi
    (Eventually.of_forall (fun ω => (hZb ω).1)) (hMstop σ hσ)
    (initialGreen κ z) (s ^ greenExponent κ) (initialGreen_pos κ z hz)
    (Real.rpow_nonneg hs _) E hE hbound
  have he : P.withDensity (fun ω => ENNReal.ofReal (Z ω / initialGreen κ z)) =
      finiteCenteredLaw P κ B γ G z u := by
    apply withDensity_congr_ae
    filter_upwards [hsource] with ω hω
    rw [hω.2]
  exact he ▸ h

end SLEExactGauge

end

end OAI
