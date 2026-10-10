import OAI.Probability.SLE.Loewner.CanonicalApproach
import OAI.Probability.SLE.Geometry.RestartSectionUpper
import OAI.Probability.SLE.Loewner.RestartDomainEquality
import OAI.Probability.SLE.Geometry.FiniteDensityAtRadiusState
import OAI.Probability.SLE.Geometry.StoppedMarkedStateMeasurability

namespace OAI

/-! The one-point approach estimate conditional on an actual finite stopped
past. The density on that past is the exact terminal finite-centered law. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance actualApproachDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance actualApproachDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance actualApproachPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance actualApproachPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma greenDensity_radius_factor
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (κ : ℝ) (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    (Real.sin (Complex.arg (G T z - (U T : ℂ)))) ^ greenExponent κ =
      (fullRadius G T z) ^ codimension κ * greenDensity κ U γ G T z := by
  have hR := hw.fullRadius_positive hU T z hz
  rw [greenDensity, ite_eq_left hz, ← mul_assoc, ← Real.rpow_add hR,
    add_neg_cancel, Real.rpow_zero, one_mul]

theorem actual_conditional_radius_approach
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (htrace : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B
      (fun _t => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (v : ℝ≥0) (hv : 1 ≤ (v : ℝ))
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (hlive : ∀ ω ∈ E, z ∈ survivingDomain (γ ω) (τ ω))
    (hbase : ∀ ω ∈ E, fullRadius (G ω) (τ ω) z = (2 * z.im) * Real.exp (-u))
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
    P (A ∩ E ∩ {ω | radiusLevelTime (γ ω) (G ω) z (u + v) < ∞}) ≤
      ENNReal.ofReal (uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
        ((2 * z.im) * Real.exp (-u)) ^ codimension κ * initialGreen κ z) *
        finiteCenteredLaw P κ B γ G z (u + v) (A ∩ E) := by
  classical
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let ν := P.map (sourceDriverPath B hc)
  have hbp : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hbp.aemeasurable).mpr inferInstance
  obtain ⟨Φ, Gc, Fc, hΦ, hW⟩ := exists_measurable_canonical_witness ν κ htrace
  let Y := sourceRestartDriverPath B hc τ
  have hY : Measurable Y := source_path_measurable Y (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hc
      (stopping_time_measurable_nnreal hτ)))
  have hYlaw (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
      (P.restrict A).map Y = P A • ν :=
    source_restart_continuous_driver_law hB hm hc τ hτ hA
  have hYlaw₀ : P.map Y = ν := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using hYlaw univ MeasurableSet.univ
  have hdriver (ω : Ω) : (fun t => Real.sqrt κ * Y ω t) =
      (fun t => Real.sqrt κ * B (τ ω + t) ω - Real.sqrt κ * B (τ ω) ω) := by
    funext t
    exact mul_sub _ _ _
  have hrestart := canonical_witness_pullback hW Y hY hYlaw₀
  let w := stoppedMarkedCenter κ B γ G τ z
  have hwm : Measurable[hτ.measurableSpace] w :=
    source_stoppedMarkedCenter_measurable B hm hc κ γ G F hw τ hτ z
  have hwH (ω : Ω) (hω : ω ∈ E) : w ω ∈ upperHalfPlane := by
    dsimp only [w]
    rw [stoppedMarkedCenter_eq κ B γ G τ z ω (hlive ω hω)]
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im, sub_zero]
      using (hw ω).imag_positive (τ ω) z (hlive ω hω)
  have hpoint (ω : Ω) (hω : ω ∈ E) :
      F ω (τ ω) (w ω + (Real.sqrt κ * B (τ ω) ω : ℝ)) = z := by
    dsimp only [w]
    rw [stoppedMarkedCenter_eq κ B γ G τ z ω (hlive ω hω), sub_add_cancel]
    exact (hw ω).2.2.2.2.2.2.2.1 _ _ (hlive ω hω)
  let C : Set (Ω × C(ℝ≥0, ℝ)) :=
    {p | canonicalRadiusLevel κ ((v : ℝ), w p.1, p.2) < ∞}
  have hC : @MeasurableSet (Ω × C(ℝ≥0, ℝ))
      (hτ.measurableSpace.prod inferInstance) C :=
    @measurableSet_lt _ _ _ _ _ (hτ.measurableSpace.prod inferInstance) _ _ _ _ _
      ((canonicalRadiusLevel_measurable κ).comp
        (measurable_const.prodMk ((hwm.comp measurable_fst).prodMk measurable_snd))) measurable_const
  let r : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
      (Real.sin (Complex.arg (w ω))) ^ greenExponent κ)
  have hsections (ω : Ω) (hω : ω ∈ E) : ν {p | (ω, p) ∈ C} ≤ r ω :=
    canonical_radius_approach ν (canonical_driver_isBrownian B hB hm hc) κ hκ hκ8
      Φ Gc Fc hW (w ω) (hwH ω hω) v hv
  have hactual : ∀ᵐ ω ∂P, ω ∈ E →
      radiusLevelTime (γ ω) (G ω) z (u + v) < ∞ → (ω, Y ω) ∈ C := by
    filter_upwards [hrestart] with ω hω hωE hfinite
    have hω' := hdriver ω ▸ hω
    have hbase' := hbase ω hωE
    rw [← hpoint ω hωE] at hbase' hfinite
    have hs := ((hw ω).restart_radius_finite_iff ((hc ω).const_mul _) (τ ω) hω'
      (w ω) (hwH ω hωE) u v hu (by linarith) hbase').mp hfinite
    change canonicalRadiusLevel κ ((v : ℝ), w ω, Y ω) < ∞
    rwa [canonicalRadiusLevel_eq κ (Y ω) hω _ v.coe_nonneg (w ω)]
  have hbound := restart_event_section_upper_bound P ν hτ.measurableSpace hτ.measurableSpace_le
    Y hY hYlaw C hC E hE {ω | radiusLevelTime (γ ω) (G ω) z (u + v) < ∞}
    r hsections hactual A hA
  obtain ⟨M, _, _, hMactual, hMpast⟩ :=
    exists_finiteDensity_at_radius_state hB hBm hc hB0 κ hκ hκ8 γ G F hw
      τ hτ z hz u v hu (by linarith) E hE hlive hbase
  let K := uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
    ((2 * z.im) * Real.exp (-u)) ^ codimension κ * initialGreen κ z
  have hK0 : 0 ≤ K := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num)).le (Real.exp_pos _).le)
      (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) hz.le) (Real.exp_pos _).le) _))
      (initialGreen_pos κ z hz).le
  have heq : r =ᵐ[P.restrict (A ∩ E)] (fun ω => ENNReal.ofReal K * M ω) := by
    filter_upwards [ae_restrict_of_ae hMactual, ae_restrict_mem (hτ.measurableSpace_le _ (hA.inter hE))]
      with ω hMω hω
    rw [hMω hω.2, ← ENNReal.ofReal_mul hK0]
    apply congrArg ENNReal.ofReal
    dsimp only [r, K, w]
    rw [stoppedMarkedCenter_eq κ B γ G τ z ω (hlive ω hω.2),
      greenDensity_radius_factor (hw ω) ((hc ω).const_mul _) κ (τ ω) z (hlive ω hω.2),
      hbase ω hω.2]
    field_simp [(initialGreen_pos κ z hz).ne']
  calc
    _ ≤ ∫⁻ ω in A ∩ E, r ω ∂P := hbound
    _ = ∫⁻ ω in A ∩ E, ENNReal.ofReal K * M ω ∂P := lintegral_congr_ae heq
    _ = ENNReal.ofReal K * (∫⁻ ω in A ∩ E, M ω ∂P) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [hMpast A hA]

end SLEExactGauge

end

end OAI
