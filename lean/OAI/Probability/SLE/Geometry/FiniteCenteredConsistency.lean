import OAI.Probability.SLE.Geometry.FiniteDensityAtPast
import OAI.Probability.SLE.Loewner.ActualRadiusStops
import OAI.Probability.SLE.Gauge.ExtendedExperimentStop

namespace OAI

/-! Exact consistency of the finite centered laws on the past of an
earlier conformal-radius stop. Extended stopping times are exhausted
through finite cutoffs; the finite centered laws give the earlier stop
finite time almost surely. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.physicalStoppedGreen_at_or_before
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (κ : ℝ) (z : ℂ) (u : ℝ) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤ radiusLevelTime γ G z u) :
    physicalStoppedGreen κ U γ G z u t = greenDensity κ U γ G t z := by
  by_cases hstop : radiusLevelTime γ G z u ≤ (t : ℝ≥0∞)
  · have he : radiusLevelTime γ G z u = (t : ℝ≥0∞) := le_antisymm hstop ht
    have hf : radiusLevelTime γ G z u < ∞ := by rw [he]; exact ENNReal.coe_lt_top
    obtain ⟨T, hT, hR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z u hf
    have hTt : T = t := by
      exact_mod_cast (radiusLevelTime_eq_of_live_level hU hw z u T hT hR).symm.trans he
    subst T
    rw [physicalStoppedGreen, ite_eq_left hstop,
      stoppedGreen_eq_of_live_level hU hw κ z u t hT hR]
  · exact ite_eq_right hstop

/-- Finite-stop consistency holds on the entire earlier stopped past,
including events on which the later radius level is never reached. -/
theorem finiteCenteredLaw_consistent_at_finite_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (v V : ℝ) (hv : 0 ≤ v) (hvV : v ≤ V)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B
      (fun _t => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hbefore : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) ≤ radiusLevelTime (γ ω) (G ω) z v)
    (A : Set Ω) (hA : MeasurableSet[hσ.measurableSpace] A) :
    finiteCenteredLaw P κ B γ G z V A = finiteCenteredLaw P κ B γ G z v A := by
  obtain ⟨Mv, Zv, _, hZvi, _, hZvn, _, hvstop, hvsrc, _⟩ :=
    exists_physical_green_stopping_regular hB hBm hc hB0 κ hκ hκ8 γ G F hw z hz v hv
  obtain ⟨MV, ZV, _, hZVi, _, hZVn, _, hVstop, hVsrc, _⟩ :=
    exists_physical_green_stopping_regular hB hBm hc hB0 κ hκ hκ8 γ G F hw z hz V (hv.trans hvV)
  have hvmeasure : P.withDensity (fun ω => ENNReal.ofReal (Zv ω / initialGreen κ z)) =
      finiteCenteredLaw P κ B γ G z v := by
    apply withDensity_congr_ae
    filter_upwards [hvsrc] with ω hω
    rw [hω.2]
  have hVmeasure : P.withDensity (fun ω => ENNReal.ofReal (ZV ω / initialGreen κ z)) =
      finiteCenteredLaw P κ B γ G z V := by
    apply withDensity_congr_ae
    filter_upwards [hVsrc] with ω hω
    rw [hω.2]
  have hev := normalizedDensity_measure_at_past P hσ.measurableSpace hσ.measurableSpace_le
    Zv (fun ω => Mv (σ ω) ω) hZvi (Eventually.of_forall (fun ω => (hZvn ω).1))
    (hvstop σ hσ) (initialGreen κ z) (initialGreen_pos κ z hz) A hA
  have heV := normalizedDensity_measure_at_past P hσ.measurableSpace hσ.measurableSpace_le
    ZV (fun ω => MV (σ ω) ω) hZVi (Eventually.of_forall (fun ω => (hZVn ω).1))
    (hVstop σ hσ) (initialGreen κ z) (initialGreen_pos κ z hz) A hA
  rw [hvmeasure] at hev
  rw [hVmeasure] at heV
  refine heV.trans ((lintegral_congr_ae ?_).trans hev.symm)
  filter_upwards [ae_restrict_of_ae hw, ae_restrict_of_ae hbefore,
    ae_restrict_of_ae hvsrc, ae_restrict_of_ae hVsrc] with ω hω hbef hvs hVs
  rw [hvs.1 (σ ω), hVs.1 (σ ω),
    hω.physicalStoppedGreen_at_or_before ((hc ω).const_mul _) κ z v (σ ω) hbef,
    hω.physicalStoppedGreen_at_or_before ((hc ω).const_mul _) κ z V (σ ω)
      (hbef.trans (radiusLevelTime_mono ((hc ω).const_mul _) hω z hv hvV))]

lemma stopped_past_cover_of_ae_finite
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (σ : Ω → WithTop ℝ≥0) (hfinite : ∀ᵐ ω ∂Q, σ ω ≠ ⊤) (A : Set Ω) :
    A =ᵐ[Q] ⋃ n : ℕ, A ∩ {ω | σ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} := by
  filter_upwards [hfinite] with ω hω
  simp only [mem_iUnion]
  apply propext
  constructor
  · intro hωA
    lift σ ω to ℝ≥0 using hω with t ht
    obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
    refine ⟨n, hωA, ?_⟩
    change σ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)
    rw [← ht]
    exact WithTop.coe_le_coe.mpr (by exact_mod_cast hn)
  · rintro ⟨n, hn⟩
    exact hn.1

/-- Every earlier stop is finite under a later finite centered law, even
when it is infinite on a set of positive original probability. -/
theorem finiteCenteredLaw_earlier_stop_ae_finite
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (v V : ℝ) (hv : 0 ≤ v) (hvV : v ≤ V)
    (σ : Ω → WithTop ℝ≥0)
    (hbefore : ∀ᵐ ω ∂P, σ ω ≤ radiusLevelTime (γ ω) (G ω) z v) :
    ∀ᵐ ω ∂finiteCenteredLaw P κ B γ G z V, σ ω ≠ ⊤ := by
  have hl := finiteCenteredLaw_live_compact hB κ hκ hκ8 γ G F hw z hz V (hv.trans hvV)
  filter_upwards [hl, (withDensity_absolutelyContinuous P _).ae_le hbefore,
    (withDensity_absolutelyContinuous P _).ae_le hw] with ω hω hb hW
  obtain ⟨t, _, _, ht, _⟩ := hω
  have hlt : σ ω < ⊤ :=
    (hb.trans (radiusLevelTime_mono ((hc ω).const_mul _) hW z hv hvV)).trans_lt
      (by rw [ht]; exact ENNReal.coe_lt_top)
  exact hlt.ne

/-- Extended-stop consistency. The sole geometric requirement is that
this stop occur no later than the earlier conformal-radius level almost
surely under the original law. -/
theorem finiteCenteredLaw_consistent_at_extended_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (v V : ℝ) (hv : 0 ≤ v) (hvV : v ≤ V)
    (σ : Ω → WithTop ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B
      (fun _t => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable)) σ)
    (hbefore : ∀ᵐ ω ∂P, σ ω ≤ radiusLevelTime (γ ω) (G ω) z v)
    (A : Set Ω) (hA : MeasurableSet[hσ.measurableSpace] A) :
    finiteCenteredLaw P κ B γ G z V A = finiteCenteredLaw P κ B γ G z v A := by
  let Qv := finiteCenteredLaw P κ B γ G z v
  let QV := finiteCenteredLaw P κ B γ G z V
  have hvfinite : ∀ᵐ ω ∂Qv, σ ω ≠ ⊤ :=
    finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F hw
      z hz v v hv le_rfl σ hbefore
  have hVfinite : ∀ᵐ ω ∂QV, σ ω ≠ ⊤ :=
    finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F hw
      z hz v V hv hvV σ hbefore
  let An (n : ℕ) := A ∩ {ω | σ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}
  have hmono : Monotone An := by
    intro n m hnm ω hω
    refine ⟨hω.1, ?_⟩
    change σ ω ≤ ((m : ℝ≥0) : WithTop ℝ≥0)
    exact hω.2.trans (WithTop.coe_le_coe.mpr (by exact_mod_cast hnm))
  have hlocal (n : ℕ) : QV (An n) = Qv (An n) := by
    let τ := cutoffStop σ (n : ℝ≥0)
    have hτ := cutoffStop_stopping _ σ hσ (n : ℝ≥0)
    apply finiteCenteredLaw_consistent_at_finite_stop hB hBm hc hB0 κ hκ hκ8
      γ G F hw z hz v V hv hvV τ hτ _ (An n)
      (cutoffStop_success_measurable _ σ hσ _ A hA)
    filter_upwards [hbefore] with ω hω
    exact (le_of_eq (cutoffStop_coe σ (n : ℝ≥0) ω)).trans ((min_le_left _ _).trans hω)
  calc
    QV A = QV (⋃ n, An n) := measure_congr (stopped_past_cover_of_ae_finite QV σ hVfinite A)
    _ = ⨆ n, QV (An n) := hmono.measure_iUnion
    _ = ⨆ n, Qv (An n) := by congr 1; funext n; exact hlocal n
    _ = Qv (⋃ n, An n) := hmono.measure_iUnion.symm
    _ = Qv A := (measure_congr (stopped_past_cover_of_ae_finite Qv σ hvfinite A)).symm

/-- The cover application: any stopping-time version of the actual
radius-v time has exactly the same stopped-past law under every later
finite centered measure. -/
theorem finiteCenteredLaw_consistent_at_radius_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (v V : ℝ) (hv : 0 ≤ v) (hvV : v ≤ V)
    (σ : Ω → WithTop ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B
      (fun _t => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable)) σ)
    (hactual : ∀ᵐ ω ∂P, σ ω = radiusLevelTime (γ ω) (G ω) z v)
    (A : Set Ω) (hA : MeasurableSet[hσ.measurableSpace] A) :
    finiteCenteredLaw P κ B γ G z V A = finiteCenteredLaw P κ B γ G z v A :=
  finiteCenteredLaw_consistent_at_extended_stop hB hBm hc hB0 κ hκ hκ8 γ G F hw
    z hz v V hv hvV σ hσ (hactual.mono fun _ h => h.le) A hA

end SLEExactGauge

end

end OAI
