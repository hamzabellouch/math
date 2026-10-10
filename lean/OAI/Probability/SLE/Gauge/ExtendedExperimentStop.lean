import OAI.Probability.SLE.Gauge.ExperimentChangeOfLaw

namespace OAI

/-! A completion stop may be infinite on failure. Restrict success to
finite deterministic horizons, apply the finite-stop density identity,
and then exhaust the successful event. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def cutoffStop {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (H : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (τ ω) (H : WithTop ℝ≥0)).untopD 0

lemma cutoffStop_coe {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (H : ℝ≥0) (ω : Ω) :
    (cutoffStop τ H ω : WithTop ℝ≥0) = min (τ ω) (H : WithTop ℝ≥0) := by
  cases h : τ ω with
  | top => simp only [cutoffStop, h, min_top_left, WithTop.untopD_coe]
  | coe t => simp only [cutoffStop, h, ← WithTop.coe_min, WithTop.untopD_coe]

lemma cutoffStop_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ) (H : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => (cutoffStop τ H ω : WithTop ℝ≥0)) := by
  have he : (fun ω => (cutoffStop τ H ω : WithTop ℝ≥0)) =
      fun ω => min (τ ω) (H : WithTop ℝ≥0) := funext (cutoffStop_coe τ H)
  rw [he]
  exact hτ.min_const H

lemma cutoffStop_success_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ) (H : ℝ≥0)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E) :
    MeasurableSet[(cutoffStop_stopping ℱ τ hτ H).measurableSpace]
      (E ∩ {ω | τ ω ≤ (H : WithTop ℝ≥0)}) := by
  have hh := hτ.measurableSet_inter_le (isStoppingTime_const ℱ H) E hE
  rw [IsStoppingTime.measurableSet] at hh ⊢
  exact ⟨hh.1, fun t => by simpa only [cutoffStop_coe] using hh.2 t⟩

lemma cutoffStop_eq_on_success {Ω : Type*}
    (τ : Ω → WithTop ℝ≥0) (H : ℝ≥0) (ω : Ω) (hω : τ ω ≤ (H : WithTop ℝ≥0)) :
    cutoffStop τ H ω = (τ ω).untopD 0 := by
  simp only [cutoffStop, min_eq_left hω]

/-- The normalized terminal density pays the same fixed cost when the
completion stop is finite only on success. -/
theorem normalizedDensity_completed_event_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ)
    (Z : Ω → ℝ) (hZ : Integrable Z P) (hZpos : 0 ≤ᵐ[P] Z)
    (M : ℝ≥0 → Ω → ℝ)
    (hM : ∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime ℱ
        (fun ω => (σ ω : WithTop ℝ≥0))),
      (fun ω => M (σ ω) ω) =ᵐ[P] P[Z | hσ.measurableSpace])
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (hfinite : ∀ᵐ ω ∂P, ω ∈ E → τ ω ≠ ⊤)
    (hbound : ∀ᵐ ω ∂P, ω ∈ E → c * a ≤ M ((τ ω).untopD 0) ω) :
    ENNReal.ofReal c * P E ≤
      P.withDensity (fun ω => ENNReal.ofReal (Z ω / a)) E := by
  let Eₙ (n : ℕ) := E ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}
  have hmono : Monotone Eₙ := by
    intro n k hnk ω hω
    refine ⟨hω.1, ?_⟩
    change τ ω ≤ ((k : ℝ≥0) : WithTop ℝ≥0)
    exact hω.2.trans (WithTop.coe_le_coe.mpr (by exact_mod_cast hnk))
  have hcover : E =ᵐ[P] ⋃ n, Eₙ n := by
    filter_upwards [hfinite] with ω hω
    simp only [mem_iUnion]
    apply propext
    constructor
    · intro hωE
      lift τ ω to ℝ≥0 using hω hωE with t ht
      obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
      refine ⟨n, hωE, ?_⟩
      change τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)
      rw [← ht]
      exact WithTop.coe_le_coe.mpr (by exact_mod_cast hn)
    · rintro ⟨n, hn⟩
      exact hn.1
  have hlocal (n : ℕ) : ENNReal.ofReal c * P (Eₙ n) ≤
      P.withDensity (fun ω => ENNReal.ofReal (Z ω / a)) (Eₙ n) := by
    let σ := cutoffStop τ (n : ℝ≥0)
    have hσ := cutoffStop_stopping ℱ τ hτ (n : ℝ≥0)
    apply normalizedDensity_event_lower_bound_of_condExp P hσ.measurableSpace
      hσ.measurableSpace_le Z (fun ω => M (σ ω) ω) hZ hZpos (hM σ hσ)
      a c ha hc (Eₙ n) (cutoffStop_success_measurable ℱ τ hτ _ E hE)
    filter_upwards [hbound] with ω hb hω
    change c * a ≤ M (cutoffStop τ (n : ℝ≥0) ω) ω
    rw [cutoffStop_eq_on_success τ _ ω hω.2]
    exact hb hω.1
  calc
    _ = ENNReal.ofReal c * P (⋃ n, Eₙ n) := by rw [measure_congr hcover]
    _ = ⨆ n, ENNReal.ofReal c * P (Eₙ n) := by
      rw [hmono.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ _ := iSup_le fun n => (hlocal n).trans (measure_mono inter_subset_left)

/-- The successful dense experiment need not finish on unsuccessful
samples. Its actual finite completion and angle bound on success suffice
for the centered-law lower bound. -/
theorem finiteCenteredLaw_completed_experiment_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B
      (fun _t => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable)) τ)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (s : ℝ) (hs : 0 ≤ s)
    (hsuccess : ∀ᵐ ω ∂P, ω ∈ E → τ ω ≠ ⊤ ∧
      τ ω < radiusLevelTime (γ ω) (G ω) z u ∧
      z ∈ survivingDomain (γ ω) ((τ ω).untopD 0) ∧
      s ≤ Real.sin (Complex.arg
        (G ω ((τ ω).untopD 0) z - (Real.sqrt κ * B ((τ ω).untopD 0) ω : ℂ)))) :
    ENNReal.ofReal (s ^ greenExponent κ) * P E ≤ finiteCenteredLaw P κ B γ G z u E := by
  obtain ⟨M, Z, _, hZi, _, hZb, _, hMstop, hsource, _⟩ :=
    exists_physical_green_stopping_regular hB hBm hBc hB0 κ hκ hκ8 γ G F hw z hz u hu
  have hbound : ∀ᵐ ω ∂P, ω ∈ E →
      s ^ greenExponent κ * initialGreen κ z ≤ M ((τ ω).untopD 0) ω := by
    filter_upwards [hw, hsource, hsuccess] with ω hω hsrc hsucc hωE
    obtain ⟨hfinite, hbefore, hlive, hangle⟩ := hsucc hωE
    have he : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) = τ ω := by
      cases ht : τ ω with
      | top => exact (hfinite ht).elim
      | coe t => simp only [WithTop.untopD_coe]; rfl
    rw [hsrc.1 ((τ ω).untopD 0), physicalStoppedGreen,
      ite_eq_right (not_le.mpr (he.symm ▸ hbefore))]
    exact greenDensity_lower_of_angle ((hBc ω).const_mul _) hω κ hκ hκ8 z
      ((τ ω).untopD 0) hlive hs (by simpa only [Complex.ofReal_mul] using hangle)
  have h := normalizedDensity_completed_event_lower_bound P _ Z hZi
    (Eventually.of_forall (fun ω => (hZb ω).1)) M hMstop τ hτ
    (initialGreen κ z) (s ^ greenExponent κ) (initialGreen_pos κ z hz)
    (Real.rpow_nonneg hs _) E hE (hsuccess.mono fun _ hω hωE => (hω hωE).1) hbound
  have he : P.withDensity (fun ω => ENNReal.ofReal (Z ω / initialGreen κ z)) =
      finiteCenteredLaw P κ B γ G z u := by
    apply withDensity_congr_ae
    filter_upwards [hsource] with ω hω
    rw [hω.2]
  exact he ▸ h

end SLEExactGauge

end

end OAI
