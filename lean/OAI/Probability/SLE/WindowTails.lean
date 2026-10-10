import Mathlib
import OAI.Probability.SLE.WindowBounds

namespace OAI

/-! Window Tails for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
namespace SLEExactGauge
noncomputable section
universe u_source_spatial
def SourceSpatialConditionalMeanTarget : Prop :=
  ∀ (Ω : Type u_source_spatial) (_ : MeasurableSpace Ω) (P : Measure Ω),
  IsProbabilityMeasure P → ∀ (κ : ℝ), 0 < κ → κ < 8 →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (z : ℂ) (ε r : ℝ), 0 < ε → ε ≤ r → r ≤ z.im →
  ∃ hτ : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r),
    let μ := P.comap (Subtype.val : a.samples → Ω)
    let W := fun v ω => spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) z v
    μ[W ε | hτ.measurableSpace] =ᵐ[μ] W r ∧
    ∀ Y : a.samples → ℝ, Integrable Y μ → Y ≤ᵐ[μ] W ε →
      μ[Y | hτ.measurableSpace] ≤ᵐ[μ] W r

lemma spatialHitTime_antitone_radius {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) {ε r : ℝ} (hεr : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    spatialHitTime γ z r ≤ spatialHitTime γ z ε := by
  by_cases he : spatialHitTime γ z ε = ⊤
  · rw [he]; exact le_top
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp he
  rw [← ht]
  have hd := spatialHitTime_mem hc z ε t ht.symm
  exact spatialHitTime_le_of_dist_le hc z r hs t (hd.le.trans hεr)

lemma source_nested_stops_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 mΩ) (τ σ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hτσ : τ ≤ σ)
    (M : ℝ≥0 → Ω → ℝ) (Z V W : Ω → ℝ) (hZ : Integrable Z μ)
    (hStop : ∀ (ρ : Ω → ℝ≥0) (hρ : IsStoppingTime ℱ (fun ω => (ρ ω : WithTop ℝ≥0))),
      (fun ω => M (ρ ω) ω) =ᵐ[μ] μ[Z | hρ.measurableSpace])
    (K : ℝ) (hbound : ∀ t ω, ‖M t ω‖ ≤ K)
    (hVlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (sourceStopTruncate τ n ω) ω) atTop (𝓝 (V ω)))
    (hWlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (sourceStopTruncate σ n ω) ω) atTop (𝓝 (W ω)))
    (hzero : ∀ ω, τ ω = ⊤ → V ω = 0 ∧ W ω = 0)
    (hterm : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, τ ω ≤ (t : WithTop ℝ≥0) → M (sourceStopTruncate τ t ω) ω = V ω) :
    μ[W | hτ.measurableSpace] =ᵐ[μ] V := by
  let τn := sourceStopTruncate τ
  let σn := sourceStopTruncate σ
  have hτn (t : ℝ≥0) := sourceStopTruncate_stopping ℱ hτ t
  have hσn (t : ℝ≥0) := sourceStopTruncate_stopping ℱ hσ t
  have hVi (t : ℝ≥0) : Integrable (fun ω => M (τn t ω) ω) μ :=
    integrable_condExp.congr (hStop (τn t) (hτn t)).symm
  have hWi (t : ℝ≥0) : Integrable (fun ω => M (σn t ω) ω) μ :=
    integrable_condExp.congr (hStop (σn t) (hσn t)).symm
  have hVm (n : ℕ) : StronglyMeasurable[hτ.measurableSpace]
      (μ[Z | (hτn n).measurableSpace]) := by
    apply stronglyMeasurable_condExp.mono
    apply IsStoppingTime.measurableSpace_mono
    intro ω
    dsimp only
    rw [sourceStopTruncate_coe]
    exact min_le_left _ _
  have hVmeas : AEStronglyMeasurable[hτ.measurableSpace] V μ := by
    refine ⟨fun ω => limUnder atTop (fun n : ℕ => μ[Z | (hτn n).measurableSpace] ω),
      (by
        let : MeasurableSpace Ω := hτ.measurableSpace
        exact StronglyMeasurable.limUnder hVm), ?_⟩
    filter_upwards [hVlim, ae_all_iff.mpr (fun n : ℕ => hStop (τn n) (hτn n))] with ω hω he
    have hf : (fun n : ℕ => μ[Z | (hτn n).measurableSpace] ω) =
        (fun n : ℕ => M (τn n ω) ω) := funext fun n => (he n).symm
    rw [hf]
    exact hω.limUnder_eq.symm
  have hVint : Integrable V μ := by
    apply Integrable.of_bound (hVmeas.mono hτ.measurableSpace_le) K
    filter_upwards [hVlim] with ω hω
    exact le_of_tendsto hω.norm (Eventually.of_forall fun n => hbound _ _)
  have hWint : Integrable W μ := by
    apply Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop
      (fun n : ℕ => (hWi n).aestronglyMeasurable) hWlim) K
    filter_upwards [hWlim] with ω hω
    exact le_of_tendsto hω.norm (Eventually.of_forall fun n => hbound _ _)
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hWint
    (fun _ _ _ => hVint.integrableOn) _ hVmeas
  intro A hA _
  have hAm (m : ℕ) : MeasurableSet[(hτn m).measurableSpace]
      (A ∩ {ω | τ ω ≤ (m : ℝ≥0)}) := by
    have hh := hτ.measurableSet_inter_le (isStoppingTime_const ℱ (m : ℝ≥0)) A hA
    convert hh using 1
    · congr 1
      funext ω
      exact sourceStopTruncate_coe τ m ω
  have hset (m : ℕ) : (∫ ω in A ∩ {ω | τ ω ≤ (m : ℝ≥0)}, V ω ∂μ) =
      ∫ ω in A ∩ {ω | τ ω ≤ (m : ℝ≥0)}, W ω ∂μ := by
    let E := A ∩ {ω | τ ω ≤ (m : ℝ≥0)}
    have hI : Tendsto (fun n : ℕ => ∫ ω in E, M (σn n ω) ω ∂μ) atTop
        (𝓝 (∫ ω in E, W ω ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => K)
        (fun n => (hWi n).integrableOn.aestronglyMeasurable)
        (integrable_const _) _ (ae_restrict_of_ae hWlim)
      intro n
      exact Eventually.of_forall fun ω => hbound _ _
    have he : ∀ᶠ n : ℕ in atTop, (∫ ω in E, M (σn n ω) ω ∂μ) =
        ∫ ω in E, V ω ∂μ := by
      filter_upwards [eventually_ge_atTop m] with n hn
      have hmn : (m : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hn
      have hle : (hτn m).measurableSpace ≤ (hσn n).measurableSpace := by
        apply IsStoppingTime.measurableSpace_mono
        intro ω
        dsimp only
        rw [sourceStopTruncate_coe, sourceStopTruncate_coe]
        exact min_le_min (hτσ ω) (WithTop.coe_le_coe.mpr hmn)
      have h1 : (∫ ω in E, M (σn n ω) ω ∂μ) = ∫ ω in E, Z ω ∂μ := by
        rw [integral_congr_ae (ae_restrict_of_ae (hStop (σn n) (hσn n)))]
        have : IsFiniteMeasure (μ.trim (hσn n).measurableSpace_le) := isFiniteMeasure_trim _
        exact setIntegral_condExp (hσn n).measurableSpace_le hZ (hle E (hAm m))
      have h2 : (∫ ω in E, M (τn m ω) ω ∂μ) = ∫ ω in E, Z ω ∂μ := by
        rw [integral_congr_ae (ae_restrict_of_ae (hStop (τn m) (hτn m)))]
        have : IsFiniteMeasure (μ.trim (hτn m).measurableSpace_le) := isFiniteMeasure_trim _
        exact setIntegral_condExp (hτn m).measurableSpace_le hZ (hAm m)
      rw [h1, ← h2]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hterm, ae_restrict_mem
        ((hτn m).measurableSpace_le E (hAm m))] with ω hω hE
      exact hω m hE.2
    have hc : Tendsto (fun n : ℕ => ∫ ω in E, M (σn n ω) ω ∂μ) atTop
        (𝓝 (∫ ω in E, V ω ∂μ)) := tendsto_const_nhds.congr' (he.mono fun n hn => hn.symm)
    exact (tendsto_nhds_unique hI hc).symm
  have hlim (f : Ω → ℝ) (hf : Integrable f μ) (hz : ∀ ω, τ ω = ⊤ → f ω = 0) :
      Tendsto (fun n : ℕ => ∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, f ω ∂μ) atTop
        (𝓝 (∫ ω in A, f ω ∂μ)) := by
    have he (n : ℕ) : (∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, f ω ∂μ) =
        ∫ ω in A, {ω | τ ω ≤ (n : ℝ≥0)}.indicator f ω ∂μ :=
      (setIntegral_indicator (μ := μ) (s := A) (f := f)
        ((ℱ.le (n : ℝ≥0)) _ (hτ n))).symm
    simp_rw [he]
    apply tendsto_integral_of_dominated_convergence (fun ω => ‖f ω‖)
      (fun n => (hf.indicator ((ℱ.le (n : ℝ≥0)) _ (hτ n))).integrableOn.aestronglyMeasurable)
      hf.norm.integrableOn
    · intro n
      exact Eventually.of_forall fun ω => norm_indicator_le_norm_self _ _
    · apply Eventually.of_forall
      intro ω
      apply (sourceStop_indicator_tendsto (τ ω) (f ω) (hz ω)).congr'
      apply Eventually.of_forall
      intro n
      classical
      by_cases hn : τ ω ≤ (n : WithTop ℝ≥0) <;> simp [Set.indicator, hn]
  have h1 := hlim V hVint (fun ω hω => (hzero ω hω).1)
  have h2 := hlim W hWint (fun ω hω => (hzero ω hω).2)
  exact tendsto_nhds_unique (h1.congr' (Eventually.of_forall hset)) h2

 

theorem sourceSpatialConditionalMean_proved : SourceSpatialConditionalMeanTarget := by
  intro Ω mΩ P hP κ hκ hκ8 γ a z ε r hε hεr hry
  let : IsProbabilityMeasure P := hP
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  let τ (ω : a.samples) := spatialHitTime (γ ω) z r
  let σ (ω : a.samples) := spatialHitTime (γ ω) z ε
  have hτ : IsStoppingTime a.filtration τ :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r
  have hσ : IsStoppingTime a.filtration σ :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z ε
  refine ⟨hτ, ?_⟩
  let W (v : ℝ) (ω : a.samples) := spatialGreenWeight κ
    (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z v
  change μ[W ε | hτ.measurableSpace] =ᵐ[μ] W r ∧
    ∀ Y : a.samples → ℝ, Integrable Y μ → Y ≤ᵐ[μ] W ε →
      μ[Y | hτ.measurableSpace] ≤ᵐ[μ] W r
  have hr : 0 < r := hε.trans_le hεr
  have hz : z ∈ upperHalfPlane := hr.trans_le hry
  have hεy : ε ≤ z.im := hεr.trans hry
  have hτσ : τ ≤ σ := by
    intro ω
    apply spatialHitTime_antitone_radius (a.trace_continuous ω) z hεr
    rw [(a.witness ω).2.1, dist_zero_left]
    exact hry.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  let u := Real.log (4 * z.im / ε)
  have hratio : 0 < 4 * z.im / ε := div_pos (mul_pos (by norm_num) hz) hε
  have hu : 0 ≤ u := Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith))
  have hlev : (2 * z.im) * Real.exp (-u) = ε / 2 := by
    dsimp only [u]
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp [(show 0 < z.im from hz).ne']
    ring
  have hlevelε : (2 * z.im) * Real.exp (-u) < ε := by rw [hlev]; linarith
  have hlevelr := hlevelε.trans_le hεr
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  obtain ⟨M, Z, hM, hZ, hMb, hZb, hClosed, hStop, heq, hNoHit⟩ :=
    exists_physical_green_stopping_regular a.brownian hBm a.continuous_B a.zero_B
      κ hκ hκ8 (γ ∘ Subtype.val) a.G a.F (Eventually.of_forall a.witness) z hz u hu
  have hVlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (sourceStopTruncate τ n ω) ω)
      atTop (𝓝 (W r ω)) := by
    filter_upwards [heq, hNoHit] with ω he hn
    simpa only [he.1, τ, W, sourceStopTruncate, boundedSpatialHit, Function.comp_apply] using
      (a.witness ω).spatialGreen_limit ((a.continuous_B ω).const_mul _)
        κ z r hr hry u hlevelr hn
  have hWlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (sourceStopTruncate σ n ω) ω)
      atTop (𝓝 (W ε ω)) := by
    filter_upwards [heq, hNoHit] with ω he hn
    simpa only [he.1, σ, W, sourceStopTruncate, boundedSpatialHit, Function.comp_apply] using
      (a.witness ω).spatialGreen_limit ((a.continuous_B ω).const_mul _)
        κ z ε hε hεy u hlevelε hn
  have hzero : ∀ ω, τ ω = ⊤ → W r ω = 0 ∧ W ε ω = 0 := by
    intro ω hω
    have hσtop : σ ω = ⊤ := top_unique (hω ▸ hτσ ω)
    simp only [τ] at hω
    simp only [σ] at hσtop
    simp [W, spatialGreenWeight, hω, hσtop]
  have hterm : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, τ ω ≤ (t : WithTop ℝ≥0) →
      M (sourceStopTruncate τ t ω) ω = W r ω := by
    filter_upwards [heq] with ω he
    intro t ht
    have hn : spatialHitTime (γ ω) z r ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top ht
    have htrunc : sourceStopTruncate τ t ω = (spatialHitTime (γ ω) z r).untopD 0 := by
      exact congrArg (fun v : WithTop ℝ≥0 => v.untopD 0) (min_eq_left ht)
    have hle : (((spatialHitTime (γ ω) z r).untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤
        spatialHitTime (γ ω) z r := by
      obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hn
      rw [← hv, WithTop.untopD_coe]
    change M (sourceStopTruncate τ t ω) ω =
      if spatialHitTime (γ ω) z r = ⊤ then 0 else
        greenDensity κ (fun s => Real.sqrt κ * a.B s ω) (γ ω) (a.G ω)
          ((spatialHitTime (γ ω) z r).untopD 0) z
    rw [ite_eq_right hn, htrunc, he.1]
    exact (a.witness ω).physicalGreen_eq_before_spatial ((a.continuous_B ω).const_mul _)
      κ z r hr hry u hlevelr _ hle
  have hcond := source_nested_stops_condExp a.filtration τ σ hτ hσ hτσ M Z (W r) (W ε)
    hZ hStop (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
    (fun t ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hMb t ω).1]; exact (hMb t ω).2)
    hVlim hWlim hzero hterm
  refine ⟨hcond, ?_⟩
  intro Y hY hYW
  have hWi := (a.spatialGreen_expectation hκ hκ8 z ε hε hεy).1
  have hle := condExp_mono (m := hτ.measurableSpace) hY hWi hYW
  filter_upwards [hcond, hle] with ω hω hi
  exact hi.trans_eq hω

end
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

 

lemma source_condExp_le_changed_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 mΩ) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hle : σ ≤ τ) (A : Set Ω) (hA : MeasurableSet[hσ.measurableSpace] A)
    (heq : ∀ ω ∈ A, τ ω = σ ω)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hgm : StronglyMeasurable[hσ.measurableSpace] g)
    (hf0 : ∀ ω ∉ A, f ω = 0) (hg0 : ∀ ω ∉ A, g ω = 0)
    (hbound : μ[f | hσ.measurableSpace] ≤ᵐ[μ] g) :
    μ[f | hτ.measurableSpace] ≤ᵐ[μ] g := by
  have hm := hσ.measurableSpace_mono hτ hle
  apply source_condExp_le_of_setIntegral_le hτ.measurableSpace_le hf hg (hgm.mono hm)
  intro E hE
  have hEA : MeasurableSet[hσ.measurableSpace] (E ∩ A) := by
    have hh := hτ.measurableSet_inter_le hσ E hE
    have hraw : MeasurableSet[hσ.measurableSpace] (E ∩ {ω | τ ω ≤ σ ω}) :=
      (IsStoppingTime.measurableSet_min_iff hτ hσ _).mp hh |>.2
    have hsub : A ⊆ {ω | τ ω ≤ σ ω} := fun ω hω => (heq ω hω).le
    convert hraw.inter hA using 1
    exact (Set.inter_assoc _ _ _ |>.trans (congrArg (Set.inter E) (Set.inter_eq_right.mpr hsub))).symm
  have hfi : A.indicator f = f := by
    funext ω
    by_cases hω : ω ∈ A
    · exact Set.indicator_of_mem hω _
    · rw [Set.indicator_of_notMem hω, hf0 ω hω]
  have hgi : A.indicator g = g := by
    funext ω
    by_cases hω : ω ∈ A
    · exact Set.indicator_of_mem hω _
    · rw [Set.indicator_of_notMem hω, hg0 ω hω]
  have hAm := hσ.measurableSpace_le _ hA
  rw [← hfi, setIntegral_indicator hAm, ← hgi, setIntegral_indicator hAm]
  rw [← setIntegral_condExp hσ.measurableSpace_le hf hEA]
  exact setIntegral_mono_ae integrable_condExp.integrableOn hg.integrableOn hbound

lemma source_windowHB_range (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) :
    (sourceSpatialWindowH γ z r ε R = 0 ∨ sourceSpatialWindowH γ z r ε R = 1) ∧
    (sourceSpatialWindowB γ z r ε R = 0 ∨ sourceSpatialWindowB γ z r ε R = 1) := by
  constructor <;> (first | unfold sourceSpatialWindowH | unfold sourceSpatialWindowB) <;>
    split_ifs <;> simp

lemma source_windowHB_zero {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (hs : liveSpatialHitTime γ z r = ⊤) :
    sourceSpatialWindowH γ z r ε R = 0 ∧ sourceSpatialWindowB γ z r ε R = 0 := by
  have ht : sourceSpatialWindowTime γ z r ε R = ⊤ :=
    top_unique (by simpa only [hs] using source_window_start_le hc z r ε R)
  simp only [sourceSpatialWindowH,sourceSpatialWindowB,ht,ne_eq,not_true_eq_false,false_and,ite_false,and_self]

lemma source_windowH_le_indicator {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    sourceSpatialWindowH γ z r ε R ≤
      (if liveSpatialHitTime γ z ε = ⊤ then (0:ℝ) else 1) := by
  rcases (source_windowHB_range γ z r ε R).1 with h | h
  · rw [h]; split_ifs <;> norm_num
  · rw [h, ite_eq_right ((source_windowH_iff hc z r ε R her hs).mp h).2]

end
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_window_origin_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r : ℝ)
    (hy : r ≤ z.im) (ω : a.samples) : r ≤ dist (γ ω 0) z := by
  rw [(a.witness ω).2.1,dist_zero_left]
  exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))

lemma source_window_change_live_mean
    {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (z : ℂ) (r : ℝ) (hy : r ≤ z.im)
    (hraw : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r))
    (hs : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r))
    (f g : a.samples → ℝ)
    (hf : Integrable f (P.comap Subtype.val)) (hg : Integrable g (P.comap Subtype.val))
    (hgm : StronglyMeasurable[hraw.measurableSpace] g)
    (hf0 : ∀ ω : a.samples, liveSpatialHitTime (γ ω) z r = ⊤ → f ω = 0)
    (hg0 : ∀ ω : a.samples, liveSpatialHitTime (γ ω) z r = ⊤ → g ω = 0)
    (hbound : (P.comap Subtype.val)[f | hraw.measurableSpace] ≤ᵐ[P.comap Subtype.val] g) :
    (P.comap Subtype.val)[f | hs.measurableSpace] ≤ᵐ[P.comap Subtype.val] g := by
  let : IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) := a.probability
  let A := {ω : a.samples | z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z r).untopA}
  have hA : MeasurableSet[hraw.measurableSpace] A := source_live_stopped_measurable a z hraw
  have he (ω : a.samples) : liveSpatialHitTime (γ ω) z r =
      if ω ∈ A then spatialHitTime (γ ω) z r else ⊤ :=
    source_liveTime_eq_killed (a.trace_continuous ω) z r (source_window_origin_bound a z r hy ω)
  have hle : (fun ω : a.samples => spatialHitTime (γ ω) z r) ≤
      (fun ω : a.samples => liveSpatialHitTime (γ ω) z r) := by
    intro ω; dsimp only; rw [he]; split_ifs <;> first | exact le_rfl | exact le_top
  apply source_condExp_le_changed_stop a.filtration hraw hs hle A hA
    (fun ω hω => by rw [he,ite_eq_left hω]) hf hg hgm
  · intro ω hω; exact hf0 ω (by rw [he,ite_eq_right hω])
  · intro ω hω; exact hg0 ω (by rw [he,ite_eq_right hω])
  · exact hbound

lemma source_window_weight_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r : ℝ)
    (hy : r ≤ z.im) (ω : a.samples) (h : liveSpatialHitTime (γ ω) z r = ⊤) :
    spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r = 0 := by
  rw [spatialGreenWeight_eq_live (a.trace_continuous ω) κ _ _ z r
    (source_window_origin_bound a z r hy ω),ite_eq_left h]

lemma source_windowH_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r ε R : ℝ)
    (hy : r ≤ z.im) :
    Integrable (fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε R) (P.comap Subtype.val) := by
  let : IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) := a.probability
  have hτ := source_window_stopping a z r ε R hy
  have hm := (source_windowHB_stopped_measurable a z r ε R hτ).1.mono hτ.measurableSpace_le le_rfl
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Eventually.of_forall fun ω => by
    rcases (source_windowHB_range (γ ω) z r ε R).1 with h|h <;> simp only [h,norm_zero,norm_one,zero_le_one,le_refl]

lemma source_windowV_integrable_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (hk : 0 < κ) (hk8 : κ < 8)
    (z : ℂ) (r ε R : ℝ) (he : 0 < ε) (her : ε ≤ r) (hy : r ≤ z.im) :
    let W := fun ω : a.samples => spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z ε
    let V := fun ω : a.samples => W ω*sourceSpatialWindowH (γ ω) z r ε R
    Integrable V (P.comap Subtype.val) ∧ V ≤ᵐ[P.comap Subtype.val] W := by
  dsimp only
  let W := fun ω : a.samples => spatialGreenWeight κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z ε
  let H := fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε R
  have hτ := source_window_stopping a z r ε R hy
  have hHm : Measurable H :=
    (source_windowHB_stopped_measurable a z r ε R hτ).1.mono hτ.measurableSpace_le le_rfl
  have hVm : Measurable (fun ω => W ω * H ω) :=
    (source_windowV_stopped_measurable a z r ε R her hy hτ).mono hτ.measurableSpace_le le_rfl
  have hWi := (a.spatialGreen_expectation hk hk8 z ε he (her.trans hy)).1
  have hW0 (ω : a.samples) : 0 ≤ W ω :=
    ((a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _) hk hk8 he z (her.trans hy)).1
  constructor
  · apply Integrable.mono' hWi hVm.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖W ω * H ω‖ ≤ W ω
    dsimp only [H]
    rcases (source_windowHB_range (γ ω) z r ε R).1 with h|h
    · simp only [h,mul_zero,norm_zero]; exact hW0 ω
    · simp only [h,mul_one,Real.norm_eq_abs,abs_of_nonneg (hW0 ω),le_refl]
  · filter_upwards [] with ω
    rcases (source_windowHB_range (γ ω) z r ε R).1 with h|h
    · simpa only [h,mul_zero] using hW0 ω
    · simp only [h,mul_one,le_refl]

end
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_windowH_mean_of_raw
    {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hk : 0 < κ) (hk8 : κ < 8) (z : ℂ) (ε r R C : ℝ)
    (he : 0 < ε) (her : ε ≤ r) (hy : r ≤ z.im)
    (hraw : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r))
    (hs : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r))
    (hbound : (P.comap Subtype.val)[(fun ω : a.samples =>
      if liveSpatialHitTime (γ ω) z ε = ⊤ then (0:ℝ) else 1) | hraw.measurableSpace]
      ≤ᵐ[P.comap Subtype.val] (fun ω : a.samples => C*ε^codimension κ*
        spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r)) :
    (P.comap Subtype.val)[(fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε R) | hs.measurableSpace]
      ≤ᵐ[P.comap Subtype.val] (fun ω : a.samples => C*ε^codimension κ*
        spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r) := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  have hi := source_windowH_integrable a z r ε R hy
  have hWi := (a.spatialGreen_expectation hk hk8 z r (he.trans_le her) hy).1
  have hWm := source_spatialWeight_stopping_measurable a.measurable_B a.continuous_B κ
    (fun ω : a.samples => γ ω) a.G a.F a.witness z r hraw
  have hfi : Integrable (fun ω : a.samples => if liveSpatialHitTime (γ ω) z ε = ⊤ then (0:ℝ) else 1) μ := by
    apply Integrable.of_bound (source_liveIndicator_measurable a z ε (her.trans hy)).aestronglyMeasurable 1
    exact Eventually.of_forall fun ω => by split_ifs <;> norm_num
  have hcomp := condExp_mono (m := hraw.measurableSpace) hi hfi
    (Eventually.of_forall fun ω => source_windowH_le_indicator (a.trace_continuous ω) z r ε R her
      (source_window_origin_bound a z r hy ω))
  apply source_window_change_live_mean a z r hy hraw hs _ _ hi (hWi.const_mul _)
      (measurable_const.mul hWm).stronglyMeasurable
  · intro ω hω; exact (source_windowHB_zero (a.trace_continuous ω) z r ε R hω).1
  · intro ω hω; rw [source_window_weight_zero a z r hy ω hω,mul_zero]
  · exact hcomp.trans hbound

lemma source_windowV_mean
    {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hk : 0 < κ) (hk8 : κ < 8) (z : ℂ) (ε r R : ℝ)
    (he : 0 < ε) (her : ε ≤ r) (hy : r ≤ z.im)
    (hs : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r)) :
    let W := fun v (ω : a.samples) => spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
    (P.comap Subtype.val)[(fun ω : a.samples => r^codimension κ*W ε ω*
      sourceSpatialWindowH (γ ω) z r ε R) | hs.measurableSpace]
      ≤ᵐ[P.comap Subtype.val] (fun ω : a.samples => r^codimension κ*W r ω) := by
  dsimp only
  let μ : Measure a.samples := P.comap Subtype.val
  let W := fun v (ω : a.samples) => spatialGreenWeight κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
  let V := fun ω : a.samples => W ε ω*sourceSpatialWindowH (γ ω) z r ε R
  have hi := source_windowV_integrable_le a hk hk8 z r ε R he her hy
  have hWi := (a.spatialGreen_expectation hk hk8 z r (he.trans_le her) hy).1
  obtain ⟨hraw,_,hvbound⟩ := sourceSpatialConditionalMean_proved Ω m P inferInstance κ hk hk8 γ a z ε r he her hy
  have hWm := source_spatialWeight_stopping_measurable a.measurable_B a.continuous_B κ
    (fun ω : a.samples => γ ω) a.G a.F a.witness z r hraw
  have hv : μ[V | hs.measurableSpace] ≤ᵐ[μ] W r := by
    apply source_window_change_live_mean a z r hy hraw hs V (W r) hi.1 hWi hWm.stronglyMeasurable
    · intro ω hω; dsimp only [V]; rw [(source_windowHB_zero (a.trace_continuous ω) z r ε R hω).1,mul_zero]
    · exact source_window_weight_zero a z r hy
    · exact hvbound V hi.1 hi.2
  change μ[(fun ω => r^codimension κ*W ε ω*sourceSpatialWindowH (γ ω) z r ε R) |
    hs.measurableSpace] ≤ᵐ[μ] (fun ω => r^codimension κ*W r ω)
  have heqv : (fun ω => r^codimension κ*W ε ω*sourceSpatialWindowH (γ ω) z r ε R) =
      (fun ω => r^codimension κ*V ω) := by funext ω; dsimp only [V]; ring
  rw [heqv]
  filter_upwards [condExp_smul (μ := μ) (r^codimension κ) V hs.measurableSpace, hv] with ω hc hv
  change μ[(fun ω => r^codimension κ*V ω) | hs.measurableSpace] ω =
    r^codimension κ*μ[V | hs.measurableSpace] ω at hc
  rw [hc]
  exact mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg (he.trans_le her).le _)

lemma source_window_HV_mean :
    ∀ κ : ℝ, 0 < κ → κ < 8 → ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
      (z : ℂ) (ε r R : ℝ), 0 < ε → ε ≤ q*r → r ≤ z.im →
    ∃ hσ : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r),
      let μ := P.comap (Subtype.val : a.samples → Ω)
      let W := fun v (ω : a.samples) => spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
      let H := fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε R
      μ[H | hσ.measurableSpace] ≤ᵐ[μ] (fun ω => C*ε^codimension κ*W r ω) ∧
      μ[(fun ω => r^codimension κ*W ε ω*H ω) | hσ.measurableSpace] ≤ᵐ[μ]
        (fun ω => r^codimension κ*W r ω) := by
  intro κ hk hk8
  obtain ⟨C,hC,q,hq,hq1,happ⟩ := sourceConditionalApproach_proved κ hk hk8
  refine ⟨C,q,hC,hq,hq1,?_⟩
  intro Ω m P hP γ a z ε r R he heq hy
  let : IsProbabilityMeasure P := hP
  have hr : 0 < r := by
    by_contra! hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hq.le hn
    linarith
  have her : ε < r := heq.trans_lt (by nlinarith)
  have hs := source_liveHit_stopping a z r hy
  obtain ⟨hraw,hbound⟩ := happ Ω m P hP γ a z ε r he heq hy
  exact ⟨hs,source_windowH_mean_of_raw a hk hk8 z ε r R C he her.le hy hraw hs hbound,
    source_windowV_mean a hk hk8 z ε r R he her.le hy hs⟩

end
end SLEExactGauge

end
end

end OAI
