import Mathlib
import OAI.Probability.SLE.SwallowLyapunov

namespace OAI

/-! Stopped Power for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def powerLogGenerator (κ p α : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  powerLogDensity κ p α q x *
    ((-4 * α + κ * α * (α + 1) / 2) * (q.1.re - Real.sqrt κ * x) ^ 2 +
      (4 * p - κ * α / 2) * Real.exp (2 * q.1.im)) /
    (greenLogNormSq κ q x) ^ 2

lemma continuous_powerLogGenerator (κ p α : ℝ) :
    Continuous (fun q : (ℂ × ℝ) × ℝ => powerLogGenerator κ p α q.1 q.2) := by
  have hD := (powerLogDensity_contDiff κ p α).continuous
  have hN : Continuous (fun q : (ℂ × ℝ) × ℝ => greenLogNormSq κ q.1 q.2) := by
    unfold greenLogNormSq
    fun_prop
  unfold powerLogGenerator
  apply Continuous.div (hD.mul (by fun_prop)) (hN.pow 2)
  intro q
  exact pow_ne_zero 2 (greenLogNormSq_pos κ q.1 q.2).ne'

lemma measurable_powerLogGenerator_comp {X : Type*} [MeasurableSpace X]
    (κ p α : ℝ) (q : X → ℂ × ℝ) (b : X → ℝ)
    (hq : Measurable q) (hb : Measurable b) :
    Measurable (fun x => powerLogGenerator κ p α (q x) (b x)) := by
  have hh := (continuous_powerLogGenerator κ p α).measurable.comp (hq.prodMk hb)
  dsimp only [Function.comp_def] at hh
  with_reducible exact hh

lemma compact_power_drift
    (κ p α : ℝ) (hκ : 0 ≤ κ) (lo hi : ℝ) (hle : lo ≤ hi)
    (φ : (ℂ × ℝ) × ℝ → ℝ) (q : ℂ × ℝ) (x : ℝ)
    (hφD : fderiv ℝ φ (q, x) =
      fderiv ℝ (fun r : (ℂ × ℝ) × ℝ => powerLogDensity κ p α r.1 r.2) (q, x))
    (hφ2 : iteratedDeriv 2 (fun y => φ (q, y)) x =
      iteratedDeriv 2 (powerLogDensity κ p α q) x)
    (hq : q.1.im ∈ Icc lo hi) :
    fderiv ℝ φ (q, x)
        (clippedLogLoewnerField lo hi hle (Real.sqrt κ * x) q, 0) +
      (1 / 2 : ℝ) * iteratedDeriv 2 (fun y => φ (q, y)) x =
        powerLogGenerator κ p α q x := by
  rw [hφD, hφ2, powerLogDensity_pair_directional,
    clippedLogLoewnerField_eq_physical lo hi hle _ _ hq]
  exact power_physical_generator κ p α hκ q x

 

theorem ClippedLogSolution.stopped_power_dynkin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 ≤ κ) (p α : ℝ)
    (R : ℝ) (hR : 0 ≤ R) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hinside : ∀ ω t, t ≤ τ ω →
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi) :
    Integrable (fun ω => powerLogDensity κ p α (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, powerLogDensity κ p α (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) =
        powerLogDensity κ p α q₀ 0 +
        ∫ ω, (∫ t in (0 : ℝ)..(τ ω : ℝ),
          powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_power_field κ p α R hR
  obtain ⟨L₀, K₀, hL₀, _⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) :=
    clippedLogLoewnerField lo hi hle (Real.sqrt κ * B t.toNNReal ω) (c.Q t ω)
  have hBr : Measurable (fun p : ℝ × Ω => Real.sqrt κ * B p.1.toNNReal p.2) :=
    (hBm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      measurable_snd)).const_mul _
  have hpair : Measurable (fun p : ℝ × Ω =>
      (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)) := hBr.prodMk c.measurable
  have hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun p : ℝ × Ω => (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)))
    exact (continuous_clippedLogLoewnerField lo hi hle).measurable.comp hpair
  have hVb (t : ℝ) (ω : Ω) : ‖V t ω‖ ≤ (max c.L L₀ : ℝ≥0) :=
    (hL₀ _ _).trans (by exact_mod_cast le_max_right c.L L₀)
  obtain ⟨K, hfield⟩ := compact_state_smooth_brownian_field B hm c.Q V (max c.L L₀)
    c.measurable c.adapted (fun ω => (c.lipschitz ω).weaken (le_max_left _ _)) hVm hVb
    (fun t ω ht => c.derivative ω t ht) φ hφ hφc
  let F (t : ℝ≥0) (ω : Ω) (x : ℝ) := φ (c.Q t ω, x)
  let a (t : ℝ≥0) (ω : Ω) (x : ℝ) := fderiv ℝ φ (c.Q t ω, x) (V t ω, 0)
  have hgen (ω : Ω) (t : ℝ) (ht : t ∈ Icc 0 (τ ω : ℝ)) :
      brownianFieldDrift B F a t ω =
        powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω) := by
    have ht' : t.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr ht.2
    obtain ⟨hball, hlo, hhi⟩ := hinside ω t.toNNReal ht'
    have he : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht.1
    change fderiv ℝ φ (c.Q (t.toNNReal : ℝ) ω, B t.toNNReal ω)
      (V (t.toNNReal : ℝ) ω, 0) + _ = _
    dsimp only [V]
    rw [Real.toNNReal_coe]
    have hh := compact_power_drift κ p α hκ lo hi hle φ _ _
      (hφD _ _ hball) (hφ2 _ _ hball) ⟨hlo, hhi⟩
    simpa only [F, he] using hh
  have hopt := brownian_time_field_stopped_dynkin hB hm hBm hBc K F a hfield τ hτ T hb
  have hτm := stopping_time_measurable_nnreal hτ
  have hBmτ : Measurable (fun ω => B (τ ω) ω) := hBm.comp (hτm.prodMk measurable_id)
  have hQmτ : Measurable (fun ω => c.Q (τ ω) ω) :=
    c.measurable.comp ((NNReal.continuous_coe.measurable.comp hτm).prodMk measurable_id)
  have hfm : Measurable (fun ω => F (τ ω) ω (B (τ ω) ω)) :=
    hφ.continuous.measurable.comp (hQmτ.prodMk hBmτ)
  have hfi : Integrable (fun ω => F (τ ω) ω (B (τ ω) ω)) P := by
    apply Integrable.of_bound hfm.aestronglyMeasurable (K : ℝ)
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, iteratedDeriv_zero] using
        hfield.bound (τ ω) ω (B (τ ω) ω) 0 (by decide)
  have hfeq (ω : Ω) : F (τ ω) ω (B (τ ω) ω) =
      powerLogDensity κ p α (c.Q (τ ω) ω) (B (τ ω) ω) :=
    hφeq _ _ (hinside ω (τ ω) le_rfl).1
  refine ⟨hfi.congr (Eventually.of_forall hfeq), ?_⟩
  calc
    _ = ∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => (hfeq ω).symm)
    _ = (∫ ω, F 0 ω (B 0 ω) ∂P) +
        ∫ ω, (∫ t in (0 : ℝ)..(τ ω : ℝ), brownianFieldDrift B F a t ω) ∂P := hopt
    _ = _ := by
      congr 1
      · calc
          _ = ∫ _, powerLogDensity κ p α q₀ 0 ∂P := by
            apply integral_congr_ae
            filter_upwards [hB.eval_zero_ae_eq_zero] with ω hB0
            change φ (c.Q 0 ω, B 0 ω) = _
            have hh : ‖(c.Q 0 ω, B 0 ω)‖ ≤ R := by
              simpa only [NNReal.coe_zero] using (hinside ω 0 zero_le).1
            rw [hφeq _ _ hh, c.initial ω, hB0]
          _ = _ := by simp
      · apply integral_congr_ae
        exact Eventually.of_forall fun ω => intervalIntegral.integral_congr
          (fun t ht => hgen ω t (by simpa only [uIcc_of_le (τ ω).coe_nonneg] using ht))

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma stopping_paste_after
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (f : Filtration ℝ≥0 mΩ)
    {σ τ : Ω → ℝ≥0}
    (hσ : IsStoppingTime f (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime f (fun ω => (τ ω : WithTop ℝ≥0)))
    (hle : ∀ ω, σ ω ≤ τ ω) {A : Set Ω}
    (hA : MeasurableSet[hσ.measurableSpace] A) :
    IsStoppingTime f (fun ω => ((if ω ∈ A then τ ω else σ ω : ℝ≥0) : WithTop ℝ≥0)) := by
  classical
  intro t
  have he : {ω | ((if ω ∈ A then τ ω else σ ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
      (A ∩ {ω | (σ ω : WithTop ℝ≥0) ≤ t} ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ t}) ∪
        (Aᶜ ∩ {ω | (σ ω : WithTop ℝ≥0) ≤ t}) := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_union, mem_inter_iff, mem_compl_iff]
    split_ifs with h
    · simp only [h, true_and, not_true_eq_false, false_and, or_false]
      exact ⟨fun ht => ⟨(hle ω).trans ht, ht⟩, fun ht => ht.2⟩
    · simp [h]
  rw [he]
  exact ((hA.2 t).inter (hτ t)).union ((hA.compl).2 t)

 

theorem ClippedLogSolution.stopped_green_bounded_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (η₀ u : ℝ) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T)
    (hin : ∀ ω t, t ≤ σ ω → logRadiusClock η₀ (c.Q t ω) ≤ u ∧
      lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi) :
    Integrable (fun ω => greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω) ∂P) =
        greenLogDensity κ q₀ 0 := by
  classical
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hBa : Adapted f B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  have hex (n : ℕ) : ∃ β : Ω → ℝ≥0,
      IsStoppingTime f (fun ω => (β ω : WithTop ℝ≥0)) ∧
      (∀ ω, β ω ≤ T) ∧
      (∀ ω t, t ≤ β ω → |B t ω| ≤ (n : ℝ) + 1) ∧
      (∀ ω, β ω < T → |B (β ω) ω| = (n : ℝ) + 1) := by
    let D (t : ℝ≥0) (ω : Ω) := (n : ℝ) + 1 - |B t ω|
    obtain ⟨β, hβ, hbβ, hβin, _, hβbd⟩ := first_margin_stopping f D
      (fun t => by
        let : MeasurableSpace Ω := f t
        exact (hBa t).abs.const_sub ((n : ℝ) + 1))
      (fun ω => continuous_const.sub (hBc ω).abs)
      (fun ω => by simpa [D, hB0 ω] using (show 0 ≤ (n : ℝ) + 1 by positivity)) T
    refine ⟨β, hβ, hbβ, ?_, ?_⟩
    · intro ω t ht
      exact sub_nonneg.mp (hβin ω t ht)
    · intro ω ht
      exact (sub_eq_zero.mp (hβbd ω ht)).symm
  choose β hβ hbβ hβin hβbd using hex
  let σn (n : ℕ) (ω : Ω) := min (σ ω) (β n ω)
  have hsn (n : ℕ) : IsStoppingTime f (fun ω => (σn n ω : WithTop ℝ≥0)) := by
    simpa only [σn, WithTop.coe_min] using hσ.min (hβ n)
  have hsnb (n : ℕ) (ω : Ω) : σn n ω ≤ T := (min_le_left _ _).trans (hb ω)
  have hsin (n : ℕ) (ω : Ω) (t : ℝ≥0) (ht : t ≤ σn n ω) :
      logRadiusClock η₀ (c.Q t ω) ≤ u ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi :=
    hin ω t (ht.trans (min_le_left _ _))
  have hmean (n : ℕ) :
      Integrable (fun ω => greenLogDensity κ (c.Q (σn n ω) ω) (B (σn n ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (c.Q (σn n ω) ω) (B (σn n ω) ω) ∂P) = greenLogDensity κ q₀ 0 := by
    let R := max (‖q₀‖ + c.L * T) ((n : ℝ) + 1)
    have hR : 0 ≤ R := (by positivity : 0 ≤ (n : ℝ) + 1).trans (le_max_right _ _)
    apply c.stopped_green hB hBm hBc hκ hκ8 R hR (σn n) (hsn n) T (hsnb n)
    intro ω t ht
    refine ⟨?_, (hsin n ω t ht).2⟩
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    exact ⟨(c.norm_le ω t T (ht.trans (hsnb n ω))).trans (le_max_left _ _),
      (hβin n ω t (ht.trans (min_le_right _ _))).trans (le_max_right _ _)⟩
  have hstable (ω : Ω) : ∀ᶠ n : ℕ in atTop, σn n ω = σ ω := by
    obtain ⟨N, hN⟩ := continuous_path_bounded_by_nat (fun t => B t ω) (hBc ω) T
    filter_upwards [eventually_ge_atTop N] with n hn
    have hbn : β n ω = T := by
      apply le_antisymm (hbβ n ω)
      by_contra h
      have hlt : β n ω < T := lt_of_not_ge h
      have hh := hN (β n ω) (hbβ n ω)
      rw [hβbd n ω hlt] at hh
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    dsimp only [σn]
    rw [hbn, min_eq_left (hb ω)]
  let K := Real.exp (codimension κ * (u - Real.log 2 - η₀))
  have hbound (n : ℕ) (ω : Ω) :
      ‖greenLogDensity κ (c.Q (σn n ω) ω) (B (σn n ω) ω)‖ ≤ K := by
    rw [Real.norm_eq_abs, abs_of_nonneg (greenLogDensity_nonneg _ _ _)]
    exact greenLogDensity_le_radius κ η₀ u hκ hκ8 _ _ (hsin n ω _ le_rfl).1
  have hlim (ω : Ω) : Tendsto
      (fun n => greenLogDensity κ (c.Q (σn n ω) ω) (B (σn n ω) ω)) atTop
      (𝓝 (greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω))) :=
    tendsto_const_nhds.congr' ((hstable ω).mono fun n hn => by dsimp only; rw [hn])
  have hσm := stopping_time_measurable_nnreal hσ
  have hQm := c.measurable.comp ((measurable_coe_nnreal_real.comp hσm).prodMk measurable_id)
  have hbm := hBm.comp (hσm.prodMk measurable_id)
  have hmeas : Measurable (fun ω => greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω)) :=
    (greenLogDensity_contDiff κ).continuous.measurable.comp (hQm.prodMk hbm)
  have hi : Integrable (fun ω => greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω)) P := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable K
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (greenLogDensity_nonneg _ _ _)]
    exact greenLogDensity_le_radius κ η₀ u hκ hκ8 _ _ (hin ω _ le_rfl).1
  refine ⟨hi, ?_⟩
  apply tendsto_nhds_unique (tendsto_integral_of_dominated_convergence (fun _ => K)
    (fun n => (hmean n).1.aestronglyMeasurable) (integrable_const K)
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim))
  simpa only [(hmean _).2] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => greenLogDensity κ q₀ 0) atTop (𝓝 _))

 

theorem ClippedLogSolution.stopped_green_history
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (η₀ u : ℝ) (σ τ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω ≤ τ ω)
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hin : ∀ ω t, t ≤ τ ω → logRadiusClock η₀ (c.Q t ω) ≤ u ∧
      lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi)
    (A : Set Ω) (hA : MeasurableSet[hσ.measurableSpace] A) :
    (∫ ω in A, greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) =
      ∫ ω in A, greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω) ∂P := by
  let ρ (ω : Ω) : ℝ≥0 := if ω ∈ A then τ ω else σ ω
  have hρ := stopping_paste_after _ hσ hτ hστ hA
  have hρτ (ω : Ω) : ρ ω ≤ τ ω := by dsimp [ρ]; split_ifs <;> simp_all
  obtain ⟨hiti, hitm⟩ := c.stopped_green_bounded_clock hB hBm hBc hB0 hκ hκ8
    η₀ u τ hτ T hb hin
  obtain ⟨hisi, hism⟩ := c.stopped_green_bounded_clock hB hBm hBc hB0 hκ hκ8
    η₀ u σ hσ T (fun ω => (hστ ω).trans (hb ω))
    (fun ω t ht => hin ω t (ht.trans (hστ ω)))
  obtain ⟨hipi, hipm⟩ := c.stopped_green_bounded_clock hB hBm hBc hB0 hκ hκ8
    η₀ u ρ hρ T (fun ω => (hρτ ω).trans (hb ω))
    (fun ω t ht => hin ω t (ht.trans (hρτ ω)))
  have hAm : MeasurableSet A := hσ.measurableSpace_le A hA
  have hex (ω : Ω) :
      greenLogDensity κ (c.Q (ρ ω) ω) (B (ρ ω) ω) -
        greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω) =
      A.indicator (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) -
        greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω)) ω := by
    by_cases hω : ω ∈ A <;> simp [ρ, hω]
  have he : (∫ ω, A.indicator (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) -
        greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω)) ω ∂P) = 0 := by
    simp_rw [← hex]
    rw [integral_sub hipi hisi, hipm, hism, sub_self]
  rw [integral_indicator hAm, integral_sub hiti.integrableOn hisi.integrableOn] at he
  exact sub_eq_zero.mp he

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma exists_brownian_compact_stops
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T) :
    ∃ σn : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (σn n ω : WithTop ℝ≥0))) ∧
      (∀ n ω, σn n ω ≤ σ ω) ∧
      (∀ n ω t, t ≤ σn n ω → |B t ω| ≤ (n : ℝ) + 1) ∧
      (∀ ω, ∀ᶠ n : ℕ in atTop, σn n ω = σ ω) := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hBa : Adapted f B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  have hex (n : ℕ) : ∃ β : Ω → ℝ≥0,
      IsStoppingTime f (fun ω => (β ω : WithTop ℝ≥0)) ∧
      (∀ ω, β ω ≤ T) ∧
      (∀ ω t, t ≤ β ω → |B t ω| ≤ (n : ℝ) + 1) ∧
      (∀ ω, β ω < T → |B (β ω) ω| = (n : ℝ) + 1) := by
    let D (t : ℝ≥0) (ω : Ω) := (n : ℝ) + 1 - |B t ω|
    obtain ⟨β, hβ, hbβ, hβin, _, hβbd⟩ := first_margin_stopping f D
      (fun t => by
        let : MeasurableSpace Ω := f t
        exact (hBa t).abs.const_sub ((n : ℝ) + 1))
      (fun ω => continuous_const.sub (hBc ω).abs)
      (fun ω => by simpa [D, hB0 ω] using (show 0 ≤ (n : ℝ) + 1 by positivity)) T
    refine ⟨β, hβ, hbβ, ?_, ?_⟩
    · intro ω t ht
      exact sub_nonneg.mp (hβin ω t ht)
    · intro ω ht
      exact (sub_eq_zero.mp (hβbd ω ht)).symm
  choose β hβ hbβ hβin hβbd using hex
  let σn (n : ℕ) (ω : Ω) := min (σ ω) (β n ω)
  refine ⟨σn, ?_, fun n ω => min_le_left _ _, ?_, ?_⟩
  · intro n
    simpa only [σn, WithTop.coe_min] using hσ.min (hβ n)
  · intro n ω t ht
    exact hβin n ω t (ht.trans (min_le_right _ _))
  · intro ω
    obtain ⟨N, hN⟩ := continuous_path_bounded_by_nat (fun t => B t ω) (hBc ω) T
    filter_upwards [eventually_ge_atTop N] with n hn
    have hbn : β n ω = T := by
      apply le_antisymm (hbβ n ω)
      by_contra h
      have hlt : β n ω < T := lt_of_not_ge h
      have hh := hN (β n ω) (hbβ n ω)
      rw [hβbd n ω hlt] at hh
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    dsimp only [σn]
    rw [hbn, min_eq_left (hb ω)]

lemma bounded_stopped_cumulative_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (G : ℝ → Ω → ℝ) (hGm : Measurable (Function.uncurry G))
    (σ τ : Ω → ℝ≥0) (hτm : Measurable τ) (hle : ∀ ω, τ ω ≤ σ ω)
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ ω t, 0 ≤ t → t ≤ (σ ω : ℝ) → |G t ω| ≤ C) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..(τ ω : ℝ), G t ω) P ∧
      ∀ ω, |∫ t in (0 : ℝ)..(τ ω : ℝ), G t ω| ≤ C * T := by
  have hm : Measurable (fun ω => ∫ t in (0 : ℝ)..(τ ω : ℝ), G t ω) :=
    (cumulative_integral_measurable G hGm).comp (hτm.prodMk measurable_id)
  have hbnd (ω : Ω) : |∫ t in (0 : ℝ)..(τ ω : ℝ), G t ω| ≤ C * T := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (τ ω : ℝ)) (C := C) (f := fun t => G t ω) (fun t ht => by
        have htt : t ∈ Ioc (0 : ℝ) (τ ω : ℝ) := by simpa only [uIoc_of_le (τ ω).coe_nonneg] using ht
        simpa only [Real.norm_eq_abs] using hG ω t htt.1.le (htt.2.trans (by exact_mod_cast hle ω)))
    simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg (τ ω).coe_nonneg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (hle ω).trans (hb ω)) hC)
  exact ⟨Integrable.of_bound hm.aestronglyMeasurable _
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbnd ω), hbnd⟩

lemma integral_tendsto_stopped_eval
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (F : ℝ≥0 → Ω → ℝ) (σn : ℕ → Ω → ℝ≥0) (σ : Ω → ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (fun ω => F (σn n ω) ω) P)
    (K : ℝ) (hb : ∀ n ω, |F (σn n ω) ω| ≤ K)
    (hstable : ∀ ω, ∀ᶠ n : ℕ in atTop, σn n ω = σ ω) :
    Tendsto (fun n => ∫ ω, F (σn n ω) ω ∂P) atTop (𝓝 (∫ ω, F (σ ω) ω ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => K) hm (integrable_const K)
    (fun n => Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb n ω)
  apply Eventually.of_forall
  intro ω
  exact tendsto_const_nhds.congr' ((hstable ω).mono fun n hn => by dsimp only; rw [hn])

lemma integral_identity_of_stable_stops
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (F H : ℝ≥0 → Ω → ℝ) (σn : ℕ → Ω → ℝ≥0) (σ : Ω → ℝ≥0)
    (hstable : ∀ ω, ∀ᶠ n : ℕ in atTop, σn n ω = σ ω)
    (A K C : ℝ)
    (hmean : ∀ n, Integrable (fun ω => F (σn n ω) ω) P ∧
      (∫ ω, F (σn n ω) ω ∂P) = A + ∫ ω, H (σn n ω) ω ∂P)
    (hFi : Integrable (fun ω => F (σ ω) ω) P)
    (hHim : AEStronglyMeasurable (fun ω => H (σ ω) ω) P)
    (hHnm : ∀ n, AEStronglyMeasurable (fun ω => H (σn n ω) ω) P)
    (hFb : ∀ n ω, |F (σn n ω) ω| ≤ K)
    (hHb : ∀ n ω, |H (σn n ω) ω| ≤ C)
    (hHbound : ∀ ω, |H (σ ω) ω| ≤ C) :
    Integrable (fun ω => F (σ ω) ω) P ∧
    Integrable (fun ω => H (σ ω) ω) P ∧
      (∫ ω, F (σ ω) ω ∂P) = A + ∫ ω, H (σ ω) ω ∂P := by
  refine ⟨hFi, Integrable.of_bound hHim C
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hHbound ω), ?_⟩
  have hlimF := integral_tendsto_stopped_eval F σn σ
    (fun n => (hmean n).1.aestronglyMeasurable) K hFb hstable
  have hlimH := integral_tendsto_stopped_eval H σn σ hHnm C hHb hstable
  have he := hlimH.const_add A
  simp_rw [← (hmean _).2] at he
  exact tendsto_nhds_unique hlimF he

lemma ClippedLogSolution.stopped_power_dynkin_compact_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 ≤ κ) (p α : ℝ) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T)
    (hin : ∀ ω t, t ≤ σ ω → (c.Q t ω).1.im ∈ Icc lo hi)
    (N : ℝ) (hN : 0 ≤ N) (hcap : ∀ ω t, t ≤ σ ω → |B t ω| ≤ N) :
    Integrable (fun ω => powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω)) P ∧
      (∫ ω, powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω) ∂P) =
        powerLogDensity κ p α q₀ 0 + ∫ ω, (∫ t in (0 : ℝ)..(σ ω : ℝ),
          powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) ∂P := by
  let R := max (‖q₀‖ + c.L * T) N
  have hR : 0 ≤ R := hN.trans (le_max_right _ _)
  apply c.stopped_power_dynkin hB hBm hBc hκ p α R hR σ hσ T hb
  intro ω t ht
  refine ⟨?_, hin ω t ht⟩
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
  exact ⟨(c.norm_le ω t T (ht.trans (hb ω))).trans (le_max_left _ _),
    (hcap ω t ht).trans (le_max_right _ _)⟩

lemma ClippedLogSolution.stopped_power_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (p α : ℝ) (σ : Ω → ℝ≥0) (hσm : Measurable σ) (K : ℝ)
    (hval : ∀ ω, |powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω)| ≤ K) :
    Integrable (fun ω => powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω)) P := by
  have hQm := c.measurable.comp ((measurable_coe_nnreal_real.comp hσm).prodMk measurable_id)
  have hbm := hBm.comp (hσm.prodMk measurable_id)
  have hWm := (powerLogDensity_contDiff κ p α).continuous.measurable.comp (hQm.prodMk hbm)
  exact Integrable.of_bound hWm.aestronglyMeasurable K
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hval ω)

lemma ClippedLogSolution.power_generator_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (p α : ℝ) :
    Measurable (fun q : ℝ × Ω => powerLogGenerator κ p α (c.Q q.1 q.2) (B q.1.toNNReal q.2)) := by
  have ht : Measurable (fun q : ℝ × Ω => q.1.toNNReal) :=
    continuous_real_toNNReal.measurable.comp measurable_fst
  have hb : Measurable (fun q : ℝ × Ω => B q.1.toNNReal q.2) :=
    hBm.comp (ht.prodMk measurable_snd)
  exact measurable_powerLogGenerator_comp κ p α
    (fun q : ℝ × Ω => c.Q q.1 q.2) (fun q : ℝ × Ω => B q.1.toNNReal q.2)
    c.measurable hb

lemma ClippedLogSolution.stopped_power_cumulative_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (p α : ℝ) (σ τ : Ω → ℝ≥0) (hτm : Measurable τ) (hleτ : ∀ ω, τ ω ≤ σ ω)
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hdrift : ∀ ω t, t ≤ σ ω → |powerLogGenerator κ p α (c.Q t ω) (B t ω)| ≤ C) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..(τ ω : ℝ),
      powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) P ∧
      (∀ ω, |∫ t in (0 : ℝ)..(τ ω : ℝ),
        powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)| ≤ C * T) := by
  let G (t : ℝ) (ω : Ω) := powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)
  have hGm : Measurable (Function.uncurry G) := c.power_generator_measurable hBm p α
  have hGb (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (htσ : t ≤ (σ ω : ℝ)) : |G t ω| ≤ C := by
    have hh := hdrift ω t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr htσ)
    simpa only [G, Real.coe_toNNReal t ht] using hh
  exact bounded_stopped_cumulative_integrable G hGm σ τ hτm hleτ T hb C hC hGb

 

theorem ClippedLogSolution.stopped_power_dynkin_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 ≤ κ) (p α : ℝ) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T)
    (hin : ∀ ω t, t ≤ σ ω → (c.Q t ω).1.im ∈ Icc lo hi)
    (K C : ℝ) (hC : 0 ≤ C)
    (hval : ∀ ω t, t ≤ σ ω → |powerLogDensity κ p α (c.Q t ω) (B t ω)| ≤ K)
    (hdrift : ∀ ω t, t ≤ σ ω → |powerLogGenerator κ p α (c.Q t ω) (B t ω)| ≤ C) :
    Integrable (fun ω => powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω)) P ∧
    Integrable (fun ω => ∫ t in (0 : ℝ)..(σ ω : ℝ),
      powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) P ∧
      (∫ ω, powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω) ∂P) =
        powerLogDensity κ p α q₀ 0 +
        ∫ ω, (∫ t in (0 : ℝ)..(σ ω : ℝ),
          powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨σn, hsn, hsle, hsB, hstable⟩ := exists_brownian_compact_stops B hm hBc hB0 σ hσ T hb
  have hsnb (n : ℕ) (ω : Ω) : σn n ω ≤ T := (hsle n ω).trans (hb ω)
  let W (τ : Ω → ℝ≥0) (ω : Ω) := powerLogDensity κ p α (c.Q (τ ω) ω) (B (τ ω) ω)
  let G (t : ℝ) (ω : Ω) := powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)
  let H (τ : Ω → ℝ≥0) (ω : Ω) := ∫ t in (0 : ℝ)..(τ ω : ℝ), G t ω
  have hmean (n : ℕ) : Integrable (W (σn n)) P ∧
      (∫ ω, W (σn n) ω ∂P) = powerLogDensity κ p α q₀ 0 + ∫ ω, H (σn n) ω ∂P := by
    exact c.stopped_power_dynkin_compact_cap hB hBm hBc hκ p α (σn n) (hsn n)
      T (hsnb n) (fun ω t ht => hin ω t (ht.trans (hsle n ω))) ((n : ℝ) + 1)
      (by positivity) (hsB n)
  have hH (τ : Ω → ℝ≥0) (hτm : Measurable τ) (hτ : ∀ ω, τ ω ≤ σ ω) :
      Integrable (H τ) P ∧ ∀ ω, |H τ ω| ≤ C * T :=
    c.stopped_power_cumulative_integrable hBm p α σ τ hτm hτ T hb C hC hdrift
  have hσm := stopping_time_measurable_nnreal hσ
  have hWi : Integrable (W σ) P := c.stopped_power_integrable hBm p α σ hσm K
    (fun ω => hval ω (σ ω) le_rfl)
  exact integral_identity_of_stable_stops
    (fun t ω => powerLogDensity κ p α (c.Q t ω) (B t ω))
    (fun t ω => ∫ u in (0 : ℝ)..(t : ℝ), G u ω) σn σ hstable
    (powerLogDensity κ p α q₀ 0) K (C * T) hmean hWi
    (hH σ hσm (fun _ => le_rfl)).1.aestronglyMeasurable
    (fun n => (hH (σn n) (stopping_time_measurable_nnreal (hsn n)) (hsle n)).1.aestronglyMeasurable)
    (fun n ω => hval ω (σn n ω) (hsle n ω))
    (fun n => (hH (σn n) (stopping_time_measurable_nnreal (hsn n)) (hsle n)).2)
    (hH σ hσm (fun _ => le_rfl)).2

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}

lemma ClippedLogSolution.swallow_generator_measurable
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (β C : ℝ) :
    Measurable (fun p : ℝ × Ω => swallowGenerator κ β C (c.Q p.1 p.2) (B p.1.toNNReal p.2)) := by
  have hBr : Measurable (fun p : ℝ × Ω => B p.1.toNNReal p.2) :=
    hBm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hp : Measurable (fun p : ℝ × Ω => (c.Q p.1 p.2, B p.1.toNNReal p.2)) :=
    c.measurable.prodMk hBr
  have hh := (continuous_swallowGenerator κ β C).measurable.comp hp
  dsimp only [Function.comp_def] at hh
  with_reducible exact hh

lemma ClippedLogSolution.swallow_generator_continuous
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (β C : ℝ) (ω : Ω) :
    Continuous (fun t : ℝ => swallowGenerator κ β C (c.Q t ω) (B t.toNNReal ω)) := by
  have hB : Continuous (fun t : ℝ => B t.toNNReal ω) :=
    (hBc ω).comp continuous_real_toNNReal
  have hQ : Continuous (fun t : ℝ => c.Q t ω) := (c.lipschitz ω).continuous
  have hp : Continuous (fun t : ℝ => (c.Q t ω, B t.toNNReal ω)) := hQ.prodMk hB
  have hh := (continuous_swallowGenerator κ β C).comp hp
  dsimp only [Function.comp_def] at hh
  with_reducible exact hh

lemma ClippedLogSolution.swallow_cumulative_integrable
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (β C : ℝ)
    (τ : Ω → ℝ≥0) (hτm : Measurable τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ ω t, t ≤ τ ω → |swallowGenerator κ β C (c.Q t ω) (B t ω)| ≤ D) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..(τ ω : ℝ),
      swallowGenerator κ β C (c.Q t ω) (B t.toNNReal ω)) P := by
  let G (t : ℝ) (ω : Ω) := swallowGenerator κ β C (c.Q t ω) (B t.toNNReal ω)
  have hGm : Measurable (Function.uncurry G) := c.swallow_generator_measurable hBm β C
  have hGb (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (hτ : t ≤ (τ ω : ℝ)) : |G t ω| ≤ D := by
    have hh := hbound ω t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hτ)
    simpa only [G, Real.coe_toNNReal t ht] using hh
  exact (bounded_stopped_cumulative_integrable (P := P) G hGm τ τ hτm
    (fun _ => le_rfl) T hτT D hD hGb).1

lemma bounded_nnreal_integrable {P : Measure Ω} [IsFiniteMeasure P]
    (τ : Ω → ℝ≥0) (hτm : Measurable τ) (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => (τ ω : ℝ)) P := by
  apply Integrable.of_bound ((NNReal.continuous_coe.measurable.comp hτm).aestronglyMeasurable) T
  exact Eventually.of_forall fun ω => by
    change ‖(τ ω : ℝ)‖ ≤ (T : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (τ ω).coe_nonneg]
    exact NNReal.coe_le_coe.mpr (hb ω)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RadialLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    {c : ClippedLogSolution B hm κ lo hi hle q₀} {R : ℝ} {T : ℝ≥0}

lemma exists_compact_bound (a : RadialLocalization c R T) (hκ : 0 < κ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω t, t ≤ a.τ ω → ‖(c.Q t ω, B t ω)‖ ≤ K := by
  let M : ℝ := ‖q₀‖+c.L*T
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨max M ((M+R)/Real.sqrt κ), le_max_of_le_left hM, ?_⟩
  intro ω t ht
  have hQ : ‖c.Q t ω‖ ≤ M := c.norm_le ω t T (ht.trans (a.bounded ω))
  have hB := norm_driver_of_radial_bound κ R M hκ hR (c.Q t ω) (B t ω) hQ (a.inside ω t ht).1
  rw [Prod.norm_def]
  exact max_le_max hQ (by simpa only [Real.norm_eq_abs] using hB)

lemma exists_generator_bound (a : RadialLocalization c R T)
    (hκ : 0 < κ) (hR : 0 ≤ R) (β C : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ω t, t ≤ a.τ ω →
      |swallowGenerator κ β C (c.Q t ω) (B t ω)| ≤ D := by
  obtain ⟨K,hK,hbound⟩ := a.exists_compact_bound hκ hR
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0 : (ℂ × ℝ) × ℝ) K).exists_bound_of_continuousOn
    (continuous_swallowGenerator κ β C).continuousOn
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro ω t ht
  have hmem : (c.Q t ω, B t ω) ∈ Metric.closedBall (0 : (ℂ × ℝ) × ℝ) K := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound ω t ht
  exact (hD _ hmem).trans (le_max_left _ _)

lemma generator_cumulative_integrable {P : Measure Ω} [IsFiniteMeasure P]
    (a : RadialLocalization c R T)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hκ : 0 < κ) (hR : 0 ≤ R) (β C : ℝ) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..(a.τ ω : ℝ),
      swallowGenerator κ β C (c.Q t ω) (B t.toNNReal ω)) P := by
  obtain ⟨D,hD,hbound⟩ := a.exists_generator_bound hκ hR β C
  exact c.swallow_cumulative_integrable hBm β C a.τ
    (stopping_time_measurable_nnreal a.stopping) T a.bounded D hD hbound

lemma stopped_lyapunov_bound {P : Measure Ω}
    (a : RadialLocalization c R T)
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 4 < κ) (hR : 0 < R) (hhi : q₀.1.im ≤ hi) :
    Integrable (fun ω => swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8)
      (c.Q (a.τ ω) ω) (B (a.τ ω) ω)) P ∧
    (∫ ω, swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8)
      (c.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) +
      (((κ-4)/(2*κ))*((κ-4)/4)*Real.exp ((((κ-4)/(2*κ))-2)*Real.log R)) *
        (∫ ω, (a.τ ω : ℝ) ∂P) ≤ swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8) q₀ 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  let β := (κ-4)/(2*κ)
  let C := 3*(κ-4)/8
  let d := β*((κ-4)/4)*Real.exp ((β-2)*Real.log R)
  let G (t : ℝ) (ω : Ω) := swallowGenerator κ β C (c.Q t ω) (B t.toNNReal ω)
  obtain ⟨K,hK,hbound⟩ := a.exists_compact_bound hk hR.le
  have hmean := c.stopped_swallow_dynkin hB hBm hBc hk.le β C K hK a.τ a.stopping
    T a.bounded (fun ω t ht => ⟨hbound ω t ht, (a.inside ω t ht).2,
      (a.height_le_initial ω t ht).trans hhi⟩)
  refine ⟨hmean.1, ?_⟩
  have hτi : Integrable (fun ω => (a.τ ω : ℝ)) P :=
    bounded_nnreal_integrable a.τ (stopping_time_measurable_nnreal a.stopping) T a.bounded
  have hGi : Integrable (fun ω => ∫ t in (0 : ℝ)..(a.τ ω : ℝ), G t ω) P :=
    a.generator_cumulative_integrable hBm hk hR.le β C
  have hGle (ω : Ω) : (∫ t in (0 : ℝ)..(a.τ ω : ℝ), G t ω) ≤ -d*(a.τ ω : ℝ) := by
    have hGc : Continuous (fun t : ℝ => G t ω) := c.swallow_generator_continuous hBc β C ω
    have hh := intervalIntegral.integral_mono_on (a.τ ω).coe_nonneg
      (hGc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _ :
        IntervalIntegrable (fun _ : ℝ => -d) volume 0 (a.τ ω)) (fun t ht => by
          have hh := swallowGenerator_uniform_negative κ hκ (c.Q t.toNNReal ω)
            (B t.toNNReal ω) R hR
            (a.inside ω t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2)).1
          simpa only [G, Real.coe_toNNReal t ht.1] using hh)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hh
  have htotal := integral_mono hGi (hτi.const_mul (-d)) hGle
  rw [integral_const_mul] at htotal
  change (∫ ω, swallowLyapunov κ β C (c.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) +
    d*(∫ ω, (a.τ ω : ℝ) ∂P) ≤ swallowLyapunov κ β C q₀ 0
  rw [hmean.2]
  linarith

end RadialLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

 

theorem compensated_exponential_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X E : ℕ → Ω → ℝ) (Y Q : Ω → ℝ) (θ V : ℝ)
    (hm : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal
      (Real.exp (θ * X n ω - θ ^ 2 * E n ω / 2))) P)
    (hX : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hE : ∀ᵐ ω ∂P, Tendsto (fun n => E n ω) atTop (𝓝 (Q ω)))
    (hQ : ∀ᵐ ω ∂P, Q ω ≤ V)
    (hexp : ∀ n, (∫⁻ ω, ENNReal.ofReal
      (Real.exp (θ * X n ω - θ ^ 2 * E n ω / 2)) ∂P) ≤ 1) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Y ω - θ ^ 2 * V / 2)) ∂P) ≤ 1 := by
  let f (n : ℕ) (ω : Ω) := ENNReal.ofReal (Real.exp (θ * X n ω - θ ^ 2 * E n ω / 2))
  have hl : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (θ * Y ω - θ ^ 2 * Q ω / 2)) =
      liminf (fun n => f n ω) atTop := by
    filter_upwards [hX, hE] with ω hx he
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto _).comp ((hx.const_mul θ).sub ((he.const_mul (θ^2)).div_const 2)))).liminf_eq.symm
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Y ω - θ ^ 2 * Q ω / 2)) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hQ] with ω hq
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hq (sq_nonneg θ)]
    _ = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P := lintegral_congr_ae hl
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop := lintegral_liminf_le' hm
    _ ≤ 1 := liminf_le_of_frequently_le (Frequently.of_forall hexp)

 
theorem compensated_exponential_limit_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X E : ℕ → Ω → ℝ) (Y Q : Ω → ℝ) (θ : ℝ)
    (hm : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal
      (Real.exp (θ * X n ω - θ ^ 2 * E n ω / 2))) P)
    (hX : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hE : ∀ᵐ ω ∂P, Tendsto (fun n => E n ω) atTop (𝓝 (Q ω)))
    (hexp : ∀ n, (∫⁻ ω, ENNReal.ofReal
      (Real.exp (θ * X n ω - θ ^ 2 * E n ω / 2)) ∂P) ≤ 1) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Y ω - θ ^ 2 * Q ω / 2)) ∂P) ≤ 1 := by
  let f (n : ℕ) (ω : Ω) := ENNReal.ofReal (Real.exp (θ * X n ω - θ ^ 2 * E n ω / 2))
  have hl : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (θ * Y ω - θ ^ 2 * Q ω / 2)) =
      liminf (fun n => f n ω) atTop := by
    filter_upwards [hX, hE] with ω hx he
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto _).comp ((hx.const_mul θ).sub
        ((he.const_mul (θ^2)).div_const 2)))).liminf_eq.symm
  calc
    _ = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P := lintegral_congr_ae hl
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop := lintegral_liminf_le' hm
    _ ≤ 1 := liminf_le_of_frequently_le (Frequently.of_forall hexp)

 
theorem exponential_tail_of_compensated
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} (hY : AEMeasurable Y P) {θ : ℝ} (hθ : 0 ≤ θ) (V x : ℝ)
    (h : (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Y ω - θ ^ 2 * V / 2)) ∂P) ≤ 1) :
    P {ω | x ≤ Y ω} ≤ ENNReal.ofReal (Real.exp (-θ * x + θ ^ 2 * V / 2)) := by
  let a := ENNReal.ofReal (Real.exp (θ * x - θ ^ 2 * V / 2))
  have ha : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hab : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hm := (((hY.const_mul θ).sub_const (θ ^ 2 * V / 2)).exp).ennreal_ofReal
  have hle := meas_ge_le_lintegral_div hm ha hab
  have hs : {ω | x ≤ Y ω} ⊆ {ω | a ≤ ENNReal.ofReal
      (Real.exp (θ * Y ω - θ ^ 2 * V / 2))} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (sub_le_sub_right (mul_le_mul_of_nonneg_left hω hθ) _))
  calc
    _ ≤ P {ω | a ≤ ENNReal.ofReal (Real.exp (θ * Y ω - θ ^ 2 * V / 2))} := measure_mono hs
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Y ω - θ ^ 2 * V / 2)) ∂P) / a := hle
    _ ≤ 1 / a := ENNReal.div_le_div_right h a
    _ = _ := by
      rw [one_div, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
      congr 2
      ring

 
theorem subGaussian_tail_of_compensated
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} (hY : AEMeasurable Y P) {V x : ℝ} (hV : 0 < V) (hx : 0 ≤ x)
    (h : ∀ θ : ℝ, (∫⁻ ω, ENNReal.ofReal
      (Real.exp (θ * Y ω - θ ^ 2 * V / 2)) ∂P) ≤ 1) :
    P {ω | x ≤ Y ω} ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * V))) := by
  have ht := exponential_tail_of_compensated hY (div_nonneg hx hV.le) V x (h (x/V))
  convert ht using 2
  congr 2
  field_simp
  ring

end SLEExactGauge
end

 
end

end OAI
