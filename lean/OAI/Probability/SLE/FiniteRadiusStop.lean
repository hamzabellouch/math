import Mathlib
import OAI.Probability.SLE.BoundaryDensity

namespace OAI

/-! Finite Radius Stop for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma continuous_nonneg_at_boundary (D : ℝ≥0 → ℝ) (hD : Continuous D)
    (h0 : 0 ≤ D 0) (τ : ℝ≥0) (hb : ∀ t, t < τ → 0 < D t) :
    ∀ t, t ≤ τ → 0 ≤ D t := by
  intro t ht
  by_cases hτ : τ = 0
  · have : t = 0 := le_antisymm (ht.trans hτ.le) zero_le
    simpa only [this] using h0
  · have hτpos : 0 < τ := pos_iff_ne_zero.mpr hτ
    apply le_on_closure (s := Iio τ) (f := fun _ : ℝ≥0 => (0 : ℝ)) (g := D)
      (fun s hs => (hb s hs).le) continuous_const.continuousOn hD.continuousOn
    rw [closure_Iio' (show (Iio τ).Nonempty from ⟨0, hτpos⟩)]
    exact ht

 

theorem first_margin_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (f : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → Ω → ℝ) (hDa : Adapted f D)
    (hDc : ∀ ω, Continuous (fun t => D t ω)) (hD0 : ∀ ω, 0 ≤ D 0 ω)
    (T : ℝ≥0) :
    ∃ τ : Ω → ℝ≥0,
      IsStoppingTime f (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      (∀ ω, τ ω ≤ T) ∧
      (∀ ω t, t ≤ τ ω → 0 ≤ D t ω) ∧
      (∀ ω t, t < τ ω → 0 < D t ω) ∧
      (∀ ω, τ ω < T → D (τ ω) ω = 0) := by
  let H (t : ℝ≥0) (ω : Ω) := max 0 (D t ω)
  have hHa : Adapted f H := fun t => measurable_const.max (hDa t)
  have hHc (ω : Ω) : Continuous (fun t => H t ω) := continuous_const.max (hDc ω)
  have hHn (t : ℝ≥0) (ω : Ω) : 0 ≤ H t ω := le_max_left _ _
  let τ (ω : Ω) := hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω
  obtain ⟨hτ, hb, hpre, hat⟩ := continuous_nonnegative_first_zero_stopping f H hHa hHc hHn T
  have hDpre (ω : Ω) (t : ℝ≥0) (ht : t < τ ω) : 0 < D t ω := by
    have hh := hpre ω t ht
    simpa only [H, lt_max_iff, lt_self_iff_false, false_or] using hh
  have hDle (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ ω) : 0 ≤ D t ω :=
    continuous_nonneg_at_boundary (fun s => D s ω) (hDc ω) (hD0 ω) (τ ω) (hDpre ω) t ht
  refine ⟨τ, hτ, hb, hDle, hDpre, ?_⟩
  intro ω ht
  apply le_antisymm _ (hDle ω (τ ω) le_rfl)
  have hh := le_max_right 0 (D (τ ω) ω)
  exact hh.trans (hat ω ht).le

 
noncomputable def logStopMargin (κ η₀ u lo hi ε N : ℝ) (q : ℂ × ℝ) (b : ℝ) : ℝ :=
  min (u - logRadiusClock η₀ q)
    (min (logAngleSq κ q b - ε)
      (min (q.1.im - lo) (min (hi - q.1.im) (N - |b|))))

lemma continuous_logStopMargin (κ η₀ u lo hi ε N : ℝ) :
    Continuous (fun p : (ℂ × ℝ) × ℝ => logStopMargin κ η₀ u lo hi ε N p.1 p.2) := by
  unfold logStopMargin
  exact (continuous_const.sub ((continuous_logRadiusClock η₀).comp continuous_fst)).min
    (((continuous_logAngleSq κ).sub continuous_const).min
      (((Complex.continuous_im.comp continuous_fst.fst).sub continuous_const).min
        ((continuous_const.sub (Complex.continuous_im.comp continuous_fst.fst)).min
          (continuous_const.sub continuous_snd.abs))))

lemma logStopMargin_nonneg_iff (κ η₀ u lo hi ε N : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    0 ≤ logStopMargin κ η₀ u lo hi ε N q b ↔
      logRadiusClock η₀ q ≤ u ∧ ε ≤ logAngleSq κ q b ∧
        lo ≤ q.1.im ∧ q.1.im ≤ hi ∧ |b| ≤ N := by
  simp only [logStopMargin, le_min_iff, sub_nonneg]

lemma logStopMargin_pos_iff (κ η₀ u lo hi ε N : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    0 < logStopMargin κ η₀ u lo hi ε N q b ↔
      logRadiusClock η₀ q < u ∧ ε < logAngleSq κ q b ∧
        lo < q.1.im ∧ q.1.im < hi ∧ |b| < N := by
  simp only [logStopMargin, lt_min_iff, sub_pos]

lemma ClippedLogSolution.norm_le
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (ω : Ω) (t T : ℝ≥0) (ht : t ≤ T) :
    ‖c.Q t ω‖ ≤ ‖q₀‖ + c.L * T := by
  have hh := (c.lipschitz ω).norm_sub_le (t : ℝ) 0
  rw [c.initial ω, sub_zero, Real.norm_eq_abs, abs_of_nonneg t.coe_nonneg] at hh
  have hn := norm_add_le (c.Q t ω - q₀) q₀
  rw [sub_add_cancel] at hn
  have hmul : (c.L : ℝ) * t ≤ c.L * T :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast ht) c.L.coe_nonneg
  linarith

 

theorem ClippedLogSolution.finite_radius_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hq0 : q₀.2 = 0)
    (u ε N : ℝ) (hu : 0 ≤ u) (hε : 0 < ε) (hN : 0 ≤ N)
    (hε0 : ε ≤ logAngleSq κ q₀ 0)
    (hlo : lo < q₀.1.im - u / (2 * ε)) (hhi : q₀.1.im < hi)
    (T : ℝ≥0) (hT : u < (4 * ε ^ 2 / Real.exp (2 * q₀.1.im)) * T) :
    ∃ τ : Ω → ℝ≥0,
      IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      (∀ ω, τ ω < T) ∧
      (∀ ω t, t ≤ τ ω →
        logRadiusClock q₀.1.im (c.Q t ω) ≤ u ∧
        ε ≤ logAngleSq κ (c.Q t ω) (B t ω) ∧
        lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi ∧ |B t ω| ≤ N) ∧
      (∀ ω t, t < τ ω →
        logRadiusClock q₀.1.im (c.Q t ω) < u ∧
        ε < logAngleSq κ (c.Q t ω) (B t ω) ∧
        lo < (c.Q t ω).1.im ∧ (c.Q t ω).1.im < hi ∧ |B t ω| < N) ∧
      (∀ ω, logRadiusClock q₀.1.im (c.Q (τ ω) ω) = u ∨
        logAngleSq κ (c.Q (τ ω) ω) (B (τ ω) ω) = ε ∨ |B (τ ω) ω| = N) ∧
      Integrable (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) = greenLogDensity κ q₀ 0 := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let D (t : ℝ≥0) (ω : Ω) := logStopMargin κ q₀.1.im u lo hi ε N (c.Q t ω) (B t ω)
  have hBa : Adapted f B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  have hDa : Adapted f D := by
    intro t
    change Measurable[f t] ((fun p : (ℂ × ℝ) × ℝ => logStopMargin κ q₀.1.im u lo hi ε N p.1 p.2) ∘
      (fun ω => (c.Q t ω, B t ω)))
    exact (continuous_logStopMargin κ q₀.1.im u lo hi ε N).measurable.comp
      ((c.adapted t).prodMk (hBa t))
  have hDc (ω : Ω) : Continuous (fun t => D t ω) := by
    change Continuous ((fun p : (ℂ × ℝ) × ℝ => logStopMargin κ q₀.1.im u lo hi ε N p.1 p.2) ∘
      (fun t : ℝ≥0 => (c.Q t ω, B t ω)))
    exact (continuous_logStopMargin κ q₀.1.im u lo hi ε N).comp
      (((c.lipschitz ω).continuous.comp NNReal.continuous_coe).prodMk (hBc ω))
  have hD0 (ω : Ω) : 0 ≤ D 0 ω := by
    change 0 ≤ logStopMargin κ q₀.1.im u lo hi ε N (c.Q (0 : ℝ≥0) ω) (B 0 ω)
    rw [NNReal.coe_zero, c.initial ω, hB0 ω, logStopMargin_nonneg_iff]
    refine ⟨?_, hε0, ?_, hhi.le, ?_⟩
    · simpa only [logRadiusClock, sub_self, zero_add, hq0] using hu
    · have hd : 0 ≤ u / (2 * ε) := div_nonneg hu (by positivity)
      linarith
    · simpa only [abs_zero] using hN
  obtain ⟨τ, hτ, hb, hleD, hltD, hzero⟩ := first_margin_stopping f D hDa hDc hD0 T
  have hin (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ ω) :
      logRadiusClock q₀.1.im (c.Q t ω) ≤ u ∧
      ε ≤ logAngleSq κ (c.Q t ω) (B t ω) ∧
      lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi ∧ |B t ω| ≤ N :=
    (logStopMargin_nonneg_iff κ q₀.1.im u lo hi ε N _ _).mp (hleD ω t ht)
  have hg (ω : Ω) :
      (c.Q (τ ω) ω).1.im ≤ q₀.1.im ∧
      q₀.1.im - logRadiusClock q₀.1.im (c.Q (τ ω) ω) / (2 * ε) ≤ (c.Q (τ ω) ω).1.im ∧
      (4 * ε ^ 2 / Real.exp (2 * q₀.1.im)) * τ ω ≤ logRadiusClock q₀.1.im (c.Q (τ ω) ω) := by
    have hd (s : ℝ) (hs : s ∈ Icc 0 (τ ω : ℝ)) :
        HasDerivWithinAt (fun t => c.Q t ω)
          (physicalLogLoewnerField (Real.sqrt κ * B s.toNNReal ω) (c.Q s ω))
          (Icc 0 (τ ω : ℝ)) s := by
      have hst : s.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr hs.2
      have hbounds := (hin ω s.toNNReal hst).2.2
      rw [Real.coe_toNNReal _ hs.1] at hbounds
      have hh := (c.derivative ω s hs.1).mono (show Icc (0 : ℝ) (τ ω : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
      rwa [clippedLogLoewnerField_eq_physical lo hi hle _ _ ⟨hbounds.1, hbounds.2.1⟩] at hh
    have ha (s : ℝ) (hs : s ∈ Icc 0 (τ ω : ℝ)) :
        ε ≤ logAngleSq κ (c.Q s ω) (B s.toNNReal ω) := by
      have hh := (hin ω s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)).2.1
      simpa only [Real.coe_toNNReal _ hs.1] using hh
    have hq : (c.Q 0 ω).2 = 0 := by rw [c.initial ω, hq0]
    have hh := log_loewner_height_clock_bounds (τ ω).coe_nonneg hε hq hd ha
    simpa only [c.initial ω] using hh
  have hτlt (ω : Ω) : τ ω < T := by
    by_contra hn
    have he : τ ω = T := le_antisymm (hb ω) (not_lt.mp hn)
    have hh := (hg ω).2.2.trans (hin ω (τ ω) le_rfl).1
    rw [he] at hh
    exact (not_le_of_gt hT) hh
  have he (ω : Ω) :
      logRadiusClock q₀.1.im (c.Q (τ ω) ω) = u ∨
      logAngleSq κ (c.Q (τ ω) ω) (B (τ ω) ω) = ε ∨ |B (τ ω) ω| = N := by
    obtain ⟨hr, ha, hl, hh, hbn⟩ := hin ω (τ ω) le_rfl
    have hstrictlo : lo < (c.Q (τ ω) ω).1.im := by
      have hdiv := div_le_div_of_nonneg_right hr (show 0 ≤ 2 * ε by positivity)
      linarith [(hg ω).2.1]
    have hstricthi : (c.Q (τ ω) ω).1.im < hi := (hg ω).1.trans_lt hhi
    by_contra hn
    push Not at hn
    have hp : 0 < D (τ ω) ω :=
      (logStopMargin_pos_iff κ q₀.1.im u lo hi ε N _ _).mpr
        ⟨lt_of_le_of_ne hr hn.1, lt_of_le_of_ne ha (Ne.symm hn.2.1),
          hstrictlo, hstricthi, lt_of_le_of_ne hbn hn.2.2⟩
    rw [hzero ω (hτlt ω)] at hp
    exact lt_irrefl 0 hp
  let R := max (‖q₀‖ + c.L * T) N
  have hR : 0 ≤ R := hN.trans (le_max_right _ _)
  have hinside (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ ω) :
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi := by
    refine ⟨?_, (hin ω t ht).2.2.1, (hin ω t ht).2.2.2.1⟩
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    exact ⟨(c.norm_le ω t T (ht.trans (hb ω))).trans (le_max_left _ _),
      (hin ω t ht).2.2.2.2.trans (le_max_right _ _)⟩
  obtain ⟨hint, hmean⟩ := c.stopped_green hB hBm hBc hκ hκ8 R hR τ hτ T hb hinside
  refine ⟨τ, hτ, hτlt, hin, ?_, he, hint, hmean⟩
  intro ω t ht
  exact (logStopMargin_pos_iff κ q₀.1.im u lo hi ε N _ _).mp (hltD ω t ht)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma continuous_path_bounded_by_nat (B : ℝ≥0 → ℝ) (hB : Continuous B) (T : ℝ≥0) :
    ∃ n : ℕ, ∀ t : ℝ≥0, t ≤ T → |B t| < (n : ℝ) + 1 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).exists_bound_of_continuousOn hB.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, fun t ht => ?_⟩
  have hh : |B t| ≤ C := by simpa only [Real.norm_eq_abs] using hC t ⟨zero_le, ht⟩
  linarith

lemma first_radius_angle_le (S A : ℝ≥0 → ℝ) (u ε : ℝ) (s t : ℝ≥0)
    (hpre : ∀ v, v < s → S v < u ∧ ε < A v)
    (hat : S t = u ∨ A t = ε) : s ≤ t := by
  by_contra hn
  obtain ⟨hr, ha⟩ := hpre t (not_le.mp hn)
  rcases hat with h | h
  · exact (ne_of_lt hr) h
  · exact (ne_of_gt ha) h

lemma bounded_iSup_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (f : Filtration ℝ≥0 mΩ)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, IsStoppingTime f (fun ω => (τ n ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ n ω, τ n ω ≤ T) :
    IsStoppingTime f (fun ω => ((⨆ n, τ n ω : ℝ≥0) : WithTop ℝ≥0)) := by
  intro t
  have he : {ω | ((⨆ n, τ n ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
      ⋂ n : ℕ, {ω | (τ n ω : WithTop ℝ≥0) ≤ t} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_iInter]
    exact ciSup_le_iff ⟨T, by rintro v ⟨n, rfl⟩; exact hb n ω⟩
  rw [he]
  exact MeasurableSet.iInter (fun n => hτ n t)

lemma greenLogDensity_nonneg (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) : 0 ≤ greenLogDensity κ q b :=
  (Real.exp_pos _).le

lemma greenLogDensity_le_radius
    (κ η₀ u : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (q : ℂ × ℝ) (b : ℝ)
    (hclock : logRadiusClock η₀ q ≤ u) :
    greenLogDensity κ q b ≤ Real.exp (codimension κ * (u - Real.log 2 - η₀)) := by
  simpa only [Real.one_rpow, mul_one] using
    greenLogDensity_le_at_angular_exit κ η₀ u 1 hκ hκ8 q b hclock (logAngleSq_le_one κ q b)

 

theorem ClippedLogSolution.finite_angular_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hq0 : q₀.2 = 0)
    (u ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε)
    (hε0 : ε ≤ logAngleSq κ q₀ 0)
    (hlo : lo < q₀.1.im - u / (2 * ε)) (hhi : q₀.1.im < hi)
    (T : ℝ≥0) (hT : u < (4 * ε ^ 2 / Real.exp (2 * q₀.1.im)) * T) :
    ∃ τ : Ω → ℝ≥0,
      IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      (∀ ω, τ ω < T) ∧
      (∀ ω t, t ≤ τ ω →
        logRadiusClock q₀.1.im (c.Q t ω) ≤ u ∧
        ε ≤ logAngleSq κ (c.Q t ω) (B t ω) ∧
        lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi) ∧
      (∀ ω t, t < τ ω →
        logRadiusClock q₀.1.im (c.Q t ω) < u ∧ ε < logAngleSq κ (c.Q t ω) (B t ω)) ∧
      (∀ ω, logRadiusClock q₀.1.im (c.Q (τ ω) ω) = u ∨
        logAngleSq κ (c.Q (τ ω) ω) (B (τ ω) ω) = ε) ∧
      Integrable (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) = greenLogDensity κ q₀ 0 := by
  classical
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hall (n : ℕ) := c.finite_radius_cutoff hB hBm hBc hB0 hκ hκ8 hq0
    u ε ((n : ℝ) + 1) hu hε (by positivity) hε0 hlo hhi T hT
  choose τn hstop htime hin hpre hboundary hint hmean using hall
  let τ (ω : Ω) : ℝ≥0 := ⨆ n, τn n ω
  have hb (n : ℕ) (ω : Ω) : τn n ω ≤ T := (htime n ω).le
  have hbd (ω : Ω) : BddAbove (range (fun n => τn n ω)) :=
    ⟨T, by rintro v ⟨n, rfl⟩; exact hb n ω⟩
  have hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)) := bounded_iSup_stopping _ τn hstop T hb
  have hstable (ω : Ω) : ∃ n : ℕ, τ ω = τn n ω ∧
      (∀ m, n ≤ m → τn m ω = τ ω) ∧
      (logRadiusClock q₀.1.im (c.Q (τ ω) ω) = u ∨
        logAngleSq κ (c.Q (τ ω) ω) (B (τ ω) ω) = ε) := by
    obtain ⟨n, hnb⟩ := continuous_path_bounded_by_nat (fun t => B t ω) (hBc ω) T
    have hhit (m : ℕ) (hnm : n ≤ m) :
        logRadiusClock q₀.1.im (c.Q (τn m ω) ω) = u ∨
          logAngleSq κ (c.Q (τn m ω) ω) (B (τn m ω) ω) = ε := by
      rcases hboundary m ω with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have hh := hnb (τn m ω) (hb m ω)
        have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
        linarith
    have hle (m : ℕ) : τn m ω ≤ τn n ω :=
      first_radius_angle_le _ _ u ε _ _ (fun t ht => ⟨(hpre m ω t ht).1, (hpre m ω t ht).2.1⟩)
        (hhit n le_rfl)
    have he : τ ω = τn n ω := le_antisymm (ciSup_le hle) (le_ciSup (hbd ω) n)
    refine ⟨n, he, ?_, ?_⟩
    · intro m hnm
      rw [he]
      apply le_antisymm (hle m)
      exact first_radius_angle_le _ _ u ε _ _
        (fun t ht => ⟨(hpre n ω t ht).1, (hpre n ω t ht).2.1⟩) (hhit m hnm)
    · rw [he]
      exact hhit n le_rfl
  have hτtime (ω : Ω) : τ ω < T := by
    obtain ⟨n, he, _⟩ := hstable ω
    rw [he]
    exact htime n ω
  have hτin (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ ω) :
      logRadiusClock q₀.1.im (c.Q t ω) ≤ u ∧
      ε ≤ logAngleSq κ (c.Q t ω) (B t ω) ∧
      lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi := by
    obtain ⟨n, he, _⟩ := hstable ω
    obtain ⟨h1, h2, h3, h4, _⟩ := hin n ω t (by simpa only [he] using ht)
    exact ⟨h1, h2, h3, h4⟩
  have hτpre (ω : Ω) (t : ℝ≥0) (ht : t < τ ω) :
      logRadiusClock q₀.1.im (c.Q t ω) < u ∧ ε < logAngleSq κ (c.Q t ω) (B t ω) := by
    obtain ⟨n, he, _⟩ := hstable ω
    have hh := hpre n ω t (by simpa only [he] using ht)
    exact ⟨hh.1, hh.2.1⟩
  let K := Real.exp (codimension κ * (u - Real.log 2 - q₀.1.im))
  have hbound (n : ℕ) (ω : Ω) :
      ‖greenLogDensity κ (c.Q (τn n ω) ω) (B (τn n ω) ω)‖ ≤ K := by
    rw [Real.norm_eq_abs, abs_of_nonneg (greenLogDensity_nonneg _ _ _)]
    exact greenLogDensity_le_radius κ q₀.1.im u hκ hκ8 _ _ (hin n ω (τn n ω) le_rfl).1
  have hlim (ω : Ω) : Tendsto
      (fun n => greenLogDensity κ (c.Q (τn n ω) ω) (B (τn n ω) ω)) atTop
      (𝓝 (greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω))) := by
    obtain ⟨n, _, he, _⟩ := hstable ω
    apply tendsto_const_nhds.congr'
    exact (eventually_ge_atTop n).mono (fun m hm => by dsimp only; rw [he m hm])
  have hτm := stopping_time_measurable_nnreal hτ
  have hQm : Measurable (fun ω => c.Q (τ ω) ω) :=
    c.measurable.comp ((NNReal.continuous_coe.measurable.comp hτm).prodMk measurable_id)
  have hBmτ : Measurable (fun ω => B (τ ω) ω) := hBm.comp (hτm.prodMk measurable_id)
  have hfm : Measurable (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)) :=
    (greenLogDensity_contDiff κ).continuous.measurable.comp (hQm.prodMk hBmτ)
  have hfi : Integrable (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)) P := by
    apply Integrable.of_bound hfm.aestronglyMeasurable K
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (greenLogDensity_nonneg _ _ _)]
      exact greenLogDensity_le_radius κ q₀.1.im u hκ hκ8 _ _ (hτin ω (τ ω) le_rfl).1
  have hconv := tendsto_integral_of_dominated_convergence (fun _ : Ω => K)
    (fun n => (hint n).aestronglyMeasurable) (integrable_const K)
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  have hmean' : (∫ ω, greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) =
      greenLogDensity κ q₀ 0 := by
    apply tendsto_nhds_unique hconv
    simp only [hmean]
    exact tendsto_const_nhds
  exact ⟨τ, hτ, hτtime, hτin, hτpre, fun ω => (hstable ω).choose_spec.2.2, hfi, hmean'⟩

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def initialLogCoordinates (z : ℂ) : ℂ × ℝ :=
  ((z.re : ℂ) + (Real.log z.im : ℂ) * Complex.I, 0)

noncomputable def restoreLogPoint (q : ℂ × ℝ) : ℂ :=
  (q.1.re : ℂ) + (Real.exp q.1.im : ℂ) * Complex.I

lemma restoreLogPoint_im (q : ℂ × ℝ) : (restoreLogPoint q).im = Real.exp q.1.im := by
  simp only [restoreLogPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]

lemma restoreLogPoint_initial (z : ℂ) (hz : z ∈ upperHalfPlane) :
    restoreLogPoint (initialLogCoordinates z) = z := by
  apply Complex.ext <;> simp [restoreLogPoint, initialLogCoordinates, Real.exp_log hz]

lemma restoreLogPoint_derivative {Q : ℝ → ℂ × ℝ} {D : Set ℝ} {t u : ℝ}
    (hQ : HasDerivWithinAt Q (physicalLogLoewnerField u (Q t)) D t) :
    HasDerivWithinAt (fun s => restoreLogPoint (Q s))
      (2 / (restoreLogPoint (Q t) - (u : ℂ))) D t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hQ.fst
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hQ.fst
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt t hr).add
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt t hi.exp).mul_const Complex.I)
  convert hd using 1 <;> try rfl
  · let Z := restoreLogPoint (Q t) - (u : ℂ)
    have he : (((Q t).1.re - u : ℝ) : ℂ) + (Real.exp (Q t).1.im : ℂ) * Complex.I = Z := by
      simp only [Z, restoreLogPoint, Complex.ofReal_sub]; ring
    have hZi : Z.im = Real.exp (Q t).1.im := by
      dsimp only [Z]
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero, restoreLogPoint_im]
    simp only [Function.comp_def, Complex.reCLM_apply, Complex.ofRealCLM_apply,
      Complex.imCLM_apply, physicalLogLoewnerField, he, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero, mul_one, zero_add]
    change 2 / Z = ((2 * Z⁻¹.re : ℝ) : ℂ) +
      ((Real.exp (Q t).1.im * (-2 * Complex.normSq Z⁻¹) : ℝ) : ℂ) * Complex.I
    apply Complex.ext
    · simp only [div_eq_mul_inv, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
        zero_mul, sub_zero, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero]
    · simp only [div_eq_mul_inv, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
        zero_mul, add_zero, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.inv_im,
        Complex.normSq_inv, hZi]
      ring

 

theorem clipped_log_identification
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (hz : z ∈ upperHalfPlane) (T : ℝ≥0)
    (lo hi : ℝ) (hle : lo ≤ hi) (Q : ℝ → ℂ × ℝ)
    (hQ0 : Q 0 = initialLogCoordinates z)
    (hQd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt Q
      (clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t)) (Icc 0 (T : ℝ)) t)
    (hb : ∀ t ∈ Icc 0 (T : ℝ), (Q t).1.im ∈ Icc lo hi) :
    z ∈ survivingDomain γ T ∧ EqOn Q (logLoewnerCoordinates G z) (Icc 0 (T : ℝ)) := by
  let W (t : ℝ) := restoreLogPoint (Q t)
  have hW0 : W 0 = z := by
    change restoreLogPoint (Q 0) = z
    rw [hQ0, restoreLogPoint_initial z hz]
  have hp (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : 0 < (W t).im := by
    change 0 < (restoreLogPoint (Q t)).im
    rw [restoreLogPoint_im]; exact Real.exp_pos _
  have hd (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt W
      (2 / (W t - (U t.toNNReal : ℂ))) (Icc 0 (T : ℝ)) t := by
    apply restoreLogPoint_derivative
    have hh := hQd t ht
    rwa [clippedLogLoewnerField_eq_physical lo hi hle _ _ (hb t ht)] at hh
  obtain ⟨hlive, he⟩ := loewner_survival_of_positive_solution hU h T W hp hd
  rw [hW0] at hlive he
  have hη : Real.log (G T z).im = (Q T).1.im := by
    rw [he]
    change Real.log (restoreLogPoint (Q T)).im = _
    rw [restoreLogPoint_im, Real.log_exp]
  have hh₀ := hb 0 ⟨le_rfl, T.coe_nonneg⟩
  rw [hQ0] at hh₀
  have hhi : Real.log z.im ≤ hi := by simpa [initialLogCoordinates] using hh₀.2
  exact ⟨hlive, clipped_log_loewner_agrees hU h T z hlive lo hi hle
    (by rw [hη]; exact (hb T ⟨T.coe_nonneg, le_rfl⟩).1) hhi Q hQ0 hQd⟩

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem exists_joint_clipped_flow
    {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ≥0 → Ω → ℝ)
    (hUm : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2))
    (hUc : ∀ ω, Continuous (fun t => U t ω))
    (q₀ : Ω → ℂ × ℝ) (hq₀ : Measurable q₀)
    (lo hi : ℝ) (hle : lo ≤ hi) :
    ∃ Q : ℝ → Ω → ℂ × ℝ,
      Measurable (fun p : ℝ × Ω => Q p.1 p.2) ∧
      (∀ ω, Q 0 ω = q₀ ω) ∧
      (∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω)
        (clippedLogLoewnerField lo hi hle (U t.toNNReal ω) (Q t ω)) (Ici 0) t) := by
  obtain ⟨L, K, hbound, hlip⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) (x : ℂ × ℝ) :=
    clippedLogLoewnerField lo hi hle (U t.toNNReal ω) (q₀ ω + x)
  have hUr : Measurable (fun p : ℝ × Ω => U p.1.toNNReal p.2) :=
    hUm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hV : Measurable (fun p : (ℝ × Ω) × (ℂ × ℝ) => V p.1.1 p.1.2 p.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun p : (ℝ × Ω) × (ℂ × ℝ) => (U p.1.1.toNNReal p.1.2, q₀ p.1.2 + p.2)))
    exact (continuous_clippedLogLoewnerField lo hi hle).measurable.comp
      ((hUr.comp measurable_fst).prodMk
        ((hq₀.comp (measurable_snd.comp measurable_fst)).add measurable_snd))
  have hVc (ω : Ω) (x : ℂ × ℝ) : Continuous (fun t : ℝ => V t ω x) := by
    change Continuous ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun t : ℝ => (U t.toNNReal ω, q₀ ω + x)))
    exact (continuous_clippedLogLoewnerField lo hi hle).comp
      (((hUc ω).comp continuous_real_toNNReal).prodMk continuous_const)
  have hVl (ω : Ω) (t : ℝ) : LipschitzWith K (V t ω) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [V, dist_add_left] using (hlip (U t.toNNReal ω)).dist_le_mul (q₀ ω + x) (q₀ ω + y)
  obtain ⟨X, hXm, _, hX0, hXd, _⟩ := exists_measurable_global_bounded_ode_picard
    V 0 L K hV hVc hVl (fun ω t x => hbound _ _)
  refine ⟨fun t ω => q₀ ω + X t ω, (hq₀.comp measurable_snd).add hXm, ?_, ?_⟩
  · intro ω; change q₀ ω + X 0 ω = q₀ ω; rw [hX0, add_zero]
  · intro ω t ht
    simpa only [V] using (hXd ω t ht).const_add (q₀ ω)

lemma measurable_initialLogCoordinates : Measurable initialLogCoordinates := by
  exact ((Complex.measurable_ofReal.comp Complex.measurable_re).add
    ((Complex.measurable_ofReal.comp (Real.measurable_log.comp Complex.measurable_im)).mul_const
      Complex.I)).prodMk measurable_const

 
theorem exists_spatial_clipped_flow
    {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ≥0 → Ω → ℝ)
    (hUm : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2))
    (hUc : ∀ ω, Continuous (fun t => U t ω)) (n : ℕ) :
    ∃ Q : ℝ → ℂ × Ω → ℂ × ℝ,
      Measurable (fun p : ℝ × (ℂ × Ω) => Q p.1 p.2) ∧
      (∀ z ω, Q 0 (z, ω) = initialLogCoordinates z) ∧
      (∀ z ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s (z, ω))
        (clippedLogLoewnerField (-(n : ℝ)) n (by linarith [Nat.cast_nonneg (α := ℝ) n])
          (U t.toNNReal ω) (Q t (z, ω))) (Ici 0) t) := by
  obtain ⟨Q, hQm, hQ0, hQd⟩ := exists_joint_clipped_flow (fun t (p : ℂ × Ω) => U t p.2)
    (hUm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
    (fun p => hUc p.2) (fun p => initialLogCoordinates p.1)
    (measurable_initialLogCoordinates.comp measurable_fst) (-(n : ℝ)) n (by linarith [Nat.cast_nonneg (α := ℝ) n])
  exact ⟨Q, hQm, fun z ω => hQ0 (z, ω), fun z ω t ht => hQd (z, ω) t ht⟩

end SLEExactGauge
end

 
section

open Set Filter
open scoped Topology NNReal
namespace SLEExactGauge

lemma clipped_log_height_derivative
    {U : ℝ≥0 → ℝ} {lo hi : ℝ} {hle : lo ≤ hi} {Q : ℝ → ℂ × ℝ}
    {t : ℝ} {S : Set ℝ}
    (hd : HasDerivWithinAt Q
      (clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t)) S t) :
    HasDerivWithinAt (fun s => (Q s).1.im)
      (-2 * Complex.normSq (clippedCenter lo hi hle (U t.toNNReal) (Q t))⁻¹) S t := by
  simpa only [Function.comp_def, Complex.imCLM_apply, clippedLogLoewnerField,
    Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    using Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd.fst

lemma clipped_log_height_antitone
    {U : ℝ≥0 → ℝ} {lo hi : ℝ} {hle : lo ≤ hi} {Q : ℝ → ℂ × ℝ}
    (T : ℝ≥0)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt Q
      (clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t)) (Icc 0 (T : ℝ)) t) :
    AntitoneOn (fun t => (Q t).1.im) (Icc 0 (T : ℝ)) := by
  have he (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) := clipped_log_height_derivative (hd t ht)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (fun t ht => (he t ht).continuousWithinAt)
    (fun t ht => (he t (interior_subset ht)).mono interior_subset)
  intro t ht
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Complex.normSq_nonneg _)

 

lemma clipped_log_identification_of_endpoint
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ upperHalfPlane)
    (lo hi : ℝ) (hle : lo ≤ hi) (Q : ℝ → ℂ × ℝ)
    (hQ0 : Q 0 = initialLogCoordinates z)
    (hQd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt Q
      (clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t)) (Icc 0 (T : ℝ)) t)
    (hlo : lo ≤ (Q T).1.im) (hhi : Real.log z.im ≤ hi) :
    z ∈ survivingDomain γ T ∧ EqOn Q (logLoewnerCoordinates G z) (Icc 0 (T : ℝ)) := by
  apply clipped_log_identification hU h z hz T lo hi hle Q hQ0 hQd
  have hm := clipped_log_height_antitone T hQd
  intro t ht
  refine ⟨hlo.trans (hm ht ⟨T.coe_nonneg, le_rfl⟩ ht.2), ?_⟩
  have hh := hm (show (0 : ℝ) ∈ Icc 0 (T : ℝ) from ⟨le_rfl, T.coe_nonneg⟩) ht ht.1
  change (Q t).1.im ≤ (Q 0).1.im at hh
  rw [hQ0] at hh
  have hinit : (initialLogCoordinates z).1.im = Real.log z.im := by
    simp [initialLogCoordinates]
  rw [hinit] at hh
  exact hh.trans hhi

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def powerLogDensity (κ p a : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  Real.exp (-p * Real.log 2 + p * q.2 +
    (a - p) * q.1.im -
      (a / 2) * Real.log (greenLogNormSq κ q x))
lemma powerLogDensity_contDiff (κ p a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => powerLogDensity κ p a zz.1 zz.2) := by
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => zz.1.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst.fst
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => zz.1.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst.fst
  have hN : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => greenLogNormSq κ zz.1 zz.2) := by
    exact ((hre.sub (contDiff_const.mul contDiff_snd)).pow 2).add
      ((contDiff_const.mul him).exp)
  have hlog := hN.log (fun zz => (greenLogNormSq_pos κ zz.1 zz.2).ne')
  unfold powerLogDensity
  apply ContDiff.exp
  exact (((contDiff_const.add (contDiff_const.mul contDiff_fst.snd)).add
    (contDiff_const.mul him)).sub (contDiff_const.mul hlog))

lemma powerLogDensity_spatial_derivative (κ p a : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    HasDerivAt (powerLogDensity κ p a q)
      (powerLogDensity κ p a q x * (a * Real.sqrt κ * (q.1.re - Real.sqrt κ * x) /
        greenLogNormSq κ q x)) x := by
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2 * (q.1.re - Real.sqrt κ * x) * (-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2 * q.1.im)) using 1 <;> try rfl
    simp
  have hlog := hN.log (greenLogNormSq_pos κ q x).ne'
  have hd := ((hasDerivAt_const x (-p * Real.log 2 + p * q.2 +
    (a - p) * q.1.im)).sub
      (hlog.const_mul (a / 2))).exp
  convert hd using 1 <;> try rfl
  dsimp only [powerLogDensity, Pi.sub_apply, Pi.mul_apply, Function.comp_def]
  ring

lemma powerLogDensity_spatial_second (κ p a : ℝ) (hκ : 0 ≤ κ) (q : ℂ × ℝ) (x : ℝ) :
    iteratedDeriv 2 (powerLogDensity κ p a q) x =
      powerLogDensity κ p a q x * κ * a *
        ((a + 1) * (q.1.re - Real.sqrt κ * x) ^ 2 - Real.exp (2 * q.1.im)) /
        (greenLogNormSq κ q x) ^ 2 := by
  have hd : deriv (powerLogDensity κ p a q) = fun x =>
      powerLogDensity κ p a q x * (a * Real.sqrt κ * (q.1.re - Real.sqrt κ * x) /
        greenLogNormSq κ q x) := funext fun x => (powerLogDensity_spatial_derivative κ p a q x).deriv
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2 * (q.1.re - Real.sqrt κ * x) * (-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2 * q.1.im)) using 1 <;> try rfl
    simp
  have hcoef := (hX.const_mul (a * Real.sqrt κ)).div hN
    (greenLogNormSq_pos κ q x).ne'
  have hsecond := (powerLogDensity_spatial_derivative κ p a q x).mul hcoef
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
  dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, id_eq] at hsecond
  change HasDerivAt (fun y => powerLogDensity κ p a q y *
    (a * Real.sqrt κ * (q.1.re - Real.sqrt κ * y) / greenLogNormSq κ q y)) _ x at hsecond
  rw [hsecond.deriv]
  have hn := (greenLogNormSq_pos κ q x).ne'
  dsimp only [greenLogNormSq]
  generalize powerLogDensity κ p a q x = f
  generalize q.1.re - Real.sqrt κ * x = X
  generalize Real.exp (2 * q.1.im) = Y
  have hs := Real.sq_sqrt hκ
  generalize Real.sqrt κ = r at *
  rw [← hs]
  field_simp
  ring

lemma powerLogDensity_directional (κ p a : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ p a r x) q) v =
      powerLogDensity κ p a q x * (p * v.2 +
        (a - p) * v.1.im - (a / 2) *
          ((2 * (q.1.re - Real.sqrt κ * x) * v.1.re +
            2 * Real.exp (2 * q.1.im) * v.1.im) / greenLogNormSq κ q x)) := by
  have hzre : HasDerivAt (fun t : ℝ => (q + t • v).1.re) v.1.re 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_re, Complex.smul_re, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.re).const_add q.1.re
  have hzim : HasDerivAt (fun t : ℝ => (q + t • v).1.im) v.1.im 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_im, Complex.smul_im, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.im).const_add q.1.im
  have hj : HasDerivAt (fun t : ℝ => (q + t • v).2) v.2 0 := by
    simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, id_eq, one_mul]
      using ((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add q.2
  have hN : HasDerivAt (fun t : ℝ => greenLogNormSq κ (q + t • v) x)
      (2 * (q.1.re - Real.sqrt κ * x) * v.1.re +
        2 * Real.exp (2 * q.1.im) * v.1.im) 0 := by
    convert ((hzre.sub_const (Real.sqrt κ * x)).pow 2).add ((hzim.const_mul 2).exp) using 1 <;> try rfl
    simp only [zero_smul, add_zero, Nat.cast_ofNat]
    ring
  have hlog := hN.log (by simpa only [zero_smul, add_zero] using (greenLogNormSq_pos κ q x).ne')
  have hcalc := (((hj.const_mul (p)).const_add (-p * Real.log 2)).add
    (hzim.const_mul (a - p))).sub
      (hlog.const_mul (a / 2))
  have hline : HasDerivAt (fun t : ℝ => powerLogDensity κ p a (q + t • v) x)
      (powerLogDensity κ p a q x * (p * v.2 +
        (a - p) * v.1.im - (a / 2) *
          ((2 * (q.1.re - Real.sqrt κ * x) * v.1.re +
            2 * Real.exp (2 * q.1.im) * v.1.im) / greenLogNormSq κ q x))) 0 := by
    convert hcalc.exp using 1 <;> try rfl
    simp only [Pi.sub_apply, Pi.add_apply, zero_smul, add_zero]
    simp only [powerLogDensity]
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => powerLogDensity κ p a r x) :=
    (powerLogDensity_contDiff κ p a).comp (contDiff_id.prodMk contDiff_const)
  have haff : HasDerivAt (fun t : ℝ => q + t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hfd : HasFDerivAt (fun r : ℂ × ℝ => powerLogDensity κ p a r x)
      (fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ p a r x) q) (q + (0 : ℝ) • v) := by
    simpa using ((hcd.differentiable (by simp)) q).hasFDerivAt
  have hchain := hfd.comp_hasDerivAt 0 haff
  simpa only [Function.comp_def] using hchain.unique hline

lemma powerLogDensity_pair_directional (κ p a : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun zz : (ℂ × ℝ) × ℝ => powerLogDensity κ p a zz.1 zz.2) (q, x) (v, 0) =
      fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ p a r x) q v := by
  have hd := ((powerLogDensity_contDiff κ p a).differentiable (by simp)) (q, x)
  have hp := (hasFDerivAt_id (𝕜 := ℝ) q).prodMk (hasFDerivAt_const (𝕜 := ℝ) (E := ℂ × ℝ) x q)
  have hc := (hd.hasFDerivAt.comp q hp).fderiv
  have he := congrArg (fun D : (ℂ × ℝ) →L[ℝ] ℝ => D v) hc
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, id_eq, zero_apply] using he.symm

 

lemma exists_compact_power_field (κ p a R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : (ℂ × ℝ) × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ q x, ‖(q, x)‖ ≤ R → φ (q, x) = powerLogDensity κ p a q x) ∧
      (∀ q x, ‖(q, x)‖ ≤ R →
        fderiv ℝ φ (q, x) = fderiv ℝ (fun zz : (ℂ × ℝ) × ℝ => powerLogDensity κ p a zz.1 zz.2) (q, x)) ∧
      (∀ q x, ‖(q, x)‖ ≤ R → iteratedDeriv 2 (fun y => φ (q, y)) x =
        iteratedDeriv 2 (powerLogDensity κ p a q) x) := by
  let b : ContDiffBump (0 : (ℂ × ℝ) × ℝ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let φ (zz : (ℂ × ℝ) × ℝ) : ℝ := b zz * powerLogDensity κ p a zz.1 zz.2
  have hnear (zz : (ℂ × ℝ) × ℝ) (hp : ‖zz‖ ≤ R) :
      φ =ᶠ[𝓝 zz] (fun r : (ℂ × ℝ) × ℝ => powerLogDensity κ p a r.1 r.2) := by
    have hball : zz ∈ Metric.ball (0 : (ℂ × ℝ) × ℝ) b.rIn := by
      simp only [Metric.mem_ball, dist_zero_right]
      change ‖zz‖ < R + 1
      linarith
    filter_upwards [b.eventuallyEq_one_of_mem_ball hball] with r hr
    simp only [φ, hr, Pi.one_apply, one_mul]
  refine ⟨φ, b.contDiff.mul (powerLogDensity_contDiff κ p a), b.hasCompactSupport.mul_right,
    (fun q x h => (hnear (q, x) h).eq_of_nhds), ?_, ?_⟩
  · intro q x h
    exact (hnear (q, x) h).fderiv_eq
  · intro q x h
    have he := (hnear (q, x) h).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto x)
    exact he.iteratedDeriv_eq 2

 
lemma power_physical_generator (κ p a : ℝ) (hκ : 0 ≤ κ)
    (q : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ p a r x) q)
      (physicalLogLoewnerField (Real.sqrt κ * x) q) +
      (1 / 2 : ℝ) * iteratedDeriv 2 (powerLogDensity κ p a q) x =
      powerLogDensity κ p a q x *
        ((-4 * a + κ * a * (a + 1) / 2) * (q.1.re - Real.sqrt κ * x) ^ 2 +
          (4 * p - κ * a / 2) * Real.exp (2 * q.1.im)) /
        (greenLogNormSq κ q x) ^ 2 := by
  rw [powerLogDensity_directional, powerLogDensity_spatial_second κ p a hκ]
  obtain ⟨hr, hi, hj⟩ := physicalLogLoewnerField_components κ q x
  rw [hr, hi, hj]
  have hn := (greenLogNormSq_pos κ q x).ne'
  field_simp
  dsimp only [greenLogNormSq]
  ring

lemma powerLogDensity_radius_angle (κ p a η₀ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    powerLogDensity κ p a q x =
      Real.exp (p * (logRadiusClock η₀ q - Real.log 2 - η₀)) *
        (logAngleSq κ q x) ^ (a / 2) := by
  rw [Real.rpow_def_of_pos (logAngleSq_pos κ q x), ← Real.exp_add]
  unfold logAngleSq
  rw [Real.log_div (Real.exp_ne_zero _) (greenLogNormSq_pos κ q x).ne', Real.log_exp]
  unfold powerLogDensity logRadiusClock
  congr 1
  ring

 

lemma green_weighted_power_generator (κ b : ℝ) (hκ : 0 < κ)
    (q : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ (codimension κ)
        (greenExponent κ - b) r x) q)
      (physicalLogLoewnerField (Real.sqrt κ * x) q) +
      (1 / 2 : ℝ) * iteratedDeriv 2
        (powerLogDensity κ (codimension κ) (greenExponent κ - b) q) x =
      powerLogDensity κ (codimension κ) (greenExponent κ - b) q x *
        logClockRate κ q x * (κ * b / 8) *
          (1 - (greenExponent κ - b) * ((logAngleSq κ q x)⁻¹ - 1)) := by
  rw [power_physical_generator κ _ _ hκ.le]
  unfold logClockRate logAngleSq
  have hn := (greenLogNormSq_pos κ q x).ne'
  have hy := Real.exp_ne_zero (2 * q.1.im)
  dsimp only [greenExponent, codimension, dimension]
  field_simp
  dsimp only [greenLogNormSq]
  ring

end SLEExactGauge
end

 
end

end OAI
