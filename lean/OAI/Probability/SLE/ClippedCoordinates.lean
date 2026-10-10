import Mathlib
import OAI.Probability.SLE.OptionalStopping

namespace OAI

/-! Clipped Coordinates for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
lemma clippedCenter_norm_lower (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ) (q : ℂ × ℝ) :
    Real.exp lo ≤ ‖clippedCenter lo hi hle u q‖ := by
  calc
    _ ≤ clippedHeight lo hi hle q := (clippedHeight_bounds lo hi hle q).1
    _ = (clippedCenter lo hi hle u q).im := (clippedCenter_im lo hi hle u q).symm
    _ ≤ ‖clippedCenter lo hi hle u q‖ := Complex.im_le_norm _

lemma clippedCenter_inv_norm_bound (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ) (q : ℂ × ℝ) :
    ‖(clippedCenter lo hi hle u q)⁻¹‖ ≤ (Real.exp lo)⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ (Real.exp_pos lo) (clippedCenter_norm_lower lo hi hle u q)

lemma clippedCenter_dist (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ) (q r : ℂ × ℝ) :
    dist (clippedCenter lo hi hle u q) (clippedCenter lo hi hle u r) ≤
      (1 + Real.exp hi) * dist q r := by
  have he := (exp_clamp_lipschitz lo hi hle).dist_le_mul q.1.im r.1.im
  have hY : |clippedHeight lo hi hle q - clippedHeight lo hi hle r| ≤
      Real.exp hi * ‖q.1 - r.1‖ := by
    change |Real.exp (projIcc lo hi hle q.1.im) - Real.exp (projIcc lo hi hle r.1.im)| ≤ _
    change |Real.exp (projIcc lo hi hle q.1.im) - Real.exp (projIcc lo hi hle r.1.im)| ≤
      Real.exp hi * |q.1.im - r.1.im| at he
    exact he.trans
      (mul_le_mul_of_nonneg_left (show |q.1.im - r.1.im| ≤ ‖q.1 - r.1‖ from
        Complex.abs_im_le_norm (q.1 - r.1)) (Real.exp_pos hi).le)
  have hX : |q.1.re - r.1.re| ≤ ‖q.1 - r.1‖ := Complex.abs_re_le_norm (q.1 - r.1)
  have hsub : clippedCenter lo hi hle u q - clippedCenter lo hi hle u r =
      ((q.1.re - r.1.re : ℝ) : ℂ) +
        ((clippedHeight lo hi hle q - clippedHeight lo hi hle r : ℝ) : ℂ) * Complex.I := by
    simp only [clippedCenter, Complex.ofReal_sub]
    ring
  rw [dist_eq_norm, hsub]
  calc
    _ ≤ |q.1.re - r.1.re| + |clippedHeight lo hi hle q - clippedHeight lo hi hle r| := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] using
        norm_add_le ((q.1.re - r.1.re : ℝ) : ℂ)
          (((clippedHeight lo hi hle q - clippedHeight lo hi hle r : ℝ) : ℂ) * Complex.I)
    _ ≤ (1 + Real.exp hi) * ‖q.1 - r.1‖ := by linarith
    _ ≤ (1 + Real.exp hi) * dist q r := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [dist_eq_norm]
      exact norm_fst_le (q - r)

lemma clippedCenter_inv_dist (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ) (q r : ℂ × ℝ) :
    dist (clippedCenter lo hi hle u q)⁻¹ (clippedCenter lo hi hle u r)⁻¹ ≤
      ((Real.exp lo)⁻¹ ^ 2 * (1 + Real.exp hi)) * dist q r := by
  let b := (Real.exp lo)⁻¹
  have hb : 0 ≤ b := by dsimp [b]; positivity
  rw [dist_eq_norm, inv_sub_inv' (clippedCenter_ne_zero lo hi hle u q)
    (clippedCenter_ne_zero lo hi hle u r), norm_mul, norm_mul]
  calc
    _ ≤ b * ((1 + Real.exp hi) * dist q r) * b := by
      gcongr
      · exact clippedCenter_inv_norm_bound lo hi hle u q
      · simpa only [← dist_eq_norm, dist_comm] using clippedCenter_dist lo hi hle u q r
      · exact clippedCenter_inv_norm_bound lo hi hle u r
    _ = _ := by dsimp [b]; ring

noncomputable def logLoewnerVector (v : ℂ) : ℂ × ℝ :=
  (((2 * v.re : ℝ) : ℂ) + ((-2 * Complex.normSq v : ℝ) : ℂ) * Complex.I,
    (-2 * v ^ 2).re)

lemma bounded_normSq_dist {v w : ℂ} {b : ℝ} (hv : ‖v‖ ≤ b) (hw : ‖w‖ ≤ b) :
    |Complex.normSq v - Complex.normSq w| ≤ 2 * b * dist v w := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    show ‖v‖ ^ 2 - ‖w‖ ^ 2 = (‖v‖ - ‖w‖) * (‖v‖ + ‖w‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg v) (norm_nonneg w))]
  calc
    _ ≤ ‖v - w‖ * (‖v‖ + ‖w‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le v w)
        (add_nonneg (norm_nonneg v) (norm_nonneg w))
    _ ≤ ‖v - w‖ * (b + b) := by gcongr
    _ = _ := by rw [dist_eq_norm]; ring

lemma bounded_sq_dist {v w : ℂ} {b : ℝ} (hv : ‖v‖ ≤ b) (hw : ‖w‖ ≤ b) :
    ‖v ^ 2 - w ^ 2‖ ≤ 2 * b * dist v w := by
  rw [show v ^ 2 - w ^ 2 = (v - w) * (v + w) by ring, norm_mul]
  calc
    _ ≤ ‖v - w‖ * (‖v‖ + ‖w‖) := mul_le_mul_of_nonneg_left (norm_add_le v w) (norm_nonneg _)
    _ ≤ ‖v - w‖ * (b + b) := by gcongr
    _ = _ := by rw [dist_eq_norm]; ring

lemma logLoewnerVector_dist {v w : ℂ} {b : ℝ} (hv : ‖v‖ ≤ b) (hw : ‖w‖ ≤ b) :
    dist (logLoewnerVector v) (logLoewnerVector w) ≤ (2 + 4 * b) * dist v w := by
  rw [dist_eq_norm]
  apply norm_prod_le_iff.mpr
  constructor
  · have hr : ((logLoewnerVector v - logLoewnerVector w).1).re = 2 * (v.re - w.re) := by
      simp [logLoewnerVector]
      ring
    have hi : ((logLoewnerVector v - logLoewnerVector w).1).im =
        -2 * (Complex.normSq v - Complex.normSq w) := by
      simp [logLoewnerVector]
      ring
    have hRe : |v.re - w.re| ≤ dist v w := by
      simpa only [dist_eq_norm, Complex.sub_re] using Complex.abs_re_le_norm (v - w)
    calc
      _ ≤ |((logLoewnerVector v - logLoewnerVector w).1).re| +
          |((logLoewnerVector v - logLoewnerVector w).1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = 2 * |v.re - w.re| + 2 * |Complex.normSq v - Complex.normSq w| := by
        rw [hr, hi, abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * dist v w + 2 * (2 * b * dist v w) := by
        gcongr
        exact bounded_normSq_dist hv hw
      _ = _ := by ring
  · have he : (logLoewnerVector v - logLoewnerVector w).2 = (-2 * (v ^ 2 - w ^ 2)).re := by
      simp only [logLoewnerVector, Prod.snd_sub, mul_sub, Complex.sub_re]
    rw [he, Real.norm_eq_abs]
    calc
      _ ≤ ‖-2 * (v ^ 2 - w ^ 2)‖ := Complex.abs_re_le_norm _
      _ = 2 * ‖v ^ 2 - w ^ 2‖ := by rw [norm_mul]; norm_num
      _ ≤ 2 * (2 * b * dist v w) := by gcongr; exact bounded_sq_dist hv hw
      _ ≤ (2 + 4 * b) * dist v w := by nlinarith [show 0 ≤ dist v w from dist_nonneg]

lemma logLoewnerVector_norm {v : ℂ} {b : ℝ} (hb : 0 ≤ b) (hv : ‖v‖ ≤ b) :
    ‖logLoewnerVector v‖ ≤ (2 + 4 * b) * b := by
  have hh := logLoewnerVector_dist hv (show ‖(0 : ℂ)‖ ≤ b by simpa using hb)
  have h0 : logLoewnerVector 0 = 0 := by simp [logLoewnerVector]
  rw [h0, dist_zero_right, dist_zero_right] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hv (by positivity))

lemma clippedLogLoewnerField_bounds (lo hi : ℝ) (hle : lo ≤ hi) :
    ∃ (L K : ℝ≥0),
      (∀ u q, ‖clippedLogLoewnerField lo hi hle u q‖ ≤ L) ∧
      (∀ u, LipschitzWith K (clippedLogLoewnerField lo hi hle u)) := by
  let b : ℝ := (Real.exp lo)⁻¹
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let L : ℝ≥0 := ⟨(2 + 4 * b) * b, by positivity⟩
  let K : ℝ≥0 := ⟨(2 + 4 * b) * (b ^ 2 * (1 + Real.exp hi)), by positivity⟩
  refine ⟨L, K, ?_, ?_⟩
  · intro u q
    exact logLoewnerVector_norm hb (clippedCenter_inv_norm_bound lo hi hle u q)
  · intro u
    apply LipschitzWith.of_dist_le_mul
    intro q r
    change dist (logLoewnerVector (clippedCenter lo hi hle u q)⁻¹)
      (logLoewnerVector (clippedCenter lo hi hle u r)⁻¹) ≤ _
    calc
      _ ≤ (2 + 4 * b) * dist (clippedCenter lo hi hle u q)⁻¹ (clippedCenter lo hi hle u r)⁻¹ :=
        logLoewnerVector_dist (clippedCenter_inv_norm_bound lo hi hle u q)
          (clippedCenter_inv_norm_bound lo hi hle u r)
      _ ≤ (2 + 4 * b) * ((b ^ 2 * (1 + Real.exp hi)) * dist q r) :=
        mul_le_mul_of_nonneg_left (clippedCenter_inv_dist lo hi hle u q r) (by positivity)
      _ = _ := by
        change (2 + 4 * b) * (b ^ 2 * (1 + Real.exp hi) * dist q r) =
          ((2 + 4 * b) * (b ^ 2 * (1 + Real.exp hi))) * dist q r
        ring

lemma continuous_clippedLogLoewnerField (lo hi : ℝ) (hle : lo ≤ hi) :
    Continuous (fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) := by
  have hZ : Continuous (fun p : ℝ × (ℂ × ℝ) => clippedCenter lo hi hle p.1 p.2) := by
    dsimp only [clippedCenter, clippedHeight]
    fun_prop
  have hv : Continuous (fun p : ℝ × (ℂ × ℝ) => (clippedCenter lo hi hle p.1 p.2)⁻¹) :=
    hZ.inv₀ (fun p => clippedCenter_ne_zero lo hi hle p.1 p.2)
  have hF : Continuous logLoewnerVector := by fun_prop [logLoewnerVector]
  exact hF.comp hv

 

theorem clipped_log_loewner_solution
    {Ω : Type*} [MeasurableSpace Ω] (U : ℝ → Ω → ℝ)
    (hU : Measurable (fun q : ℝ × Ω => U q.1 q.2))
    (hc : ∀ ω, Continuous (fun t : ℝ => U t ω))
    (lo hi : ℝ) (hle : lo ≤ hi) (q₀ : ℂ × ℝ) (T : ℝ≥0) :
    ∃ (L : ℝ≥0) (Q : ℝ → Ω → ℂ × ℝ),
      Measurable (fun q : ℝ × Ω => Q q.1 q.2) ∧
      (∀ ω, LipschitzWith L (fun t => Q t ω)) ∧
      (∀ ω, Q 0 ω = q₀) ∧
      (∀ ω t, t ∈ Icc 0 (T : ℝ) →
        HasDerivWithinAt (fun s => Q s ω)
          (clippedLogLoewnerField lo hi hle (U t ω) (Q t ω))
          (Icc 0 (T : ℝ)) t) := by
  obtain ⟨L, K, hbound, hlip⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) (q : ℂ × ℝ) := clippedLogLoewnerField lo hi hle (U t ω) q
  have hF := continuous_clippedLogLoewnerField lo hi hle
  have hm : Measurable (fun q : (ℝ × Ω) × (ℂ × ℝ) => V q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun q : (ℝ × Ω) × (ℂ × ℝ) => (U q.1.1 q.1.2, q.2)))
    apply hF.measurable.comp
    exact (hU.comp measurable_fst).prodMk measurable_snd
  have hcont (ω : Ω) (q : ℂ × ℝ) : Continuous (fun t : ℝ => V t ω q) := by
    change Continuous ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun t : ℝ => (U t ω, q)))
    exact hF.comp ((hc ω).prodMk continuous_const)
  obtain ⟨Q, hQ⟩ := exists_measurable_bounded_ode V q₀ T L K hm hcont
    (fun ω t => hlip (U t ω)) (fun ω t q => hbound (U t ω) q)
  exact ⟨L, Q, hQ⟩

theorem exists_measurable_bounded_ode_picard
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (V : ℝ → Ω → E → E) (x₀ : E) (T L K : ℝ≥0)
    (hV : Measurable (fun q : (ℝ × Ω) × E => V q.1.1 q.1.2 q.2))
    (hc : ∀ ω x, Continuous (fun t : ℝ => V t ω x))
    (hl : ∀ ω t, LipschitzWith K (V t ω))
    (hb : ∀ ω t x, ‖V t ω x‖ ≤ L) :
    ∃ X : ℝ → Ω → E,
      Measurable (fun q : ℝ × Ω => X q.1 q.2) ∧
      (∀ ω, LipschitzWith L (fun t => X t ω)) ∧
      (∀ ω, X 0 ω = x₀) ∧
      (∀ ω t, t ∈ Icc 0 (T : ℝ) →
        HasDerivWithinAt (fun u => X u ω) (V t ω (X t ω)) (Icc 0 (T : ℝ)) t) ∧
      (∀ t ω, Tendsto (fun n => picardApprox V x₀ n (projIcc 0 (T : ℝ) T.coe_nonneg t) ω) atTop (𝓝 (X t ω))) := by
  let t₀ : Icc (0 : ℝ) T := ⟨0, ⟨le_rfl, T.coe_nonneg⟩⟩
  have hPL (ω : Ω) : IsPicardLindelof (fun t x => V t ω x) t₀ x₀ (L * T) 0 L K := by
    refine ⟨fun t ht => (hl ω t).lipschitzOnWith, fun x hx => (hc ω x).continuousOn,
      fun t ht x hx => hb ω t x, ?_⟩
    simp only [t₀, sub_zero, sub_self, max_eq_left T.coe_nonneg, NNReal.coe_mul,
      NNReal.coe_zero, le_refl]
  have hx : x₀ ∈ Metric.closedBall x₀ (0 : ℝ) := Metric.mem_closedBall_self le_rfl
  choose α hα using fun ω => ODE.FunSpace.exists_isFixedPt_next (hPL ω) hx
  let X (t : ℝ) (ω : Ω) := (α ω).compProj t
  let α₀ : ODE.FunSpace t₀ x₀ 0 L :=
    ⟨fun _ => x₀, (LipschitzWith.const x₀).weaken (show (0 : ℝ≥0) ≤ L from bot_le), hx⟩
  have hα₀ (t : Icc (0 : ℝ) T) : α₀ t = x₀ := rfl
  have hconv (t : Icc (0 : ℝ) T) (ω : Ω) :
      Tendsto (fun n => picardApprox V x₀ n t ω) atTop (𝓝 ((α ω) t)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => ?_) (by simpa only [zero_mul] using (FloorSemiring.tendsto_pow_div_factorial_atTop
        ((K : ℝ) * |(t : ℝ)|)).mul_const (dist α₀ (α ω)))
    have hh := ODE.FunSpace.dist_iterate_next_apply_le (hPL ω) hx α₀ (α ω) n t
    rw [(hα ω).iterate n] at hh
    simpa only [t₀, sub_zero, picardApprox_eq_iterate ω (hPL ω) α₀ hα₀ n t] using hh
  refine ⟨X, ?_, ?_, ?_, ?_, ?_⟩
  · apply measurable_of_tendsto_metrizable
      (f := fun n q => picardApprox V x₀ n (projIcc 0 (T : ℝ) T.coe_nonneg q.1) q.2)
    · intro n
      exact (picardApprox_measurable V x₀ hV n).comp
        (((continuous_subtype_val.comp (continuous_projIcc (h := T.coe_nonneg))).measurable.comp measurable_fst).prodMk measurable_snd)
    · apply tendsto_pi_nhds.mpr
      intro q
      exact hconv (projIcc 0 (T : ℝ) T.coe_nonneg q.1) q.2
  · intro ω
    simpa only [mul_one, X, ODE.FunSpace.compProj, Function.comp_def] using (α ω).lipschitzWith.comp (LipschitzWith.projIcc T.coe_nonneg)
  · intro ω
    change (α ω).compProj 0 = x₀
    rw [ODE.FunSpace.compProj_of_mem t₀.property]
    exact ODE.FunSpace.apply_of_zero (α ω)
  · intro ω t ht
    apply ODE.hasDerivWithinAt_picard_Icc t₀.property (hPL ω).continuousOn_uncurry
      (α ω).continuous_compProj.continuousOn
      (fun s hs => (α ω).compProj_mem_closedBall (t := s) (hPL ω).mul_max_le) x₀ ht
      |>.congr_of_mem _ ht
    intro s hs
    change (α ω).compProj s = ODE.picard (fun t x => V t ω x) t₀ x₀ (α ω).compProj s
    rw [ODE.FunSpace.compProj_of_mem hs]
    nth_rw 1 [← hα ω]
    exact ODE.FunSpace.next_apply (hPL ω) hx (α ω)

  · intro t ω
    exact hconv (projIcc 0 (T : ℝ) T.coe_nonneg t) ω

lemma picardApprox_congr_on
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V W : ℝ → Ω → E → E} (x₀ : E) (t : ℝ)
    (hVW : ∀ s ∈ Icc 0 t, ∀ ω x, V s ω x = W s ω x) (n : ℕ) :
    ∀ s ∈ Icc 0 t, ∀ ω, picardApprox V x₀ n s ω = picardApprox W x₀ n s ω := by
  induction n with
  | zero => intro s hs ω; rfl
  | succ n ih =>
    intro s hs ω
    dsimp only [picardApprox]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    have hut : u ∈ Icc 0 t := ⟨hu.1.le, hu.2.trans hs.2⟩
    dsimp only
    rw [ih u hut ω, hVW u hut]

lemma measurable_driver_frozen
    {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ)
    (hU : Measurable (fun q : ℝ≥0 × Ω => U q.1 q.2))
    (hc : ∀ ω, Continuous (fun t : ℝ≥0 => U t ω)) (t : ℝ≥0) :
    @Measurable (ℝ × Ω) ℝ
      ((borel ℝ).prod (Filtration.natural U
        (fun t => (hU.comp (measurable_prodMk_left (x := t))).stronglyMeasurable) t))
      (borel ℝ) (fun q => U (min q.1.toNNReal t) q.2) := by
  let hm := fun t => (hU.comp (measurable_prodMk_left (x := t))).stronglyMeasurable
  have hp := (Filtration.stronglyAdapted_natural hm).isStronglyProgressive_of_continuous hc
  have hpt := (hp t).measurable
  let : MeasurableSpace Ω := Filtration.natural U hm t
  have htime : Measurable (fun s : ℝ => (⟨min s.toNNReal t, by change min s.toNNReal t ≤ t; exact min_le_right s.toNNReal t⟩ : Iic t)) :=
    ((continuous_real_toNNReal.min continuous_const).measurable).subtype_mk
  exact hpt.comp ((htime.comp measurable_fst).prodMk measurable_snd)

 

theorem clipped_log_loewner_adapted_solution
    {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ)
    (hU : Measurable (fun q : ℝ≥0 × Ω => U q.1 q.2))
    (hc : ∀ ω, Continuous (fun t : ℝ≥0 => U t ω))
    (lo hi : ℝ) (hle : lo ≤ hi) (q₀ : ℂ × ℝ) (T : ℝ≥0) :
    ∃ (L : ℝ≥0) (Q : ℝ → Ω → ℂ × ℝ),
      Measurable (fun q : ℝ × Ω => Q q.1 q.2) ∧
      (∀ ω, LipschitzWith L (fun t => Q t ω)) ∧
      (∀ ω, Q 0 ω = q₀) ∧
      (∀ ω t, t ∈ Icc 0 (T : ℝ) →
        HasDerivWithinAt (fun s => Q s ω)
          (clippedLogLoewnerField lo hi hle (U t.toNNReal ω) (Q t ω))
          (Icc 0 (T : ℝ)) t) ∧
      Adapted (Filtration.natural U (fun t => (hU.comp (measurable_prodMk_left (x := t))).stronglyMeasurable))
        (fun t : ℝ≥0 => Q t) := by
  obtain ⟨L, K, hbound, hlip⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) (q : ℂ × ℝ) := clippedLogLoewnerField lo hi hle (U t.toNNReal ω) q
  have hF := continuous_clippedLogLoewnerField lo hi hle
  have hUr : Measurable (fun q : ℝ × Ω => U q.1.toNNReal q.2) :=
    hU.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun q : (ℝ × Ω) × (ℂ × ℝ) => V q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun q : (ℝ × Ω) × (ℂ × ℝ) => (U q.1.1.toNNReal q.1.2, q.2)))
    exact hF.measurable.comp ((hUr.comp measurable_fst).prodMk measurable_snd)
  have hcont (ω : Ω) (q : ℂ × ℝ) : Continuous (fun t : ℝ => V t ω q) := by
    change Continuous ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun t : ℝ => (U t.toNNReal ω, q)))
    exact hF.comp (((hc ω).comp continuous_real_toNNReal).prodMk continuous_const)
  obtain ⟨Q, hQm, hQl, hQ0, hQd, hQconv⟩ :=
    exists_measurable_bounded_ode_picard V q₀ T L K hm hcont
      (fun ω t => hlip (U t.toNNReal ω)) (fun ω t q => hbound (U t.toNNReal ω) q)
  refine ⟨L, Q, hQm, hQl, hQ0, hQd, ?_⟩
  intro t
  have hUfrozen := measurable_driver_frozen U hU hc t
  let m := Filtration.natural U (fun t => (hU.comp measurable_prodMk_left).stronglyMeasurable) t
  let : MeasurableSpace Ω := m
  let W (s : ℝ) (ω : Ω) (q : ℂ × ℝ) :=
    clippedLogLoewnerField lo hi hle (U (min s.toNNReal t) ω) q
  have hW : Measurable (fun q : (ℝ × Ω) × (ℂ × ℝ) => W q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun q : (ℝ × Ω) × (ℂ × ℝ) => (U (min q.1.1.toNNReal t) q.1.2, q.2)))
    exact hF.measurable.comp ((hUfrozen.comp measurable_fst).prodMk measurable_snd)
  let c : ℝ := projIcc 0 (T : ℝ) T.coe_nonneg (t : ℝ)
  have hc0 : 0 ≤ c := (projIcc 0 (T : ℝ) T.coe_nonneg (t : ℝ)).property.1
  have hct : c ≤ (t : ℝ) := by
    dsimp [c]
    simp only [projIcc]
    exact max_le t.coe_nonneg (min_le_right _ _)
  have heq (n : ℕ) (ω : Ω) : picardApprox W q₀ n c ω = picardApprox V q₀ n c ω := by
    apply picardApprox_congr_on q₀ c _ n c ⟨hc0, le_rfl⟩ ω
    intro s hs ω q
    have hh : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr (hs.2.trans hct)
    simp only [W, V, min_eq_left hh]
  apply measurable_of_tendsto_metrizable (f := fun n ω => picardApprox W q₀ n c ω)
  · intro n
    exact (picardApprox_measurable W q₀ hW n).comp measurable_prodMk_left
  · apply tendsto_pi_nhds.mpr
    intro ω
    simpa only [heq] using hQconv t ω

 

theorem exists_measurable_global_bounded_ode_picard
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (V : ℝ → Ω → E → E) (x₀ : E) (L K : ℝ≥0)
    (hV : Measurable (fun q : (ℝ × Ω) × E => V q.1.1 q.1.2 q.2))
    (hc : ∀ ω x, Continuous (fun t : ℝ => V t ω x))
    (hl : ∀ ω t, LipschitzWith K (V t ω))
    (hb : ∀ ω t x, ‖V t ω x‖ ≤ L) :
    ∃ X : ℝ → Ω → E,
      Measurable (fun q : ℝ × Ω => X q.1 q.2) ∧
      (∀ ω, LipschitzWith L (fun t => X t ω)) ∧
      (∀ ω, X 0 ω = x₀) ∧
      (∀ ω t, 0 ≤ t →
        HasDerivWithinAt (fun u => X u ω) (V t ω (X t ω)) (Ici 0) t) ∧
      (∀ t ω, Tendsto (fun n => picardApprox V x₀ n (max 0 t) ω) atTop (𝓝 (X t ω))) := by
  classical
  have hex (t : ℝ) (ω : Ω) : ∃ v : E,
      Tendsto (fun n => picardApprox V x₀ n (max 0 t) ω) atTop (𝓝 v) := by
    let T : ℝ≥0 := ⟨max 0 t, le_max_left _ _⟩
    obtain ⟨X, _, _, _, _, hconv⟩ := exists_measurable_bounded_ode_picard V x₀ T L K hV hc hl hb
    refine ⟨X t ω, ?_⟩
    have hc0 := hconv t ω
    change Tendsto (fun n => picardApprox V x₀ n (max 0 (min (max 0 t) t)) ω) atTop (𝓝 (X t ω)) at hc0
    simpa only [min_eq_right (le_max_right (0 : ℝ) t)] using hc0
  let Q (t : ℝ) (ω : Ω) := limUnder atTop (fun n => picardApprox V x₀ n (max 0 t) ω)
  have hlim (t : ℝ) (ω : Ω) :
      Tendsto (fun n => picardApprox V x₀ n (max 0 t) ω) atTop (𝓝 (Q t ω)) :=
    tendsto_nhds_limUnder (hex t ω)
  have hmatch (T : ℝ≥0) (X : ℝ → Ω → E)
      (hconv : ∀ t ω, Tendsto (fun n => picardApprox V x₀ n
        (projIcc 0 (T : ℝ) T.coe_nonneg t) ω) atTop (𝓝 (X t ω)))
      (t : ℝ) (ht : t ≤ T) (ω : Ω) : Q t ω = X t ω := by
    apply tendsto_nhds_unique (hlim t ω)
    simpa only [projIcc, min_eq_right ht] using hconv t ω
  refine ⟨Q, ?_, ?_, ?_, ?_, hlim⟩
  · apply measurable_of_tendsto_metrizable (f := fun n (q : ℝ × Ω) => picardApprox V x₀ n (max 0 q.1) q.2)
    · intro n
      exact (picardApprox_measurable V x₀ hV n).comp
        ((measurable_const.max measurable_fst).prodMk measurable_snd)
    · exact tendsto_pi_nhds.mpr fun q => hlim q.1 q.2
  · intro ω
    apply LipschitzWith.of_dist_le_mul
    intro s t
    let T : ℝ≥0 := ⟨max (max 0 s) t, (le_max_left 0 s).trans (le_max_left _ _)⟩
    obtain ⟨X, _, hXl, _, _, hconv⟩ := exists_measurable_bounded_ode_picard V x₀ T L K hV hc hl hb
    rw [hmatch T X hconv s ((le_max_right 0 s).trans (le_max_left _ _)) ω,
      hmatch T X hconv t (le_max_right _ _) ω]
    exact (hXl ω).dist_le_mul s t
  · intro ω
    obtain ⟨X, _, _, hX0, _, hconv⟩ := exists_measurable_bounded_ode_picard V x₀ 0 L K hV hc hl hb
    rw [hmatch 0 X hconv 0 le_rfl ω, hX0 ω]
  · intro ω t ht
    let T : ℝ≥0 := ⟨t + 1, by linarith⟩
    have hlt : t < (T : ℝ) := by change t < t + 1; linarith
    obtain ⟨X, _, _, _, hXd, hconv⟩ := exists_measurable_bounded_ode_picard V x₀ T L K hV hc hl hb
    have heq : (fun s => Q s ω) =ᶠ[𝓝 t] (fun s => X s ω) := by
      filter_upwards [Iic_mem_nhds hlt] with s hs
      exact hmatch T X hconv s hs ω
    have hd := hXd ω t ⟨ht, hlt.le⟩
    have hsets : Icc 0 (T : ℝ) =ᶠ[𝓝 t] Ici 0 := by
      filter_upwards [Iic_mem_nhds hlt] with s hs
      change (0 ≤ s ∧ s ≤ (T : ℝ)) = (0 ≤ s)
      exact propext ⟨And.left, fun h => ⟨h, hs⟩⟩
    have hd' := hd.congr_set hsets
    rw [← hmatch T X hconv t hlt.le ω] at hd'
    exact hd'.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) (heq.eq_of_nhds)

theorem clipped_log_loewner_global_adapted_solution
    {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ)
    (hU : Measurable (fun q : ℝ≥0 × Ω => U q.1 q.2))
    (hc : ∀ ω, Continuous (fun t : ℝ≥0 => U t ω))
    (lo hi : ℝ) (hle : lo ≤ hi) (q₀ : ℂ × ℝ) :
    ∃ (L : ℝ≥0) (Q : ℝ → Ω → ℂ × ℝ),
      Measurable (fun q : ℝ × Ω => Q q.1 q.2) ∧
      (∀ ω, LipschitzWith L (fun t => Q t ω)) ∧
      (∀ ω, Q 0 ω = q₀) ∧
      (∀ ω t, 0 ≤ t →
        HasDerivWithinAt (fun s => Q s ω)
          (clippedLogLoewnerField lo hi hle (U t.toNNReal ω) (Q t ω))
          (Ici 0) t) ∧
      Adapted (Filtration.natural U (fun t => (hU.comp (measurable_prodMk_left (x := t))).stronglyMeasurable))
        (fun t : ℝ≥0 => Q t) := by
  obtain ⟨L, K, hbound, hlip⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) (q : ℂ × ℝ) := clippedLogLoewnerField lo hi hle (U t.toNNReal ω) q
  have hF := continuous_clippedLogLoewnerField lo hi hle
  have hUr : Measurable (fun q : ℝ × Ω => U q.1.toNNReal q.2) :=
    hU.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun q : (ℝ × Ω) × (ℂ × ℝ) => V q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun q : (ℝ × Ω) × (ℂ × ℝ) => (U q.1.1.toNNReal q.1.2, q.2)))
    exact hF.measurable.comp ((hUr.comp measurable_fst).prodMk measurable_snd)
  have hcont (ω : Ω) (q : ℂ × ℝ) : Continuous (fun t : ℝ => V t ω q) := by
    change Continuous ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun t : ℝ => (U t.toNNReal ω, q)))
    exact hF.comp (((hc ω).comp continuous_real_toNNReal).prodMk continuous_const)
  obtain ⟨Q, hQm, hQl, hQ0, hQd, hQconv⟩ :=
    exists_measurable_global_bounded_ode_picard V q₀ L K hm hcont
      (fun ω t => hlip (U t.toNNReal ω)) (fun ω t q => hbound (U t.toNNReal ω) q)
  refine ⟨L, Q, hQm, hQl, hQ0, hQd, ?_⟩
  intro t
  have hUfrozen := measurable_driver_frozen U hU hc t
  let m := Filtration.natural U (fun t => (hU.comp measurable_prodMk_left).stronglyMeasurable) t
  let : MeasurableSpace Ω := m
  let W (s : ℝ) (ω : Ω) (q : ℂ × ℝ) :=
    clippedLogLoewnerField lo hi hle (U (min s.toNNReal t) ω) q
  have hW : Measurable (fun q : (ℝ × Ω) × (ℂ × ℝ) => W q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun q : (ℝ × Ω) × (ℂ × ℝ) => (U (min q.1.1.toNNReal t) q.1.2, q.2)))
    exact hF.measurable.comp ((hUfrozen.comp measurable_fst).prodMk measurable_snd)
  have heq (n : ℕ) (ω : Ω) : picardApprox W q₀ n (t : ℝ) ω = picardApprox V q₀ n (t : ℝ) ω := by
    apply picardApprox_congr_on q₀ (t : ℝ) _ n (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩ ω
    intro s hs ω q
    have hh : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    simp only [W, V, min_eq_left hh]
  apply measurable_of_tendsto_metrizable (f := fun n ω => picardApprox W q₀ n (t : ℝ) ω)
  · intro n
    exact (picardApprox_measurable W q₀ hW n).comp measurable_prodMk_left
  · apply tendsto_pi_nhds.mpr
    intro ω
    simpa only [heq, max_eq_right t.coe_nonneg] using hQconv t ω

noncomputable def spatialPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E × ℝ → ℝ) : ℕ → E × ℝ → ℝ
  | 0 => φ
  | n + 1 => fun p => fderiv ℝ (spatialPartial φ n) p (0, 1)

lemma spatialPartial_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialPartial φ n) := by
  induction n with
  | zero => exact hφ
  | succ n ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

lemma spatialPartial_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E × ℝ → ℝ) (hφ : HasCompactSupport φ) (n : ℕ) :
    HasCompactSupport (spatialPartial φ n) := by
  induction n with
  | zero => exact hφ
  | succ n ih =>
    exact (ih.fderiv ℝ).comp_left (g := fun D : (E × ℝ) →L[ℝ] ℝ => D (0, 1)) (by simp)

lemma spatialPartial_eq_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (n : ℕ) (q : E) (x : ℝ) :
    spatialPartial φ n (q, x) = iteratedDeriv n (fun y => φ (q, y)) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hd : HasDerivAt (fun y => spatialPartial φ n (q, y))
        (fderiv ℝ (spatialPartial φ n) (q, x) (0, 1)) x := by
      exact (((spatialPartial_smooth φ hφ n).differentiable (by simp)) (q, x)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_const x q).prodMk (hasDerivAt_id x))
    simpa only [spatialPartial, iteratedDeriv_succ, ← funext ih] using hd.deriv.symm

lemma compact_smooth_bounded_lipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : E → F) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∃ C : ℝ≥0, (∀ p, ‖φ p‖ ≤ C) ∧ LipschitzWith C φ := by
  obtain ⟨A, hA⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨D, hD⟩ := (hφ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hφc.fderiv ℝ)
  let C := Real.toNNReal (max A D)
  have hAC : A ≤ (C : ℝ) := (le_max_left _ _).trans (Real.le_coe_toNNReal _)
  have hDC : D ≤ (C : ℝ) := (le_max_right _ _).trans (Real.le_coe_toNNReal _)
  refine ⟨C, fun p => (hA p).trans hAC, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hφ.differentiable (by simp))
  intro p
  exact_mod_cast (hD p).trans hDC

 

theorem compact_state_smooth_brownian_field
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (Q V : ℝ → Ω → E) (L : ℝ≥0)
    (hQm : Measurable (fun p : ℝ × Ω => Q p.1 p.2))
    (hQa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t : ℝ≥0 => Q t))
    (hQl : ∀ ω, LipschitzWith L (fun t => Q t ω))
    (hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2))
    (hVb : ∀ t ω, ‖V t ω‖ ≤ L)
    (hQd : ∀ t ω, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω) (V t ω) (Ici 0) t)
    (φ : E × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∃ K : ℝ≥0, SmoothTimeBrownianField B hm K
      (fun t ω x => φ (Q t ω, x))
      (fun t ω x => fderiv ℝ φ (Q t ω, x) (V t ω, 0)) := by

  classical
  have hr (j : ℕ) := compact_smooth_bounded_lipschitz (spatialPartial φ j)
    (spatialPartial_smooth φ hφ j) (spatialPartial_compact φ hφc j)
  choose C hCb hCl using hr
  let C₀ : ℝ≥0 := ∑ j ∈ Finset.range 4, C j
  have hC (j : ℕ) (hj : j ≤ 3) : C j ≤ C₀ :=
    Finset.single_le_sum (fun i _ => (zero_le : (0 : ℝ≥0) ≤ C i)) (Finset.mem_range.mpr (by omega))
  have hCb' (j : ℕ) (hj : j ≤ 3) (p : E × ℝ) : |spatialPartial φ j p| ≤ C₀ := by
    have hh := (hCb j p).trans (show (C j : ℝ) ≤ C₀ by exact_mod_cast hC j hj)
    simpa only [Real.norm_eq_abs] using hh
  have hC2 : LipschitzWith C₀ (spatialPartial φ 2) := (hCl 2).weaken (hC 2 (by decide))
  obtain ⟨D, hDb, hDl⟩ := compact_smooth_bounded_lipschitz (fderiv ℝ φ)
    (hφ.fderiv_right (by simp)) (hφc.fderiv ℝ)
  let K : ℝ≥0 := (C₀ + D) * (L + 1)
  have hKC : (C₀ : ℝ) ≤ (K : ℝ) := by
    change (C₀ : ℝ) ≤ ((C₀ : ℝ) + D) * ((L : ℝ) + 1)
    nlinarith [C₀.coe_nonneg, D.coe_nonneg, L.coe_nonneg]
  have hKDL : (D : ℝ) * L ≤ (K : ℝ) := by
    change (D : ℝ) * L ≤ ((C₀ : ℝ) + D) * ((L : ℝ) + 1)
    nlinarith [C₀.coe_nonneg, D.coe_nonneg, L.coe_nonneg]
  have hKCL : (C₀ : ℝ) * ((L : ℝ) + 1) ≤ (K : ℝ) := by
    change (C₀ : ℝ) * ((L : ℝ) + 1) ≤ ((C₀ : ℝ) + D) * ((L : ℝ) + 1)
    nlinarith [C₀.coe_nonneg, D.coe_nonneg, L.coe_nonneg]
  have hQn : Measurable (fun p : ℝ≥0 × Ω => Q p.1 p.2) :=
    hQm.comp ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have hVn : Measurable (fun p : ℝ≥0 × Ω => V p.1 p.2) :=
    hVm.comp ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have happ : Continuous (fun p : (E × ℝ) × (E × ℝ) => fderiv ℝ φ p.1 p.2) :=
    ((hφ.continuous_fderiv (by simp)).comp continuous_fst).clm_apply continuous_snd
  have hameas : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => fderiv ℝ φ (Q p.1.1 p.1.2, p.2) (V p.1.1 p.1.2, 0)) :=
    happ.measurable.comp (((hQn.comp measurable_fst).prodMk measurable_snd).prodMk
      ((hVn.comp measurable_fst).prodMk measurable_const))
  have habound (t : ℝ≥0) (ω : Ω) (x : ℝ) :
      |fderiv ℝ φ (Q t ω, x) (V t ω, 0)| ≤ K := by
    calc
      _ = ‖fderiv ℝ φ (Q t ω, x) (V t ω, 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ φ (Q t ω, x)‖ * ‖(V t ω, (0 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ φ (Q t ω, x)‖ * ‖V t ω‖ := by simp
      _ ≤ (D : ℝ) * L := mul_le_mul (hDb _) (hVb t ω) (norm_nonneg _) D.coe_nonneg
      _ ≤ K := hKDL
  have haLip (t : ℝ≥0) (ω : Ω) (x y : ℝ) :
      |fderiv ℝ φ (Q t ω, x) (V t ω, 0) - fderiv ℝ φ (Q t ω, y) (V t ω, 0)| ≤
        (K : ℝ) * |x - y| := by
    have hd : ‖fderiv ℝ φ (Q t ω, x) - fderiv ℝ φ (Q t ω, y)‖ ≤ (D : ℝ) * |x - y| := by
      simpa [dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using hDl.dist_le_mul (Q t ω, x) (Q t ω, y)
    calc
      _ = ‖(fderiv ℝ φ (Q t ω, x) - fderiv ℝ φ (Q t ω, y)) (V t ω, 0)‖ := by
        rw [sub_apply, Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ φ (Q t ω, x) - fderiv ℝ φ (Q t ω, y)‖ * ‖(V t ω, (0 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ φ (Q t ω, x) - fderiv ℝ φ (Q t ω, y)‖ * ‖V t ω‖ := by simp
      _ ≤ ((D : ℝ) * |x - y|) * L := mul_le_mul hd (hVb t ω) (norm_nonneg _) (by positivity)
      _ = ((D : ℝ) * L) * |x - y| := by ring
      _ ≤ (K : ℝ) * |x - y| := mul_le_mul_of_nonneg_right hKDL (abs_nonneg _)
  refine ⟨K, ⟨?_, ?_, ?_, hameas, ?_, habound, haLip, ?_, ?_⟩⟩
  · intro t ω
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => φ (Q t ω, x)) :=
      hφ.comp (contDiff_const.prodMk contDiff_id)
    exact hc.of_le (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  · intro t j hj
    simp_rw [← spatialPartial_eq_iteratedDeriv φ hφ]
    exact (spatialPartial_smooth φ hφ j).continuous.measurable.comp
      (((hQa t).comp measurable_fst).prodMk measurable_snd)
  · intro j hj
    simp_rw [← spatialPartial_eq_iteratedDeriv φ hφ]
    exact (spatialPartial_smooth φ hφ j).continuous.measurable.comp
      ((hQn.comp measurable_fst).prodMk measurable_snd)
  · intro t ω x j hj
    rw [← spatialPartial_eq_iteratedDeriv φ hφ]
    exact (hCb' j hj _).trans hKC
  · intro s t ω x y
    rw [← spatialPartial_eq_iteratedDeriv φ hφ, ← spatialPartial_eq_iteratedDeriv φ hφ]
    have hQdist := (hQl ω).dist_le_mul (t : ℝ) (s : ℝ)
    rw [Real.dist_eq] at hQdist
    calc
      _ = dist (spatialPartial φ 2 (Q t ω, x)) (spatialPartial φ 2 (Q s ω, y)) := (Real.dist_eq _ _).symm
      _ ≤ (C₀ : ℝ) * dist (Q t ω, x) (Q s ω, y) := hC2.dist_le_mul _ _
      _ ≤ (C₀ : ℝ) * (dist (Q t ω) (Q s ω) + |x - y|) := by
        apply mul_le_mul_of_nonneg_left _ C₀.coe_nonneg
        rw [Prod.dist_eq, Real.dist_eq]
        exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left dist_nonneg)
      _ ≤ (C₀ : ℝ) * ((L : ℝ) * |(t : ℝ) - s| + |x - y|) :=
        mul_le_mul_of_nonneg_left (show dist (Q (t : ℝ) ω) (Q (s : ℝ) ω) + |x - y| ≤
          (L : ℝ) * |(t : ℝ) - s| + |x - y| by linarith) C₀.coe_nonneg
      _ ≤ ((C₀ : ℝ) * ((L : ℝ) + 1)) * (|(t : ℝ) - s| + |x - y|) := by
        nlinarith [mul_nonneg C₀.coe_nonneg (abs_nonneg ((t : ℝ) - s)),
          mul_nonneg (mul_nonneg C₀.coe_nonneg L.coe_nonneg) (abs_nonneg (x - y))]
      _ ≤ (K : ℝ) * (|(t : ℝ) - s| + |x - y|) :=
        mul_le_mul_of_nonneg_right hKCL (by positivity)
  · intro s t hst ω x
    have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    symm
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun u : ℝ => φ (Q u ω, x))
      (f' := fun u : ℝ => fderiv ℝ φ (Q u.toNNReal ω, x) (V u.toNNReal ω, 0)) hst'
    · exact (hφ.continuous.comp ((hQl ω).continuous.prodMk continuous_const)).continuousOn
    · intro u hu
      have hu0 : 0 < u := lt_of_le_of_lt s.coe_nonneg hu.1
      have hd := (hQd u ω hu0.le).hasDerivAt (Ici_mem_nhds hu0)
      have hpair := hd.prodMk (hasDerivAt_const u x)
      have hc := ((hφ.differentiable (by simp)) (Q u ω, x)).hasFDerivAt.comp_hasDerivAt u hpair
      simpa only [Function.comp_def, Real.coe_toNNReal _ hu0.le] using hc
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst']
      have hmA : Measurable (fun u : ℝ => fderiv ℝ φ (Q u.toNNReal ω, x) (V u.toNNReal ω, 0)) :=
        hameas.comp ((continuous_real_toNNReal.measurable.prodMk measurable_const).prodMk measurable_const)
      apply Integrable.of_bound hmA.aestronglyMeasurable (K : ℝ)
      exact Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using habound u.toNNReal ω x

noncomputable def dimension (κ : ℝ) : ℝ := 1 + κ / 8
noncomputable def codimension (κ : ℝ) : ℝ := ((2 : ℕ) : ℝ) - dimension κ
noncomputable def greenExponent (κ : ℝ) : ℝ := 8 / κ - 1

 

noncomputable def greenLogNormSq (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  (q.1.re - Real.sqrt κ * x) ^ 2 + Real.exp (2 * q.1.im)
noncomputable def greenLogDensity (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  Real.exp (-codimension κ * Real.log 2 + codimension κ * q.2 +
    (greenExponent κ - codimension κ) * q.1.im -
      (greenExponent κ / 2) * Real.log (greenLogNormSq κ q x))
noncomputable def physicalLogLoewnerField (u : ℝ) (q : ℂ × ℝ) : ℂ × ℝ :=
  let Z := ((q.1.re - u : ℝ) : ℂ) + (Real.exp q.1.im : ℂ) * Complex.I
  let v := Z⁻¹
  (((2 * v.re : ℝ) : ℂ) + ((-2 * Complex.normSq v : ℝ) : ℂ) * Complex.I,
    (-2 * v ^ 2).re)

lemma greenLogNormSq_pos (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    0 < greenLogNormSq κ q x :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (Real.exp_pos _)

lemma greenLogDensity_contDiff (κ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => greenLogDensity κ p.1 p.2) := by
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => p.1.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst.fst
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => p.1.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst.fst
  have hN : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => greenLogNormSq κ p.1 p.2) := by
    exact ((hre.sub (contDiff_const.mul contDiff_snd)).pow 2).add
      ((contDiff_const.mul him).exp)
  have hlog := hN.log (fun p => (greenLogNormSq_pos κ p.1 p.2).ne')
  unfold greenLogDensity
  apply ContDiff.exp
  exact (((contDiff_const.add (contDiff_const.mul contDiff_fst.snd)).add
    (contDiff_const.mul him)).sub (contDiff_const.mul hlog))

lemma greenLogDensity_spatial_derivative (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    HasDerivAt (greenLogDensity κ q)
      (greenLogDensity κ q x * (greenExponent κ * Real.sqrt κ * (q.1.re - Real.sqrt κ * x) /
        greenLogNormSq κ q x)) x := by
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2 * (q.1.re - Real.sqrt κ * x) * (-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2 * q.1.im)) using 1 <;> try rfl
    simp
  have hlog := hN.log (greenLogNormSq_pos κ q x).ne'
  have hd := ((hasDerivAt_const x (-codimension κ * Real.log 2 + codimension κ * q.2 +
    (greenExponent κ - codimension κ) * q.1.im)).sub
      (hlog.const_mul (greenExponent κ / 2))).exp
  convert hd using 1 <;> try rfl
  dsimp only [greenLogDensity, Pi.sub_apply, Pi.mul_apply, Function.comp_def]
  ring

lemma greenLogDensity_spatial_second (κ : ℝ) (hκ : 0 ≤ κ) (q : ℂ × ℝ) (x : ℝ) :
    iteratedDeriv 2 (greenLogDensity κ q) x =
      greenLogDensity κ q x * κ * greenExponent κ *
        ((greenExponent κ + 1) * (q.1.re - Real.sqrt κ * x) ^ 2 - Real.exp (2 * q.1.im)) /
        (greenLogNormSq κ q x) ^ 2 := by
  have hd : deriv (greenLogDensity κ q) = fun x =>
      greenLogDensity κ q x * (greenExponent κ * Real.sqrt κ * (q.1.re - Real.sqrt κ * x) /
        greenLogNormSq κ q x) := funext fun x => (greenLogDensity_spatial_derivative κ q x).deriv
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2 * (q.1.re - Real.sqrt κ * x) * (-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2 * q.1.im)) using 1 <;> try rfl
    simp
  have hcoef := (hX.const_mul (greenExponent κ * Real.sqrt κ)).div hN
    (greenLogNormSq_pos κ q x).ne'
  have hsecond := (greenLogDensity_spatial_derivative κ q x).mul hcoef
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
  dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, id_eq] at hsecond
  change HasDerivAt (fun y => greenLogDensity κ q y *
    (greenExponent κ * Real.sqrt κ * (q.1.re - Real.sqrt κ * y) / greenLogNormSq κ q y)) _ x at hsecond
  rw [hsecond.deriv]
  have hn := (greenLogNormSq_pos κ q x).ne'
  dsimp only [greenLogNormSq]
  generalize greenLogDensity κ q x = f
  generalize greenExponent κ = a
  generalize q.1.re - Real.sqrt κ * x = X
  generalize Real.exp (2 * q.1.im) = Y
  have hs := Real.sq_sqrt hκ
  generalize Real.sqrt κ = r at *
  rw [← hs]
  field_simp
  ring

lemma greenLogDensity_directional (κ : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun r : ℂ × ℝ => greenLogDensity κ r x) q) v =
      greenLogDensity κ q x * (codimension κ * v.2 +
        (greenExponent κ - codimension κ) * v.1.im - (greenExponent κ / 2) *
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
  have hcalc := (((hj.const_mul (codimension κ)).const_add (-codimension κ * Real.log 2)).add
    (hzim.const_mul (greenExponent κ - codimension κ))).sub
      (hlog.const_mul (greenExponent κ / 2))
  have hline : HasDerivAt (fun t : ℝ => greenLogDensity κ (q + t • v) x)
      (greenLogDensity κ q x * (codimension κ * v.2 +
        (greenExponent κ - codimension κ) * v.1.im - (greenExponent κ / 2) *
          ((2 * (q.1.re - Real.sqrt κ * x) * v.1.re +
            2 * Real.exp (2 * q.1.im) * v.1.im) / greenLogNormSq κ q x))) 0 := by
    convert hcalc.exp using 1 <;> try rfl
    simp only [Pi.sub_apply, Pi.add_apply, zero_smul, add_zero]
    simp only [greenLogDensity]
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => greenLogDensity κ r x) :=
    (greenLogDensity_contDiff κ).comp (contDiff_id.prodMk contDiff_const)
  have haff : HasDerivAt (fun t : ℝ => q + t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hfd : HasFDerivAt (fun r : ℂ × ℝ => greenLogDensity κ r x)
      (fderiv ℝ (fun r : ℂ × ℝ => greenLogDensity κ r x) q) (q + (0 : ℝ) • v) := by
    simpa using ((hcd.differentiable (by simp)) q).hasFDerivAt
  have hchain := hfd.comp_hasDerivAt 0 haff
  simpa only [Function.comp_def] using hchain.unique hline

lemma physicalLogLoewnerField_components (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    (physicalLogLoewnerField (Real.sqrt κ * x) q).1.re =
      2 * (q.1.re - Real.sqrt κ * x) / greenLogNormSq κ q x ∧
    (physicalLogLoewnerField (Real.sqrt κ * x) q).1.im =
      -2 / greenLogNormSq κ q x ∧
    (physicalLogLoewnerField (Real.sqrt κ * x) q).2 =
      -2 * ((q.1.re - Real.sqrt κ * x) ^ 2 - Real.exp (2 * q.1.im)) /
        (greenLogNormSq κ q x) ^ 2 := by
  let Z : ℂ := ((q.1.re - Real.sqrt κ * x : ℝ) : ℂ) + (Real.exp q.1.im : ℂ) * Complex.I
  have hre : Z.re = q.1.re - Real.sqrt κ * x := by simp [Z]
  have him : Z.im = Real.exp q.1.im := by
    simp only [Z, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero]
  have he : Real.exp q.1.im * Real.exp q.1.im = Real.exp (2 * q.1.im) := by
    rw [← Real.exp_add]; congr 1; ring
  have hn : Complex.normSq Z = greenLogNormSq κ q x := by
    rw [Complex.normSq_apply, hre, him, he]
    simp only [greenLogNormSq, pow_two]
  change (((2 * Z⁻¹.re : ℝ) : ℂ) + ((-2 * Complex.normSq Z⁻¹ : ℝ) : ℂ) * Complex.I).re = _ ∧
    (((2 * Z⁻¹.re : ℝ) : ℂ) + ((-2 * Complex.normSq Z⁻¹ : ℝ) : ℂ) * Complex.I).im = _ ∧
    (-2 * Z⁻¹ ^ 2).re = _
  constructor
  · simp [Complex.inv_re, hre, hn, mul_div_assoc]
  constructor
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero,
      Complex.normSq_inv, hn, div_eq_mul_inv]
  · simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.re_ofNat, Complex.im_ofNat, neg_zero, zero_mul, sub_zero,
      Complex.inv_re, Complex.inv_im, hre, him, hn]
    have he2 : Real.exp q.1.im ^ 2 = Real.exp (2 * q.1.im) := by simpa only [pow_two] using he
    rw [← he2]
    field_simp

 
theorem green_physical_generator_zero (κ : ℝ) (hκ : 0 < κ) (_hκ8 : κ < 8)
    (q : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun r : ℂ × ℝ => greenLogDensity κ r x) q)
      (physicalLogLoewnerField (Real.sqrt κ * x) q) +
      (1 / 2 : ℝ) * iteratedDeriv 2 (greenLogDensity κ q) x = 0 := by
  rw [greenLogDensity_directional, greenLogDensity_spatial_second κ hκ.le]
  obtain ⟨hr, hi, hj⟩ := physicalLogLoewnerField_components κ q x
  rw [hr, hi, hj]
  have ha : κ * (greenExponent κ + 1) = 8 := by
    simp only [greenExponent, sub_add_cancel]
    field_simp
  have hp : κ * greenExponent κ = 8 * codimension κ := by
    dsimp only [greenExponent, codimension, dimension]
    field_simp
    ring
  have hc1 : -4 * greenExponent κ + κ * greenExponent κ * (greenExponent κ + 1) / 2 = 0 := by
    linear_combination (greenExponent κ / 2) * ha
  have hc2 : 4 * codimension κ - κ * greenExponent κ / 2 = 0 := by
    linarith
  calc
    _ = greenLogDensity κ q x *
      ((-4 * greenExponent κ + κ * greenExponent κ * (greenExponent κ + 1) / 2) *
        (q.1.re - Real.sqrt κ * x) ^ 2 +
        (4 * codimension κ - κ * greenExponent κ / 2) * Real.exp (2 * q.1.im)) /
      (greenLogNormSq κ q x) ^ 2 := by
        have hn := (greenLogNormSq_pos κ q x).ne'
        field_simp
        dsimp only [greenLogNormSq]
        ring
    _ = 0 := by rw [hc1, hc2]; ring

lemma greenLogDensity_pair_directional (κ : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun p : (ℂ × ℝ) × ℝ => greenLogDensity κ p.1 p.2) (q, x) (v, 0) =
      fderiv ℝ (fun r : ℂ × ℝ => greenLogDensity κ r x) q v := by
  have hd := ((greenLogDensity_contDiff κ).differentiable (by simp)) (q, x)
  have hp := (hasFDerivAt_id (𝕜 := ℝ) q).prodMk (hasFDerivAt_const (𝕜 := ℝ) (E := ℂ × ℝ) x q)
  have hc := (hd.hasFDerivAt.comp q hp).fderiv
  have he := congrArg (fun D : (ℂ × ℝ) →L[ℝ] ℝ => D v) hc
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, id_eq, zero_apply] using he.symm

 

lemma exists_compact_green_field (κ R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : (ℂ × ℝ) × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ q x, ‖(q, x)‖ ≤ R → φ (q, x) = greenLogDensity κ q x) ∧
      (∀ q x, ‖(q, x)‖ ≤ R →
        fderiv ℝ φ (q, x) = fderiv ℝ (fun p : (ℂ × ℝ) × ℝ => greenLogDensity κ p.1 p.2) (q, x)) ∧
      (∀ q x, ‖(q, x)‖ ≤ R → iteratedDeriv 2 (fun y => φ (q, y)) x =
        iteratedDeriv 2 (greenLogDensity κ q) x) := by
  let b : ContDiffBump (0 : (ℂ × ℝ) × ℝ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let φ (p : (ℂ × ℝ) × ℝ) : ℝ := b p * greenLogDensity κ p.1 p.2
  have hnear (p : (ℂ × ℝ) × ℝ) (hp : ‖p‖ ≤ R) :
      φ =ᶠ[𝓝 p] (fun r : (ℂ × ℝ) × ℝ => greenLogDensity κ r.1 r.2) := by
    have hball : p ∈ Metric.ball (0 : (ℂ × ℝ) × ℝ) b.rIn := by
      simp only [Metric.mem_ball, dist_zero_right]
      change ‖p‖ < R + 1
      linarith
    filter_upwards [b.eventuallyEq_one_of_mem_ball hball] with r hr
    simp only [φ, hr, Pi.one_apply, one_mul]
  refine ⟨φ, b.contDiff.mul (greenLogDensity_contDiff κ), b.hasCompactSupport.mul_right,
    (fun q x h => (hnear (q, x) h).eq_of_nhds), ?_, ?_⟩
  · intro q x h
    exact (hnear (q, x) h).fderiv_eq
  · intro q x h
    have he := (hnear (q, x) h).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto x)
    exact he.iteratedDeriv_eq 2

lemma clippedLogLoewnerField_eq_physical (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ)
    (q : ℂ × ℝ) (hq : q.1.im ∈ Icc lo hi) :
    clippedLogLoewnerField lo hi hle u q = physicalLogLoewnerField u q := by
  simp only [clippedLogLoewnerField, clippedCenter, clippedHeight, projIcc_of_mem hle hq,
    physicalLogLoewnerField]

end SLEExactGauge
end

 
end

end OAI
