import Mathlib
import OAI.Analysis.RCDHeat.GeodesicMarginalCompact
import OAI.Analysis.RCDHeat.ProbabilityCutoff

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: ExistingAnalytic. -/




 

 
namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heatAt_exponential_square_integral_le (f : Lp ℝ 2 μ) (p : X)
    {r : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 ≤ t) :
    (∫x, Real.exp (a*dist p x)*heatAt μ hQ t f x^2 ∂μ) ≤
      Real.exp (a^2/2*t+a*r)*‖f‖^2 := by
  have hi := heatAt_exponential_square_integrable μ hQ f p hf ha ht
  have hb := heatAt_exponential_square_lintegral_le μ hQ f p hf ha ht
  rw [←ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

theorem heatAt_tail_square_integral_le (f : Lp ℝ 2 μ) (p : X)
    {r : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 ≤ t) (R : ℝ) :
    (∫x in {x | R ≤ dist p x}, heatAt μ hQ t f x^2 ∂μ) ≤
      Real.exp (-a*R) * (Real.exp (a^2/2*t+a*r)*‖f‖^2) := by
  let u := heatAt μ hQ t f
  let S : Set X := {x | R ≤ dist p x}
  have hS : MeasurableSet S := isClosed_le continuous_const (continuous_const.dist continuous_id) |>.measurableSet
  have hi := heatAt_exponential_square_integrable μ hQ f p hf ha ht
  have hs : Integrable (fun x => u x^2) μ := (Lp.memLp u).integrable_sq
  calc
    _ ≤ Real.exp (-a*R) * (∫x in S, Real.exp (a*dist p x)*u x^2 ∂μ) := by
      rw [←integral_const_mul]
      apply integral_mono_ae hs.integrableOn (hi.integrableOn.const_mul _)
      filter_upwards [ae_restrict_mem hS] with x hx
      have hd : a*R ≤ a*dist p x := mul_le_mul_of_nonneg_left hx ha
      have he : 1 ≤ Real.exp (-a*R)*Real.exp (a*dist p x) := by
        rw [←Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by linarith)
      nlinarith [sq_nonneg (u x)]
    _ ≤ Real.exp (-a*R) * (∫x, Real.exp (a*dist p x)*u x^2 ∂μ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact setIntegral_le_integral hi (Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_left (heatAt_exponential_square_integral_le μ hQ f p hf ha ht) (Real.exp_pos _).le



 
theorem exponential_weighted_moment_young (b c d z : ℝ) (k : ℕ) :
    |Real.exp (b*d)*d^k*z| ≤ Real.exp ((2*b+c)*d)*z^2+d^(2*k)*Real.exp (-c*d) := by
  have h := exponential_moment_young c d (Real.exp (b*d)*z) k
  have he : Real.exp (c*d)*(Real.exp (b*d)*z)^2 = Real.exp ((2*b+c)*d)*z^2 := by
    rw [mul_pow,←Real.exp_nat_mul,←mul_assoc,←Real.exp_add]
    congr 2
    ring
  rw [he] at h
  convert h using 1 ; congr 1 ; ring

theorem heatAt_weighted_moment_integrable (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) {r : ℝ} (hfs : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (k : ℕ) {b : ℝ} (hb : 0 ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => Real.exp (b*dist p x)*dist p x^k*heatAt μ hQ t f x) μ := by
  let c := B+(2*k:ℕ)+1
  have hc : 0 ≤ 2*b+c := by dsimp [c]; positivity
  have hi := (heatAt_exponential_square_integrable μ hQ f p hfs hc ht).add
    (integrable_dist_pow_mul_exp μ p hA hB hvol (2*k))
  apply hi.mono' _ (Eventually.of_forall fun x => exponential_weighted_moment_young b c (dist p x) (heatAt μ hQ t f x) k)
  exact (((Real.continuous_exp.comp (continuous_const.mul (continuous_const.dist continuous_id))).mul
    ((continuous_const.dist continuous_id).pow k)).aestronglyMeasurable).mul (Lp.aestronglyMeasurable _)

theorem heatAt_weighted_moment_integral_le (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) {r : ℝ} (hfs : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (k : ℕ) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    (∫x, Real.exp (b*dist p x)*dist p x^k*heatAt μ hQ t f x ∂μ) ≤
      Real.exp ((2*b+(B+(2*k:ℕ)+1))^2/2*t+(2*b+(B+(2*k:ℕ)+1))*r)*‖f‖^2+
      (∫x, dist p x^(2*k)*Real.exp (-(B+(2*k:ℕ)+1)*dist p x) ∂μ) := by
  let c := B+(2*k:ℕ)+1
  have hc : 0 ≤ 2*b+c := by dsimp [c]; positivity
  have h1 := heatAt_exponential_square_integrable μ hQ f p hfs hc ht
  have h2 := integrable_dist_pow_mul_exp μ p hA hB hvol (2*k)
  calc
    _ ≤ ∫x, Real.exp ((2*b+c)*dist p x)*heatAt μ hQ t f x^2+
        dist p x^(2*k)*Real.exp (-c*dist p x) ∂μ := by
      apply integral_mono_ae (heatAt_weighted_moment_integrable μ hQ p hA hB hvol f hfs k hb ht) (h1.add h2)
      exact Eventually.of_forall fun x => (le_abs_self _).trans (exponential_weighted_moment_young b c (dist p x) (heatAt μ hQ t f x) k)
    _ = (∫x, Real.exp ((2*b+c)*dist p x)*heatAt μ hQ t f x^2 ∂μ)+
        (∫x, dist p x^(2*k)*Real.exp (-c*dist p x) ∂μ) := integral_add h1 h2
    _ ≤ _ := add_le_add (heatAt_exponential_square_integral_le μ hQ f p hfs hc ht) le_rfl

theorem heatAt_tail_moment_integral_le (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) {r : ℝ} (hfs : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (k : ℕ) {b t T : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hT : t ≤ T) (R : ℝ) :
    (∫x in {x | R ≤ dist p x}, dist p x^k*heatAt μ hQ t f x ∂μ) ≤
      Real.exp (-b*R)*(Real.exp ((2*b+(B+(2*k:ℕ)+1))^2/2*T+(2*b+(B+(2*k:ℕ)+1))*r)*‖f‖^2+
      (∫x, dist p x^(2*k)*Real.exp (-(B+(2*k:ℕ)+1)*dist p x) ∂μ)) := by
  let S := {x : X | R ≤ dist p x}
  have hS : MeasurableSet S := (isClosed_le continuous_const (continuous_const.dist continuous_id)).measurableSet
  let w := fun x => Real.exp (b*dist p x)*dist p x^k*heatAt μ hQ t f x
  have hi := heatAt_weighted_moment_integrable μ hQ p hA hB hvol f hfs k hb ht
  have hf := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf0)
  have hwn : 0 ≤ᵐ[μ] w := hf.mono fun x hx => mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg dist_nonneg _)) hx
  have h1 : (∫x in S, dist p x^k*heatAt μ hQ t f x ∂μ) ≤ Real.exp (-b*R)*(∫x in S, w x ∂μ) := by
    rw [←integral_const_mul]
    apply integral_mono_ae (heatAt_dist_pow_integrable μ hQ p hA hB hvol f hfs k ht).integrableOn (hi.integrableOn.const_mul _)
    filter_upwards [ae_restrict_mem hS,ae_restrict_of_ae hf] with x hx hf
    have he : 1 ≤ Real.exp (-b*R)*Real.exp (b*dist p x) := by
      rw [←Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by have := mul_le_mul_of_nonneg_left hx hb; linarith)
    have hz : 0 ≤ dist p x^k*heatAt μ hQ t f x := mul_nonneg (pow_nonneg dist_nonneg _) hf
    change _ ≤ Real.exp (-b*R)*(Real.exp (b*dist p x)*dist p x^k*heatAt μ hQ t f x)
    nlinarith only [mul_le_mul_of_nonneg_right he hz]
  have h2 := setIntegral_le_integral (s := S) hi hwn
  have h3 := heatAt_weighted_moment_integral_le μ hQ p hA hB hvol f hfs k hb ht
  have h4 : Real.exp ((2*b+(B+(2*k:ℕ)+1))^2/2*t+(2*b+(B+(2*k:ℕ)+1))*r)*‖f‖^2 ≤
      Real.exp ((2*b+(B+(2*k:ℕ)+1))^2/2*T+(2*b+(B+(2*k:ℕ)+1))*r)*‖f‖^2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (2*b+(B+(2*k:ℕ)+1))])
  exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans (h3.trans (add_le_add h4 le_rfl))) (Real.exp_pos _).le)


end

 
section

 

open Set Filter
open scoped Topology

noncomputable def entropyLogTest (M r : ℝ) : ℝ :=
  Real.log (max (Real.exp (-M)) (min (Real.exp M) r))

noncomputable def entropyScore (r s : ℝ) : ℝ := r * s - Real.exp s + 1

theorem entropyLogTest_low {M r : ℝ} (hM : 0 ≤ M) (hr : r ≤ Real.exp (-M)) :
    entropyLogTest M r = -M := by
  have hMM : Real.exp (-M) ≤ Real.exp M := Real.exp_le_exp.mpr (by linarith)
  rw [entropyLogTest, min_eq_right (hr.trans hMM), max_eq_left hr, Real.log_exp]

theorem entropyLogTest_high {M r : ℝ} (hM : 0 ≤ M) (hr : Real.exp M ≤ r) :
    entropyLogTest M r = M := by
  have hMM : Real.exp (-M) ≤ Real.exp M := Real.exp_le_exp.mpr (by linarith)
  rw [entropyLogTest, min_eq_left hr, max_eq_right hMM, Real.log_exp]

theorem entropyLogTest_middle {M r : ℝ} (hr0 : Real.exp (-M) ≤ r)
    (hr1 : r ≤ Real.exp M) : entropyLogTest M r = Real.log r := by
  rw [entropyLogTest, min_eq_right hr1, max_eq_right hr0]

theorem entropyLogTest_abs_le {M : ℝ} (hM : 0 ≤ M) (r : ℝ) :
    |entropyLogTest M r| ≤ M := by
  have hpos : 0 < max (Real.exp (-M)) (min (Real.exp M) r) :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  rw [abs_le]
  constructor
  · simpa only [Real.log_exp, entropyLogTest] using
      (Real.log_le_log (Real.exp_pos (-M)) (le_max_left (Real.exp (-M)) (min (Real.exp M) r)))
  · simpa only [Real.log_exp, entropyLogTest] using
      (Real.log_le_log hpos (max_le
        (Real.exp_le_exp.mpr (by linarith : -M ≤ M)) (min_le_left (Real.exp M) r)))

theorem continuous_entropyLogTest (M : ℝ) : Continuous (entropyLogTest M) := by
  apply Continuous.log
  · exact continuous_const.max (continuous_const.min continuous_id)
  · intro r
    exact ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _))

 
theorem entropyScore_difference_le (r s t : ℝ) :
    entropyScore r t - entropyScore r s ≤ (r - Real.exp s) * (t - s) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t - s)) (Real.exp_pos s).le
  have he : Real.exp s * Real.exp (t - s) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  unfold entropyScore
  nlinarith

 
theorem entropyScore_le_logTest {M : ℝ} (hM : 0 ≤ M) (r t : ℝ) (ht : |t| ≤ M) :
    entropyScore r t ≤ entropyScore r (entropyLogTest M r) := by
  obtain ⟨ht0, ht1⟩ := abs_le.mp ht
  rcases le_total r (Real.exp (-M)) with hr0 | hr0
  · rw [entropyLogTest_low hM hr0]
    have hh := entropyScore_difference_le r (-M) t
    have hz : (r - Real.exp (-M)) * (t - -M) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr0) (by linarith)
    linarith
  · rcases le_total (Real.exp M) r with hr1 | hr1
    · rw [entropyLogTest_high hM hr1]
      have hh := entropyScore_difference_le r M t
      have hz : (r - Real.exp M) * (t - M) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr1) (by linarith)
      linarith
    · rw [entropyLogTest_middle hr0 hr1]
      have hh := entropyScore_difference_le r (Real.log r) t
      rw [Real.exp_log ((Real.exp_pos _).trans_le hr0), sub_self, zero_mul] at hh
      linarith

theorem entropyScore_logTest_nonneg {M : ℝ} (hM : 0 ≤ M) (r : ℝ) :
    0 ≤ entropyScore r (entropyLogTest M r) := by
  have hh := entropyScore_le_logTest hM r 0 (by simpa using hM)
  simpa only [entropyScore, mul_zero, Real.exp_zero, zero_sub, neg_add_cancel] using hh

theorem entropyScore_logTest_mono {M N : ℝ} (hM : 0 ≤ M) (hMN : M ≤ N) (r : ℝ) :
    entropyScore r (entropyLogTest M r) ≤ entropyScore r (entropyLogTest N r) :=
  entropyScore_le_logTest (hM.trans hMN) r _ ((entropyLogTest_abs_le hM r).trans hMN)

 
theorem entropyScore_logTest_tendsto (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun k : ℕ => entropyScore r (entropyLogTest (k + 1) r)) atTop
      (𝓝 (InformationTheory.klFun r)) := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    have h : Tendsto (fun k : ℕ => -(k + 1 : ℝ)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    have he := Real.tendsto_exp_atBot.comp h
    have hh := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub he
    convert hh using 1
    · ext k
      rw [entropyLogTest_low (by positivity) (Real.exp_pos _).le]
      simp [entropyScore]
      ring
    · simp [InformationTheory.klFun_zero]
  · have hevent : ∀ᶠ k : ℕ in atTop, |Real.log r| ≤ (k : ℝ) + 1 :=
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop _)
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with k hk
    obtain ⟨hk0, hk1⟩ := abs_le.mp hk
    have h0 : Real.exp (-((k : ℝ) + 1)) ≤ r := by
      rw [← Real.exp_log hr]
      exact Real.exp_le_exp.mpr hk0
    have h1 : r ≤ Real.exp ((k : ℝ) + 1) := by
      rw [← Real.exp_log hr]
      exact Real.exp_le_exp.mpr hk1
    rw [entropyLogTest_middle h0 h1]
    simp only [entropyScore, Real.exp_log hr, InformationTheory.klFun]
    ring


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal BoundedContinuousFunction

 
noncomputable def entropyDualValue {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ ν : Measure X) (f : X → ℝ) : ℝ :=
  (∫ x, f x ∂ν) - ∫ x, (Real.exp (f x) - 1) ∂μ

noncomputable def entropyDual {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ ν : Measure X) : ℝ≥0∞ :=
  ⨆ f : X →ᵇ ℝ, ENNReal.ofReal (entropyDualValue μ ν f)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem lowerSemicontinuous_entropyDual (μ : Measure X) :
    LowerSemicontinuous (fun ν : ProbabilityMeasure X => entropyDual μ ν) := by
  apply lowerSemicontinuous_iSup
  intro f
  exact (ENNReal.continuous_ofReal.comp
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).sub
      continuous_const)).lowerSemicontinuous

theorem entropy_fenchel (r s : ℝ) (hr : 0 ≤ r) :
    r * s - Real.exp s + 1 ≤ InformationTheory.klFun r := by
  rcases hr.eq_or_lt with h | h
  · rw [← h, zero_mul, InformationTheory.klFun_zero]
    linarith [Real.exp_pos s]
  · have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s - Real.log r)) h.le
    rw [Real.exp_sub, Real.exp_log h] at hh
    have he : r * (Real.exp s / r) = Real.exp s := by field_simp
    rw [he] at hh
    dsimp [InformationTheory.klFun]
    nlinarith

 
omit [MetricSpace X] [BorelSpace X] in
theorem rnDeriv_integral_mul (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : ν ≪ μ) (f : X → ℝ) (hf : Integrable f ν) :
    Integrable (fun x => (ν.rnDeriv μ x).toReal * f x) μ ∧
      (∫ x, (ν.rnDeriv μ x).toReal * f x ∂μ) = ∫ x, f x ∂ν := by
  have h := (integrable_rnDeriv_smul_iff hac).mpr hf
  constructor
  · simpa only [smul_eq_mul] using h
  · simpa only [smul_eq_mul] using integral_rnDeriv_smul (f := f) hac

 
theorem entropyDual_le_klDiv (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    entropyDual μ ν ≤ InformationTheory.klDiv ν μ := by
  by_cases hfin : InformationTheory.klDiv ν μ = ∞
  · rw [hfin]; exact le_top
  obtain ⟨hac, hi⟩ := InformationTheory.klDiv_ne_top_iff.mp hfin
  have hkl := (InformationTheory.integrable_klFun_rnDeriv_iff hac).mpr hi
  rw [InformationTheory.klDiv_eq_integral_klFun, ite_eq_left ⟨hac, hi⟩]
  apply iSup_le
  intro f
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨hf, he⟩ := rnDeriv_integral_mul μ ν hac f (f.integrable ν)
  have hexp : Integrable (fun x => Real.exp (f x) - 1) μ := by
    apply Integrable.mono' (integrable_const (Real.exp ‖f‖ + 1))
      (((Real.continuous_exp.comp f.continuous).sub continuous_const).aestronglyMeasurable)
    filter_upwards [] with x
    calc
      ‖Real.exp (f x) - 1‖ ≤ ‖Real.exp (f x)‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
      _ ≤ Real.exp ‖f‖ + 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
        gcongr
        exact (le_abs_self _).trans (f.norm_coe_le_norm x)
  have hh := integral_mono_ae (hf.sub hexp) hkl (Eventually.of_forall fun x =>
    show (ν.rnDeriv μ x).toReal * f x - (Real.exp (f x) - 1) ≤
      InformationTheory.klFun (ν.rnDeriv μ x).toReal by
      have h := entropy_fenchel (ν.rnDeriv μ x).toReal (f x) ENNReal.toReal_nonneg
      linarith)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hf hexp, he] at hh
  exact hh

 
theorem clip_error_le (M u v : ℝ) (hM : 0 ≤ M) (hu : |u| ≤ M) :
    |u - max (-M) (min M v)| ≤ |u - v| := by
  obtain ⟨hul, huu⟩ := abs_le.mp hu
  rcases le_total v M with hv | hv
  · rw [min_eq_right hv]
    rcases le_total (-M) v with hv' | hv'
    · rw [max_eq_right hv']
    · rw [max_eq_left hv', abs_of_nonneg (by linarith : 0 ≤ u - -M),
        abs_of_nonneg (by linarith : 0 ≤ u - v)]
      linarith
  · rw [min_eq_left hv, max_eq_right (by linarith : -M ≤ M),
      abs_of_nonpos (by linarith : u - M ≤ 0), abs_of_nonpos (by linarith : u - v ≤ 0)]
    linarith

noncomputable def clipBCF (M : ℝ) (hM : 0 ≤ M) (g : X →ᵇ ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max (-M) (min M (g x)))
    (continuous_const.max (continuous_const.min g.continuous)) M
    (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)

omit [MeasurableSpace X] [BorelSpace X] in
theorem clipBCF_abs_le (M : ℝ) (hM : 0 ≤ M) (g : X →ᵇ ℝ) (x : X) :
    |clipBCF M hM g x| ≤ M := by
  change |max (-M) (min M (g x))| ≤ M
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem exp_error_le {M u v : ℝ} (hu : u ≤ M) (hv : v ≤ M) :
    |Real.exp u - Real.exp v| ≤ Real.exp M * |u - v| := by
  have h := (convex_Iic M).norm_image_sub_le_of_norm_deriv_le
    (f := Real.exp) (fun x _ => Real.differentiableAt_exp)
    (fun x hx => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr hx) hv hu
  simpa only [Real.norm_eq_abs] using h

omit [MetricSpace X] [BorelSpace X] in
theorem bounded_measurable_integrable (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall hb)

omit [MetricSpace X] [BorelSpace X] in
theorem bounded_exp_integrable (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ x, f x ≤ M) :
    Integrable (fun x => Real.exp (f x)) μ := by
  apply bounded_measurable_integrable μ (Real.measurable_exp.comp hf) (M := Real.exp M)
  intro x
  change |Real.exp (f x)| ≤ Real.exp M
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (hb x)

 
omit [BorelSpace X] in
theorem entropyDualValue_error (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfb : ∀ x, |f x| ≤ M) (hgb : ∀ x, |g x| ≤ M) {ε : ℝ}
    (heμ : (∫ x, |f x - g x| ∂μ) ≤ ε)
    (heν : (∫ x, |f x - g x| ∂ν) ≤ ε) :
    entropyDualValue μ ν f ≤ entropyDualValue μ ν g + (1 + Real.exp M) * ε := by
  have hifμ := bounded_measurable_integrable μ hf hfb
  have higμ := bounded_measurable_integrable μ hg hgb
  have hifν := bounded_measurable_integrable ν hf hfb
  have higν := bounded_measurable_integrable ν hg hgb
  have hef := bounded_exp_integrable μ hf (fun x => (le_abs_self _).trans (hfb x))
  have heg := bounded_exp_integrable μ hg (fun x => (le_abs_self _).trans (hgb x))
  have haμ : Integrable (fun x => |f x - g x|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hifμ.sub higμ).norm
  have haν : Integrable (fun x => |f x - g x|) ν := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hifν.sub higν).norm
  have hν := integral_mono hifν (higν.add haν)
    (fun x => by
      change f x ≤ g x + |f x - g x|
      have hh := le_abs_self (f x - g x)
      linarith)
  simp only [Pi.add_apply] at hν
  rw [integral_add higν haν] at hν
  have hμ := integral_mono heg (hef.add (haμ.const_mul (Real.exp M)))
    (fun x => by
      have hh := exp_error_le ((le_abs_self _).trans (hgb x))
        ((le_abs_self _).trans (hfb x))
      rw [abs_sub_comm (g x) (f x)] at hh
      have hz := (le_abs_self (Real.exp (g x) - Real.exp (f x))).trans hh
      change Real.exp (g x) ≤ Real.exp (f x) + Real.exp M * |f x - g x|
      linarith)
  simp only [Pi.add_apply] at hμ
  rw [integral_add hef (haμ.const_mul (Real.exp M)), integral_const_mul] at hμ
  dsimp only [entropyDualValue]
  rw [integral_sub hef (integrable_const 1), integral_sub heg (integrable_const 1)]
  have hh := mul_le_mul_of_nonneg_left heμ (Real.exp_pos M).le
  nlinarith

 

theorem entropyDualValue_measurable_le [ProperSpace X] [SeparableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X → ℝ} (hf : Measurable f) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |f x| ≤ M) {b : ℝ}
    (h : ∀ g : X →ᵇ ℝ, entropyDualValue μ ν g ≤ b) :
    entropyDualValue μ ν f ≤ b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (1 + Real.exp M)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hfi := bounded_measurable_integrable (μ + ν) hf hb
  obtain ⟨g, hg, hgi⟩ := hfi.exists_boundedContinuous_integral_sub_le hδ
  let q := clipBCF M hM g
  have hq := clipBCF_abs_le M hM g
  have hifμ := bounded_measurable_integrable μ hf hb
  have hifν := bounded_measurable_integrable ν hf hb
  have hμnonneg : 0 ≤ ∫ x, ‖f x - g x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hνnonneg : 0 ≤ ∫ x, ‖f x - g x‖ ∂ν := integral_nonneg (fun _ => norm_nonneg _)
  have hint := integral_add_measure (hifμ.sub (g.integrable μ)).norm
    (hifν.sub (g.integrable ν)).norm
  simp only [Pi.sub_apply] at hint
  rw [hint] at hg
  have heμ : (∫ x, |f x - q x| ∂μ) ≤ δ := by
    have hh := integral_mono (hifμ.sub (q.integrable μ)).norm
      (hifμ.sub (g.integrable μ)).norm (fun x => clip_error_le M (f x) (g x) hM (hb x))
    change (∫ x, |f x - q x| ∂μ) ≤ ∫ x, |f x - g x| ∂μ at hh
    exact hh.trans (by simpa only [Real.norm_eq_abs] using (by linarith :
      (∫ x, ‖f x - g x‖ ∂μ) ≤ δ))
  have heν : (∫ x, |f x - q x| ∂ν) ≤ δ := by
    have hh := integral_mono (hifν.sub (q.integrable ν)).norm
      (hifν.sub (g.integrable ν)).norm (fun x => clip_error_le M (f x) (g x) hM (hb x))
    change (∫ x, |f x - q x| ∂ν) ≤ ∫ x, |f x - g x| ∂ν at hh
    exact hh.trans (by simpa only [Real.norm_eq_abs] using (by linarith :
      (∫ x, ‖f x - g x‖ ∂ν) ≤ δ))
  have herr := entropyDualValue_error μ ν hf q.continuous.measurable hb hq heμ heν
  have heq : (1 + Real.exp M) * δ = ε := by dsimp [δ]; field_simp
  rw [heq] at herr
  have hh := h q
  linarith

theorem entropyDualValue_bounded_measurable_le [ProperSpace X] [SeparableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hv : entropyDual μ ν ≠ ∞) {f : X → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M) :
    entropyDualValue μ ν f ≤ (entropyDual μ ν).toReal := by
  apply entropyDualValue_measurable_le μ ν hf hM hb
  intro g
  apply (ENNReal.ofReal_le_iff_le_toReal hv).mp
  exact le_iSup (fun g : X →ᵇ ℝ => ENNReal.ofReal (entropyDualValue μ ν g)) g

 

theorem absolutelyContinuous_of_entropyDual_ne_top [ProperSpace X] [SeparableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hv : entropyDual μ ν ≠ ∞) : ν ≪ μ := by
  intro s hs
  let t := toMeasurable μ s
  have ht : MeasurableSet t := measurableSet_toMeasurable μ s
  have hμt : μ t = 0 := by simpa [t] using hs
  have hνt : ν t = 0 := by
    by_contra hn
    have htr : 0 < ν.real t := ENNReal.toReal_pos hn (measure_ne_top ν t)
    let b := (entropyDual μ ν).toReal
    let M := (b + 1) / ν.real t
    have hM : 0 ≤ M := div_nonneg (by dsimp [b]; positivity) htr.le
    let f := t.indicator (fun _ : X => M)
    have hf : Measurable f := measurable_const.indicator ht
    have hfb : ∀ x, |f x| ≤ M := by
      intro x
      dsimp [f]
      by_cases hx : x ∈ t
      · rw [indicator_of_mem hx, abs_of_nonneg hM]
      · rw [indicator_of_notMem hx, abs_zero]
        exact hM
    have hh := entropyDualValue_bounded_measurable_le μ ν hv hf hM hfb
    have hf0 : f =ᵐ[μ] fun _ => 0 := by
      filter_upwards [(show ∀ᵐ x ∂μ, x ∉ t from by simpa only [ae_iff, not_not, ofPred_mem_eq] using hμt)] with x hx
      exact indicator_of_notMem hx _
    have hexp : (fun x => Real.exp (f x) - 1) =ᵐ[μ] fun _ => 0 := by
      filter_upwards [hf0] with x hx
      simp [hx]
    have he : entropyDualValue μ ν f = M * ν.real t := by
      rw [entropyDualValue, integral_congr_ae hexp, integral_zero, sub_zero]
      rw [show f = t.indicator (fun _ => M) from rfl, integral_indicator ht,
        integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
      ring
    rw [he] at hh
    have heq : M * ν.real t = b + 1 := by dsimp [M]; field_simp
    rw [heq] at hh
    change b + 1 ≤ b at hh
    linarith
  exact measure_mono_null (subset_toMeasurable μ s) hνt

 

theorem entropyDual_eq_klDiv [ProperSpace X] [SeparableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    entropyDual μ ν = InformationTheory.klDiv ν μ := by
  apply le_antisymm (entropyDual_le_klDiv μ ν)
  by_cases hv : entropyDual μ ν = ∞
  · rw [hv]; exact le_top
  have hac := absolutelyContinuous_of_entropyDual_ne_top μ ν hv
  let ρ : X → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have hρ : Measurable ρ := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  let fs : ℕ → X → ℝ := fun k x => entropyLogTest (k + 1) (ρ x)
  have hfs : ∀ k, Measurable (fs k) := fun k =>
    (continuous_entropyLogTest (k + 1)).measurable.comp hρ
  have hfb : ∀ k x, |fs k x| ≤ k + 1 := fun k x => entropyLogTest_abs_le (by positivity) _
  let us : ℕ → X → ℝ := fun k x => entropyScore (ρ x) (fs k x)
  have hum : ∀ k, Measurable (us k) := by
    intro k
    exact ((hρ.mul (hfs k)).sub (Real.measurable_exp.comp (hfs k))).add measurable_const
  have hun : ∀ k x, 0 ≤ us k x := fun k x => entropyScore_logTest_nonneg (by positivity) _
  have hui : ∀ k, Integrable (us k) μ := by
    intro k
    obtain ⟨hf, _⟩ := rnDeriv_integral_mul μ ν hac (fs k)
      (bounded_measurable_integrable ν (hfs k) (hfb k))
    exact (hf.sub (bounded_exp_integrable μ (hfs k)
      (fun x => (le_abs_self _).trans (hfb k x)))).add (integrable_const 1)
  have hue : ∀ k, (∫ x, us k x ∂μ) = entropyDualValue μ ν (fs k) := by
    intro k
    obtain ⟨hf, he⟩ := rnDeriv_integral_mul μ ν hac (fs k)
      (bounded_measurable_integrable ν (hfs k) (hfb k))
    have hexp := bounded_exp_integrable μ (hfs k)
      (fun x => (le_abs_self _).trans (hfb k x))
    change (∫ x, (ν.rnDeriv μ x).toReal * fs k x - Real.exp (fs k x) + 1 ∂μ) = _
    have ha := integral_add (hf.sub hexp) (integrable_const (μ := μ) (1 : ℝ))
    simp only [Pi.sub_apply] at ha
    rw [ha, integral_sub hf hexp]
    dsimp [entropyDualValue]
    rw [he, integral_sub hexp (integrable_const 1)]
    ring
  have hub : ∀ k, (∫⁻ x, ENNReal.ofReal (us k x) ∂μ) ≤ entropyDual μ ν := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hui k) (Eventually.of_forall (hun k)), hue k]
    have hb := entropyDualValue_bounded_measurable_le μ ν hv (hfs k)
      (show (0 : ℝ) ≤ k + 1 by positivity) (hfb k)
    exact (ENNReal.ofReal_le_ofReal hb).trans_eq (ENNReal.ofReal_toReal hv)
  have hut : ∀ x, Tendsto (fun k => ENNReal.ofReal (us k x)) atTop
      (𝓝 (ENNReal.ofReal (InformationTheory.klFun (ρ x)))) := by
    intro x
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (entropyScore_logTest_tendsto (ρ x) ENNReal.toReal_nonneg)
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac]
  calc
    _ = ∫⁻ x, liminf (fun k => ENNReal.ofReal (us k x)) atTop ∂μ := by
      apply lintegral_congr
      intro x
      exact (hut x).liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal (us k x) ∂μ) atTop :=
      lintegral_liminf_le (fun k => (hum k).ennreal_ofReal)
    _ ≤ entropyDual μ ν := by
      exact liminf_le_of_frequently_le ((Eventually.of_forall hub).frequently)

 
theorem lowerSemicontinuous_klDiv [ProperSpace X] [SeparableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    LowerSemicontinuous (fun ν : ProbabilityMeasure X => InformationTheory.klDiv ν μ) := by
  simpa only [entropyDual_eq_klDiv] using lowerSemicontinuous_entropyDual μ


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology ENNReal
open InformationTheory

 
theorem klFun_sub_le_log {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    klFun s - klFun r ≤ (s - r) * Real.log s := by
  have hf := entropy_fenchel r (Real.log s) hr
  rw [Real.exp_log hs] at hf
  dsimp [klFun] at hf ⊢
  nlinarith

noncomputable def entropyPerturb (C a r h : ℝ) : ℝ :=
  if C < r then (1 - a) * r + a * h else r + a * h

noncomputable def entropyGap (C D : ℝ) : ℝ :=
  (D - C) * Real.log (D / C)

noncomputable def entropyMixError (a : ℝ) : ℝ :=
  Real.log (1 + a) - Real.log (1 - a)

theorem entropyMixError_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    0 ≤ entropyMixError a := by
  exact sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))

theorem entropyGap_pos {C D : ℝ} (hC : 0 < C) (hD : C < D) :
    0 < entropyGap C D := by
  exact mul_pos (sub_pos.mpr hD) (Real.log_pos ((one_lt_div hC).mpr hD))

theorem entropyGap_mono {C D r : ℝ} (hC : 0 < C) (hD : C ≤ D) (hr : D ≤ r) :
    entropyGap C D ≤ entropyGap C r := by
  have hlog : 0 ≤ Real.log (D / C) := Real.log_nonneg ((one_le_div hC).mpr hD)
  exact mul_le_mul (by linarith : D - C ≤ r - C)
    (Real.log_le_log (div_pos (hC.trans_le hD) hC) (div_le_div_of_nonneg_right hr hC.le))
    hlog (by linarith)

theorem entropyPerturb_nonneg {C a r h : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 ≤ r) (hh : 0 ≤ h) :
    0 ≤ entropyPerturb C a r h := by
  unfold entropyPerturb
  split_ifs
  · exact add_nonneg (mul_nonneg (by linarith) hr) (mul_nonneg ha hh)
  · exact add_nonneg hr (mul_nonneg ha hh)

 

theorem entropyPerturb_kl_bound {C D a r h : ℝ}
    (hC : 0 < C) (hD : C < D) (ha : 0 < a) (ha1 : a < 1)
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hhC : h ≤ C) :
    klFun (entropyPerturb C a r h) ≤ klFun r +
      a * (h - if C < r then r else 0) * Real.log (C * (1 + a)) +
      a * r * entropyMixError a - a * (if D ≤ r then entropyGap C D else 0) := by
  have hp : 0 < 1 + a := by linarith
  have hm : 0 < 1 - a := by linarith
  have he := entropyMixError_nonneg ha.le ha1
  by_cases hCr : C < r
  · have hrp : 0 < r := hC.trans hCr
    have hs : 0 < (1 - a) * r + a * h :=
      (mul_pos hm hrp).trans_le (le_add_of_nonneg_right (mul_nonneg ha.le hh))
    have hsr : (1 - a) * r + a * h ≤ r := by nlinarith
    have hslo : (1 - a) * r ≤ (1 - a) * r + a * h :=
      le_add_of_nonneg_right (mul_nonneg ha.le hh)
    have ht := klFun_sub_le_log hr hs
    have hl := Real.log_le_log (mul_pos hm hrp) hslo
    have hmul := mul_le_mul_of_nonpos_left hl (sub_nonpos.mpr hsr)
    have hsplit : Real.log ((1 - a) * r) = Real.log (C * (1 + a)) -
        entropyMixError a + Real.log (r / C) := by
      rw [Real.log_mul hm.ne' hrp.ne', Real.log_mul hC.ne' hp.ne',
        Real.log_div hrp.ne' hC.ne', entropyMixError]
      ring
    have hlog : 0 ≤ Real.log (r / C) := Real.log_nonneg ((one_le_div hC).mpr hCr.le)
    have hgap : entropyGap C r ≤ (r - h) * Real.log (r / C) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hlog
    have herr : (r - h) * entropyMixError a ≤ r * entropyMixError a :=
      mul_le_mul_of_nonneg_right (by linarith) he
    have hmain : klFun ((1 - a) * r + a * h) ≤ klFun r +
        a * (h - r) * Real.log (C * (1 + a)) + a * r * entropyMixError a -
          a * entropyGap C r := by
      rw [hsplit] at hmul
      have hgp := mul_le_mul_of_nonneg_left hgap ha.le
      have hep := mul_le_mul_of_nonneg_left herr ha.le
      nlinarith
    simp only [entropyPerturb, ite_eq_left hCr]
    by_cases hrd : D ≤ r
    · rw [ite_eq_left hrd]
      have hg := entropyGap_mono hC hD.le hrd
      nlinarith
    · rw [ite_eq_right hrd]
      have hg : 0 ≤ entropyGap C r := mul_nonneg (sub_nonneg.mpr hCr.le) hlog
      nlinarith
  · have hrC : r ≤ C := le_of_not_gt hCr
    have hrd : ¬D ≤ r := by linarith
    simp only [entropyPerturb, ite_eq_right hCr, ite_eq_right hrd, sub_zero, mul_zero]
    by_cases hs : r + a * h = 0
    · have hr0 : r = 0 := by nlinarith [mul_nonneg ha.le hh]
      have hh0 : h = 0 := by nlinarith
      simp [hr0, hh0, entropyMixError]
    · have hsp : 0 < r + a * h := lt_of_le_of_ne (add_nonneg hr (mul_nonneg ha.le hh)) (Ne.symm hs)
      have ht := klFun_sub_le_log hr hsp
      have hb : r + a * h ≤ C * (1 + a) := by nlinarith
      have hl := Real.log_le_log hsp hb
      have hm := mul_le_mul_of_nonneg_left hl (mul_nonneg ha.le hh)
      have he' : 0 ≤ a * r * entropyMixError a := mul_nonneg (mul_nonneg ha.le hr) he
      nlinarith

variable {X : Type*} [MeasurableSpace X]

 

theorem exists_entropy_decreasing_perturbation
    (μ : Measure X) [IsFiniteMeasure μ] {ρ h : X → ℝ}
    (hρ : Measurable ρ) (hh : Measurable h)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hh0 : ∀ x, 0 ≤ h x)
    (hρi : Integrable ρ μ) (hEi : Integrable (fun x => klFun (ρ x)) μ)
    {C D : ℝ} (hC : 0 < C) (hD : C < D) (hhC : ∀ x, h x ≤ C)
    (hpos : μ {x | D ≤ ρ x} ≠ 0)
    (hmass : (∫ x, h x ∂μ) = ∫ x in {x | C < ρ x}, ρ x ∂μ) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      Integrable (fun x => klFun (entropyPerturb C a (ρ x) (h x))) μ ∧
      (∫ x, klFun (entropyPerturb C a (ρ x) (h x)) ∂μ) < ∫ x, klFun (ρ x) ∂μ := by
  let A : Set X := {x | C < ρ x}
  let T : Set X := {x | D ≤ ρ x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hρ
  have hT : MeasurableSet T := measurableSet_le measurable_const hρ
  have hhi : Integrable h μ := Integrable.of_bound hh.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hh0 x)] using hhC x)
  have hAi : Integrable (A.indicator ρ) μ := hρi.indicator hA
  have hTi : Integrable (T.indicator (fun _ => entropyGap C D)) μ :=
    (integrable_const _).indicator hT
  have hTV : 0 < entropyGap C D * μ.real T :=
    mul_pos (entropyGap_pos hC hD) (ENNReal.toReal_pos hpos (measure_ne_top μ T))
  have hc : ContinuousAt entropyMixError 0 := by
    unfold entropyMixError
    apply ContinuousAt.sub
    · apply ContinuousAt.log
      · fun_prop
      · norm_num
    · apply ContinuousAt.log
      · fun_prop
      · norm_num
  have hc0 : entropyMixError 0 = 0 := by simp [entropyMixError]
  have hv : Tendsto (fun a => entropyMixError a * ∫ x, ρ x ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [hc0, zero_mul] using
      (hc.tendsto.mul_const (∫ x, ρ x ∂μ)).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a < 1 ∧
      entropyMixError a * (∫ x, ρ x ∂μ) < entropyGap C D * μ.real T := by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      hv.eventually (gt_mem_nhds hTV)] with a ha0 ha1 haE
    exact ⟨ha0, ha1, haE⟩
  obtain ⟨a, ha0, ha1, haE⟩ := hsmall.exists
  let b := Real.log (C * (1 + a))
  let e := entropyMixError a
  let R : X → ℝ := fun x => klFun (ρ x) + a * (h x - A.indicator ρ x) * b +
    a * ρ x * e - a * T.indicator (fun _ => entropyGap C D) x
  have hRi : Integrable R μ := by
    exact ((hEi.add (((hhi.sub hAi).const_mul a).mul_const b)).add
      ((hρi.const_mul a).mul_const e)).sub (hTi.const_mul a)
  have hRm : ∀ x, klFun (entropyPerturb C a (ρ x) (h x)) ≤ R x := by
    intro x
    simpa only [R, b, e, A, T, Set.indicator_apply, mem_ofPred_eq] using
      entropyPerturb_kl_bound hC hD ha0 ha1 (hρ0 x) (hh0 x) (hhC x)
  have hpm : Measurable (fun x => entropyPerturb C a (ρ x) (h x)) := by
    change Measurable (A.piecewise (fun x => (1 - a) * ρ x + a * h x)
      (fun x => ρ x + a * h x))
    exact ((hρ.const_mul _).add (hh.const_mul _)).piecewise hA (hρ.add (hh.const_mul _))
  have hpi : Integrable (fun x => klFun (entropyPerturb C a (ρ x) (h x))) μ := by
    apply Integrable.mono' hRi.abs ((measurable_klFun.comp hpm).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖klFun (entropyPerturb C a (ρ x) (h x))‖ ≤ |R x|
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg
      (entropyPerturb_nonneg (C := C) ha0.le ha1.le (hρ0 x) (hh0 x)))]
    exact (hRm x).trans (le_abs_self _)
  refine ⟨a, ha0, ha1, hpi, ?_⟩
  have hle := integral_mono hpi hRi hRm
  have hRa : (∫ x, R x ∂μ) = (∫ x, klFun (ρ x) ∂μ) +
      a * (e * (∫ x, ρ x ∂μ) - entropyGap C D * μ.real T) := by
    have hiA : (∫ x, A.indicator ρ x ∂μ) = ∫ x, h x ∂μ :=
      (integral_indicator hA).trans hmass.symm
    have hiT : (∫ x, T.indicator (fun _ => entropyGap C D) x ∂μ) =
        entropyGap C D * μ.real T := by
      rw [integral_indicator hT, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
      ring
    dsimp [R]
    rw [integral_sub, integral_add, integral_add, integral_mul_const, integral_const_mul,
      integral_sub hhi hAi, hiA, sub_self, mul_zero, zero_mul, add_zero,
      integral_mul_const, integral_const_mul, integral_const_mul, hiT]
    · ring
    · exact hEi
    · exact ((hhi.sub hAi).const_mul a).mul_const b
    · exact hEi.add (((hhi.sub hAi).const_mul a).mul_const b)
    · exact (hρi.const_mul a).mul_const e
    · exact (hEi.add (((hhi.sub hAi).const_mul a).mul_const b)).add
        ((hρi.const_mul a).mul_const e)
    · exact hTi.const_mul a
  rw [hRa] at hle
  have hneg : a * (e * (∫ x, ρ x ∂μ) - entropyGap C D * μ.real T) < 0 :=
    mul_neg_of_pos_of_neg ha0 (sub_neg.mpr haE)
  linarith


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

section RnDerivLeConstOfLeSmul

variable {X : Type*} [MeasurableSpace X]

 

theorem rnDeriv_le_const_of_le_smul (μ ν : Measure X) [SigmaFinite μ]
    {C : ℝ≥0∞} (hν : ν ≤ C • μ) : ∀ᵐ x ∂μ, ν.rnDeriv μ x ≤ C := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    (ν.measurable_rnDeriv μ) fun s hs _ => ?_
  simpa only [lintegral_const, Measure.restrict_apply_univ,
    Measure.smul_apply, smul_eq_mul] using
    (Measure.setLIntegral_rnDeriv_le (μ := ν) (ν := μ) s).trans (hν s)

 

theorem renyiIntegral_le_ac_support_volume (μ ν : Measure X)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (N : ℝ) (hN : 1 < N) :
    renyiIntegral μ ν N ≤ (μ {x | ν.rnDeriv μ x ≠ 0}) ^ (1 / N) := by
  let s := {x | ν.rnDeriv μ x ≠ 0}
  have hs : MeasurableSet s := (measurableSet_eq_fun (ν.measurable_rnDeriv μ) measurable_const).compl
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hα : 0 < 1 - 1 / N := by
    rw [sub_pos, div_lt_one hN0]
    exact hN
  have hc : (1 / (1 - 1 / N)).HolderConjugate N := by
    rw [Real.holderConjugate_iff]
    constructor
    · rw [lt_div_iff₀ hα]
      have := one_div_pos.mpr hN0
      linarith
    · simp
  have hm : (1 - 1 / N) * (1 / (1 - 1 / N)) = 1 := mul_one_div_cancel hα.ne'
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict s) hc
    (((ν.measurable_rnDeriv μ).pow_const (1 - 1 / N)).aemeasurable)
    (f := fun x => (ν.rnDeriv μ x) ^ (1 - 1 / N))
    (g := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ← ENNReal.rpow_mul, hm, ENNReal.rpow_one,
    one_div_one_div, ENNReal.one_rpow, lintegral_const, one_mul,
    Measure.restrict_apply_univ] at hh
  have hr : (fun x => (ν.rnDeriv μ x) ^ (1 - 1 / N)) =
      s.indicator (fun x => (ν.rnDeriv μ x) ^ (1 - 1 / N)) := by
    funext x
    by_cases hx : x ∈ s
    · simp [hx]
    · have hz : ν.rnDeriv μ x = 0 := by simpa only [s, mem_ofPred_eq, not_not] using hx
      rw [Set.indicator_of_notMem hx, hz, ENNReal.zero_rpow_of_pos hα]
  calc
    renyiIntegral μ ν N = ∫⁻ x in s, (ν.rnDeriv μ x) ^ (1 - 1 / N) ∂μ := by
      unfold renyiIntegral
      conv_lhs => rw [hr]
      rw [lintegral_indicator hs]
    _ ≤ (∫⁻ x in s, ν.rnDeriv μ x ∂μ) ^ (1 - 1 / N) * (μ s) ^ (1 / N) := hh
    _ ≤ 1 ^ (1 - 1 / N) * (μ s) ^ (1 / N) :=
      mul_le_mul_left (ENNReal.rpow_le_rpow
        ((Measure.setLIntegral_rnDeriv_le s).trans (prob_le_one (μ := ν))) hα.le) _
    _ = _ := by simp [s]


variable [MetricSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

theorem cd_midpoint_renyi_lower (μ ν₀ ν₁ : Measure X) [SigmaFinite μ]
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    {C : ℝ≥0∞} (h0 : ν₀ ≤ C • μ) (h1 : ν₁ ≤ C • μ)
    (K N D : ℝ) (hN : 1 < N)
    (hD : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (hR : (∫⁻ γ, tau K N (1 - (1 / 2 : ℝ)) (dist (γ 0) (γ 1)) *
          (ν₀.rnDeriv μ (γ 0)) ^ (-(1 / N)) +
        tau K N (1 / 2) (dist (γ 0) (γ 1)) *
          (ν₁.rnDeriv μ (γ 1)) ^ (-(1 / N)) ∂π) ≤
        renyiIntegral μ (π.map (fun γ => γ (⟨1 / 2, by norm_num⟩ : Time))) N) :
    (2 * midpointFloor K N D) * C ^ (-(1 / N)) ≤
      renyiIntegral μ (π.map (fun γ => γ (⟨1 / 2, by norm_num⟩ : Time))) N := by
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have he0 : ν₀ ≪ μ := h0.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  have he1 : ν₁ ≪ μ := h1.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  have hd0 : ∀ᵐ γ ∂π, ν₀.rnDeriv μ (γ 0) ≤ C := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 0).aemeasurable
      (p := fun x => ν₀.rnDeriv μ x ≤ C)
    rw [hend.1]
    exact he0.ae_le (rnDeriv_le_const_of_le_smul μ ν₀ h0)
  have hd1 : ∀ᵐ γ ∂π, ν₁.rnDeriv μ (γ 1) ≤ C := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 1).aemeasurable
      (p := fun x => ν₁.rnDeriv μ x ≤ C)
    rw [hend.2]
    exact he1.ae_le (rnDeriv_le_const_of_le_smul μ ν₁ h1)
  have hβ : 0 ≤ 1 / N := (one_div_pos.mpr (zero_lt_one.trans hN)).le
  calc
    _ = ∫⁻ _ : C(Time, X),
        midpointFloor K N D * C ^ (-(1 / N)) +
        midpointFloor K N D * C ^ (-(1 / N)) ∂π := by
      simp only [lintegral_const, measure_univ, mul_one]
      rw [two_mul, add_mul]
    _ ≤ _ := (lintegral_mono_ae (by
      filter_upwards [hd0, hd1, hD] with γ hγ0 hγ1 hγD
      have hτ := midpointFloor_le_tau K N D (dist (γ 0) (γ 1)) hN dist_nonneg hγD
      have hi0 : C ^ (-(1 / N)) ≤ (ν₀.rnDeriv μ (γ 0)) ^ (-(1 / N)) := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hγ0 hβ)
      have hi1 : C ^ (-(1 / N)) ≤ (ν₁.rnDeriv μ (γ 1)) ^ (-(1 / N)) := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hγ1 hβ)
      norm_num only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
      exact add_le_add (mul_le_mul' hτ hi0) (mul_le_mul' hτ hi1))).trans hR

 

theorem FullCD.exists_midpoint_ac_support_bound (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (h0 : ν₀ ≤ C • μ) (h1 : ν₁ ≤ C • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (s₀ s₁ : Set X) (hs0 : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs1 : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (N D : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N)
    (hD : ∀ x ∈ s₀, ∀ y ∈ s₁, dist x y ≤ D) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      (2 * midpointFloor K N D) ^ N * C⁻¹ ≤
        μ {x | (π.map (fun γ => γ (⟨1/2, by norm_num⟩ : Time))).rnDeriv μ x ≠ 0} := by
  have he0 : ν₀ ≪ μ := h0.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  have he1 : ν₁ ≪ μ := h1.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  obtain ⟨π, hπ, hg, hp, hR⟩ := hcd ν₀ ν₁ inferInstance inferInstance he0 he1 hm0 hm1
  let := hπ
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have ha0 : ∀ᵐ γ ∂π, γ 0 ∈ s₀ := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 0).aemeasurable (p := fun x => x ∈ s₀)
    rwa [hend.1]
  have ha1 : ∀ᵐ γ ∂π, γ 1 ∈ s₁ := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 1).aemeasurable (p := fun x => x ∈ s₁)
    rwa [hend.2]
  have hπD : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D := by
    filter_upwards [ha0, ha1] with γ hγ0 hγ1
    exact hD _ hγ0 _ hγ1
  let t : Time := ⟨1/2, by norm_num⟩
  let : IsProbabilityMeasure (π.map (fun γ => γ t)) :=
    inferInstance
  have hh := (cd_midpoint_renyi_lower μ ν₀ ν₁ π hp h0 h1 K N D hN hπD (hR N hnN t)).trans
    (renyiIntegral_le_ac_support_volume μ (π.map (fun γ => γ t)) N hN)
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hpow := ENNReal.rpow_le_rpow hh hN0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hN0.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, one_div_mul_cancel hN0.ne', ENNReal.rpow_one] at hpow
  have hneg : -(1 / N) * N = -1 := by rw [neg_mul, one_div_mul_cancel hN0.ne']
  rw [hneg, ENNReal.rpow_neg_one] at hpow
  exact ⟨π, hπ, hg, hp, hpow⟩


end RnDerivLeConstOfLeSmul


section ExcessReplacement
variable {X : Type*} [MeasurableSpace X]

 

theorem measure_sub_add_of_singular (a b c : Measure X) (hac : a ⟂ₘ c) :
    a + b - c = a + (b - c) := by
  obtain ⟨s, hs, has, hcs⟩ := hac
  have ha : a.restrict s = 0 := by rwa [Measure.restrict_eq_zero]
  have hc : c.restrict sᶜ = 0 := by rwa [Measure.restrict_eq_zero]
  rw [← Measure.restrict_add_restrict_compl (μ := a + b - c) hs,
    ← Measure.restrict_add_restrict_compl (μ := a + (b - c)) hs]
  simp only [Measure.restrict_sub_eq_restrict_sub_restrict hs,
    Measure.restrict_sub_eq_restrict_sub_restrict hs.compl,
    Measure.restrict_add, ha, hc, zero_add, Measure.sub_zero]

 

theorem rnDeriv_excess (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) :
    (ν - C • μ).rnDeriv μ =ᵐ[μ] fun x => ν.rnDeriv μ x - C := by
  let : IsFiniteMeasure (C • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ univ)⟩
  have hsing : ν.singularPart μ ⟂ₘ C • μ :=
    (Measure.MutuallySingular.smul C (Measure.mutuallySingular_singularPart ν μ).symm).symm
  have he : ν - C • μ = ν.singularPart μ +
      μ.withDensity (fun x => ν.rnDeriv μ x - C) := by
    conv_lhs => rw [← Measure.singularPart_add_rnDeriv ν μ]
    rw [measure_sub_add_of_singular _ _ _ hsing]
    have hi : IsFiniteMeasure (μ.withDensity (fun _ => C)) := by
      rw [withDensity_const]
      infer_instance
    rw [← withDensity_const, ← Measure.withDensity_sub (ν.measurable_rnDeriv μ) measurable_const]
    rfl
  exact (Measure.eq_rnDeriv ((ν.measurable_rnDeriv μ).sub measurable_const)
    (Measure.mutuallySingular_singularPart ν μ) he).symm

 

theorem transportExcessMass_add_le (μ ν η : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞) :
    transportExcessMass μ (ν + η) C ≤ transportExcessMass μ ν C + η univ := by
  let : IsFiniteMeasure (C • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ univ)⟩
  have hb : ν ≤ (ν - C • μ) + C • μ := Measure.sub_le_iff_le_add.mp le_rfl
  have hh : ν + η ≤ ((ν - C • μ) + η) + C • μ := by
    simpa only [add_assoc, add_comm, add_left_comm] using add_le_add_right hb η
  exact (Measure.sub_le_of_le_add hh univ).trans_eq (Measure.add_apply _ _ _)

 

theorem ac_support_saturated_of_excess_add_eq (μ ν η : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure η]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (he : transportExcessMass μ (ν + η) C = transportExcessMass μ ν C + η univ) :
    ∀ᵐ x ∂μ, η.rnDeriv μ x ≠ 0 → C < (ν + η).rnDeriv μ x := by
  let : IsFiniteMeasure (C • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ univ)⟩
  have hb : ν ≤ (ν - C • μ) + C • μ := Measure.sub_le_iff_le_add.mp le_rfl
  have hh : ν + η - C • μ ≤ (ν - C • μ) + η :=
    Measure.sub_le_of_le_add (by
      simpa only [add_assoc, add_comm, add_left_comm] using add_le_add_right hb η)
  have hme : ν + η - C • μ = (ν - C • μ) + η :=
    Measure.eq_of_le_of_measure_univ_eq hh (by
      simpa only [transportExcessMass, Measure.add_apply] using he)
  have ha := Measure.rnDeriv_add (ν - C • μ) η μ
  rw [← hme] at ha
  filter_upwards [ha, rnDeriv_excess μ (ν + η) hC] with x hx hxs hη
  have hh : 0 < (ν + η).rnDeriv μ x - C := by
    rw [← hxs, hx, Pi.add_apply]
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hη) (le_add_left le_rfl)
  exact tsub_pos_iff_lt.mp hh

 

theorem transportExcessMass_remove (μ ν σ : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure σ]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hσ : σ ≤ ν - C • μ) :
    transportExcessMass μ (ν - σ) C + σ univ = transportExcessMass μ ν C := by
  let : IsFiniteMeasure (C • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ univ)⟩
  have hσν : σ ≤ ν := hσ.trans Measure.sub_le
  have he : ν - σ - C • μ = (ν - C • μ) - σ := by
    apply le_antisymm
    · apply Measure.sub_le_of_le_add
      apply Measure.sub_le_of_le_add
      rw [add_right_comm, Measure.sub_add_cancel_of_le hσ]
      exact Measure.sub_le_iff_le_add.mp le_rfl
    · apply Measure.sub_le_of_le_add
      apply Measure.sub_le_of_le_add
      rw [add_right_comm, add_assoc]
      have hh : ν - σ ≤ (ν - σ - C • μ) + C • μ :=
        Measure.sub_le_iff_le_add.mp le_rfl
      have hhh : ν - σ + σ ≤ (ν - σ - C • μ) + C • μ + σ :=
        add_le_add hh le_rfl
      simpa only [Measure.sub_add_cancel_of_le hσν, add_assoc] using hhh
  unfold transportExcessMass
  rw [he, ← Measure.add_apply, Measure.sub_add_cancel_of_le hσ]

 

theorem ac_support_saturated_of_minimizing_replacement (μ ν σ η : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure σ] [IsFiniteMeasure η]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hσ : σ ≤ ν - C • μ)
    (hm : η univ = σ univ)
    (hmin : transportExcessMass μ ν C ≤ transportExcessMass μ (ν - σ + η) C) :
    ∀ᵐ x ∂μ, η.rnDeriv μ x ≠ 0 → C < (ν - σ + η).rnDeriv μ x := by
  apply ac_support_saturated_of_excess_add_eq μ (ν - σ) η hC
  apply le_antisymm (transportExcessMass_add_le μ (ν - σ) η hC)
  rw [hm, transportExcessMass_remove μ ν σ hC hσ]
  exact hmin

 
theorem excess_eq_singular_add_withDensity (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞) :
    ν - C • μ = ν.singularPart μ +
      μ.withDensity (fun x => ν.rnDeriv μ x - C) := by
  let : IsFiniteMeasure (C • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ univ)⟩
  have hsing : ν.singularPart μ ⟂ₘ C • μ :=
    (Measure.MutuallySingular.smul C (Measure.mutuallySingular_singularPart ν μ).symm).symm
  conv_lhs => rw [← Measure.singularPart_add_rnDeriv ν μ]
  rw [measure_sub_add_of_singular _ _ _ hsing]
  have hi : IsFiniteMeasure (μ.withDensity (fun _ => C)) := by
    rw [withDensity_const]
    infer_instance
  rw [← withDensity_const, ← Measure.withDensity_sub (ν.measurable_rnDeriv μ) measurable_const]
  rfl

 

theorem positive_region_mass (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞)
    {s : Set X} (hs : MeasurableSet s) (hμs : μ s = 0)
    (hνs : ν.singularPart μ sᶜ = 0) :
    ν (s ∪ {x | C < ν.rnDeriv μ x}) =
      transportExcessMass μ ν C + C * μ {x | C < ν.rnDeriv μ x} := by
  let H := {x | C < ν.rnDeriv μ x}
  have hH : MeasurableSet H := measurableSet_lt measurable_const (ν.measurable_rnDeriv μ)
  have hA : MeasurableSet (s ∪ H) := hs.union hH
  have hae : ∀ᵐ x ∂μ, x ∉ s := by simpa [ae_iff] using hμs
  have hsa : (ν.singularPart μ).restrict (s ∪ H) = ν.singularPart μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    have ht : ∀ᵐ x ∂ν.singularPart μ, x ∈ s := by
      rw [ae_iff]
      convert hνs using 1
    filter_upwards [ht] with x hx using Or.inl hx
  have heq : (s ∪ H).indicator (ν.rnDeriv μ) =ᵐ[μ]
      (fun x => ν.rnDeriv μ x - C) + H.indicator (fun _ => C) := by
    filter_upwards [hae] with x hx
    by_cases ht : C < ν.rnDeriv μ x
    · simp only [mem_union, mem_ofPred_eq, ht, or_true, Set.indicator_of_mem,
        Pi.add_apply, H]
      exact (tsub_add_cancel_of_le ht.le).symm
    · have hh : x ∉ H := ht
      have ha : x ∉ s ∪ H := by simp [hx, hh]
      simp only [Set.indicator_of_notMem ha, Pi.add_apply,
        Set.indicator_of_notMem hh, add_zero]
      exact (tsub_eq_zero_of_le (le_of_not_gt ht)).symm
  have he : ν.restrict (s ∪ H) = (ν - C • μ) + (C • μ).restrict H := by
    conv_lhs => rw [← Measure.singularPart_add_rnDeriv ν μ]
    rw [Measure.restrict_add, hsa, restrict_withDensity hA,
      ← withDensity_indicator hA, withDensity_congr_ae heq,
      withDensity_add_left (f := fun x => ν.rnDeriv μ x - C)
        ((ν.measurable_rnDeriv μ).sub measurable_const),
      withDensity_indicator hH, withDensity_const, ← Measure.restrict_smul,
      ← add_assoc, ← excess_eq_singular_add_withDensity μ ν hC]
  have hh := congrArg (fun m : Measure X => m univ) he
  simpa only [Measure.restrict_apply_univ, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, transportExcessMass, H] using hh

 

theorem exists_buffer_positive_region (μ ν : Measure X)
    {C a : ℝ≥0∞} (hC : C ≠ ∞) (s : Set X)
    (ha : a < ν (s ∪ {x | C < ν.rnDeriv μ x})) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ δ ≠ ∞ ∧
      a < ν (s ∪ {x | C + δ < ν.rnDeriv μ x}) := by
  let B : ℕ → Set X := fun k => s ∪ {x | C + (↑(k+1) : ℝ≥0∞)⁻¹ < ν.rnDeriv μ x}
  have hmono : Monotone B := by
    intro i j hij x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (lt_of_le_of_lt
        (add_le_add le_rfl (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.add_le_add_right hij 1))) hx)
  have hu : (⋃ k, B k) = s ∪ {x | C < ν.rnDeriv μ x} := by
    ext x
    simp only [mem_iUnion, mem_union, mem_ofPred_eq, B]
    constructor
    · rintro ⟨k, hx | hx⟩
      · exact Or.inl hx
      · exact Or.inr (lt_of_le_of_lt (le_add_right le_rfl) hx)
    · rintro (hx | hx)
      · exact ⟨0, Or.inl hx⟩
      · obtain ⟨k, hk, hh⟩ := ENNReal.exists_nat_pos_inv_mul_lt
          (a := 1) (b := ν.rnDeriv μ x - C) (by simp) (tsub_pos_iff_lt.mpr hx).ne'
        have hb : (↑(k+1) : ℝ≥0∞)⁻¹ < ν.rnDeriv μ x - C := by
          have hl : (↑(k+1) : ℝ≥0∞)⁻¹ ≤ (↑k : ℝ≥0∞)⁻¹ :=
            ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ k)
          exact hl.trans_lt (by simpa only [mul_one] using hh)
        refine ⟨k, Or.inr ?_⟩
        exact (ENNReal.add_lt_add_left hC hb).trans_eq (add_tsub_cancel_of_le hx.le)
  rw [← hu, hmono.measure_iUnion] at ha
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp ha
  refine ⟨(↑(k+1) : ℝ≥0∞)⁻¹, ?_, ?_, hk⟩
  · exact ENNReal.inv_pos.mpr (by simp)
  · exact ENNReal.inv_ne_top.mpr (by simp)

 

theorem buffer_fraction_le_excess (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {C δ : ℝ≥0∞}
    (hC : C ≠ ∞) (hδ0 : 0 < δ) (hδ : δ ≠ ∞)
    {s : Set X} (hs : MeasurableSet s) (hμs : μ s = 0) :
    (δ / (C + δ)) • ν.restrict (s ∪ {x | C + δ < ν.rnDeriv μ x}) ≤ ν - C • μ := by
  let a := δ / (C + δ)
  let B := s ∪ {x | C + δ < ν.rnDeriv μ x}
  have hB : MeasurableSet B := hs.union
    (measurableSet_lt measurable_const (ν.measurable_rnDeriv μ))
  have hsum : C + δ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hC, hδ⟩
  have hsum0 : C + δ ≠ 0 := (lt_of_lt_of_le hδ0 (le_add_left le_rfl)).ne'
  have ha : a ≤ 1 := ENNReal.div_le_of_le_mul (by simp)
  have hatop : a ≠ ∞ := ENNReal.div_ne_top hδ hsum0
  have hsing : a • (ν.singularPart μ).restrict B ≤ ν.singularPart μ := by
    calc
      _ ≤ (1 : ℝ≥0∞) • (ν.singularPart μ).restrict B := fun t => by
        simpa only [Measure.smul_apply, smul_eq_mul] using
          mul_le_mul_left ha ((ν.singularPart μ).restrict B t)
      _ ≤ _ := by simpa only [one_smul] using
        (Measure.restrict_le_self (μ := ν.singularPart μ) (s := B))
  change a • ν.restrict B ≤ ν - C • μ
  conv_lhs => rw [← Measure.singularPart_add_rnDeriv ν μ]
  rw [Measure.restrict_add, smul_add, excess_eq_singular_add_withDensity μ ν hC]
  refine add_le_add hsing ?_
  rw [restrict_withDensity hB, ← withDensity_indicator hB,
    ← withDensity_smul a ((ν.measurable_rnDeriv μ).indicator hB)]
  apply withDensity_mono
  have hae : ∀ᵐ x ∂μ, x ∉ s := by simpa [ae_iff] using hμs
  filter_upwards [hae, Measure.rnDeriv_lt_top ν μ] with x hx hfin
  change a * B.indicator (ν.rnDeriv μ) x ≤ ν.rnDeriv μ x - C
  by_cases hxb : x ∈ B
  · rw [Set.indicator_of_mem hxb]
    have hbuf : C + δ < ν.rnDeriv μ x := hxb.resolve_left hx
    have hcr : C ≤ ν.rnDeriv μ x := (le_add_right le_rfl).trans hbuf.le
    apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top hatop hfin.ne)
      (ENNReal.sub_ne_top hfin.ne)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hcr hfin.ne]
    change (δ / (C + δ)).toReal * (ν.rnDeriv μ x).toReal ≤ _
    rw [ENNReal.toReal_div, ENNReal.toReal_add hC hδ, div_mul_eq_mul_div]
    have hd : 0 < C.toReal + δ.toReal := add_pos_of_nonneg_of_pos
      ENNReal.toReal_nonneg (ENNReal.toReal_pos hδ0.ne' hδ)
    have hb : C.toReal + δ.toReal ≤ (ν.rnDeriv μ x).toReal := by
      rw [← ENNReal.toReal_add hC hδ]
      exact ENNReal.toReal_mono hfin.ne hbuf.le
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (ENNReal.toReal_nonneg (a := C)) (sub_nonneg.mpr hb)]
  · simp only [Set.indicator_of_notMem hxb, mul_zero, zero_le]

end ExcessReplacement


variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

noncomputable abbrev midpointTime : Time := ⟨1 / 2, by norm_num⟩

 

omit [MetricSpace X] [BorelSpace X] in
theorem map_sub_of_le {Y : Type*} [MeasurableSpace Y]
    (π σ : Measure Y) [IsFiniteMeasure π] (hσ : σ ≤ π)
    (f : Y → X) (hf : Measurable f) :
    (π - σ).map f = π.map f - σ.map f := by
  let : IsFiniteMeasure σ := isFiniteMeasure_of_le π hσ
  calc
    _ = ((π - σ).map f + σ.map f) - σ.map f := (Measure.add_sub_cancel).symm
    _ = _ := by rw [← Measure.map_add _ _ hf, Measure.sub_add_cancel_of_le hσ]

 

theorem FullCD.replace_midpoint_region (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₀ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (s₀ s₁ : Set X) (hs0 : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs1 : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (N D : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N)
    (hD : ∀ x ∈ s₀, ∀ y ∈ s₁, dist x y ≤ D)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (B : Set X) (hB : MeasurableSet B)
    (hm : (π.map (fun γ => γ midpointTime)) B ≠ 0)
    {a : ℝ≥0∞} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∃ π' : Measure C(Time, X), ∃ η : Measure X,
      IsProbabilityMeasure π' ∧ IsFiniteMeasure η ∧
      (∀ᵐ γ ∂π', IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) ∧
      π'.map (fun γ => γ midpointTime) =
        π.map (fun γ => γ midpointTime) - a • (π.map (fun γ => γ midpointTime)).restrict B + η ∧
      η univ = a * (π.map (fun γ => γ midpointTime)) B ∧
      (2 * midpointFloor K N D) ^ N * (π.map (fun γ => γ midpointTime)) B * C₀⁻¹ ≤
        μ {x | η.rnDeriv μ x ≠ 0} := by
  let κ := π.restrict ((fun γ => γ midpointTime) ⁻¹' B)
  have hκ : κ ≤ π := Measure.restrict_le_self
  have hmass : κ univ = (π.map (fun γ => γ midpointTime)) B := by
    rw [Measure.map_apply (measurable_path_eval midpointTime) hB]
    exact Measure.restrict_apply_univ _
  have hκ0 : κ univ ≠ 0 := hmass ▸ hm
  have hκtop : κ univ ≠ ∞ := measure_ne_top κ univ
  let : NeZero κ := ⟨by intro he; exact hκ0 (by rw [he]; rfl)⟩
  let η₀ := (κ univ)⁻¹ • κ.map (fun γ => γ 0)
  let η₁ := (κ univ)⁻¹ • κ.map (fun γ => γ 1)
  have htprob : IsProbabilityMeasure ((κ univ)⁻¹ • κ) := inferInstance
  have he0 : (((κ univ)⁻¹ • κ).map (fun γ => γ 0)) = η₀ := Measure.map_smul _ (measurable_path_eval 0).aemeasurable
  have he1 : (((κ univ)⁻¹ • κ).map (fun γ => γ 1)) = η₁ := Measure.map_smul _ (measurable_path_eval 1).aemeasurable
  have hprob0 : IsProbabilityMeasure η₀ := he0 ▸
    inferInstance
  have hprob1 : IsProbabilityMeasure η₁ := he1 ▸
    inferInstance
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have hle0 : κ.map (fun γ => γ 0) ≤ ν₀ := by
    rw [← hend.1]
    exact Measure.map_mono hκ (measurable_path_eval 0)
  have hle1 : κ.map (fun γ => γ 1) ≤ ν₁ := by
    rw [← hend.2]
    exact Measure.map_mono hκ (measurable_path_eval 1)
  have hden0 : η₀ ≤ (C₀ * (κ univ)⁻¹) • μ := fun S => by
    simpa only [η₀, Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right ((hle0.trans h0) S) (κ univ)⁻¹
  have hden1 : η₁ ≤ (C₀ * (κ univ)⁻¹) • μ := fun S => by
    simpa only [η₁, Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right ((hle1.trans h1) S) (κ univ)⁻¹
  have hi : (κ univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hκ0
  have hs0' : ∀ᵐ x ∂η₀, x ∈ s₀ := by
    have ht : ∀ᵐ x ∂κ.map (fun γ => γ 0), x ∈ s₀ :=
      hs0.filter_mono hle0.absolutelyContinuous.ae_le
    exact ht.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hs1' : ∀ᵐ x ∂η₁, x ∈ s₁ := by
    have ht : ∀ᵐ x ∂κ.map (fun γ => γ 1), x ∈ s₁ :=
      hs1.filter_mono hle1.absolutelyContinuous.ae_le
    exact ht.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨τ, hτ, hgτ, hpτ, hvolτ⟩ := hcd.exists_midpoint_ac_support_bound μ K n η₀ η₁
    hden0 hden1 ((hm0.of_le hle0).smul hi) ((hm1.of_le hle1).smul hi)
    s₀ s₁ hs0' hs1' N D hnN hN hD
  let := hτ
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top (by simp) ha1
  let q := a * κ univ
  have hq0 : q ≠ 0 := mul_ne_zero ha0.ne' hκ0
  have hqtop : q ≠ ∞ := ENNReal.mul_ne_top hatop hκtop
  have hcancel : q * (κ univ)⁻¹ = a := by
    dsimp only [q]
    rw [mul_assoc, ENNReal.mul_inv_cancel hκ0 hκtop, mul_one]
  have hasub : a • κ ≤ π := by
    calc
      _ ≤ (1 : ℝ≥0∞) • κ := fun S => by
        simpa only [Measure.smul_apply, smul_eq_mul] using mul_le_mul_left ha1 (κ S)
      _ = κ := one_smul _ _
      _ ≤ π := hκ
  have hscaled : IsOptimalCoupling ((a • κ).map (fun γ => γ 0))
      ((a • κ).map (fun γ => γ 1)) ((q • τ).map (fun γ => (γ 0, γ 1))) := by
    have hh := hpτ.smul hq0 hqtop
    simpa only [η₀, η₁, Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_smul _ (measurable_path_eval 1).aemeasurable, Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable, smul_smul, hcancel] using hh
  have hgscaled : ∀ᵐ γ ∂(q • τ), IsGeodesic γ :=
    hgτ.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨hprob', hg', hp'⟩ := optimalPlan_replace_subplan hp hg hasub hscaled hgscaled
  let η := (q • τ).map (fun γ => γ midpointTime)
  let : IsFiniteMeasure (q • τ) := ⟨by
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact hqtop.lt_top⟩
  have hκmid : κ.map (fun γ => γ midpointTime) =
      (π.map (fun γ => γ midpointTime)).restrict B :=
    (Measure.restrict_map (measurable_path_eval midpointTime) hB).symm
  refine ⟨π - a • κ + q • τ, η, hprob', inferInstance, hg', hp', ?_, ?_, ?_⟩
  · rw [Measure.map_add _ _ (measurable_path_eval midpointTime),
      map_sub_of_le π (a • κ) hasub _ (measurable_path_eval midpointTime),
      Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable, hκmid]
  · simp only [η, Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply_of_aemeasurable (measurable_path_eval midpointTime).aemeasurable
        MeasurableSet.univ, preimage_univ, measure_univ, mul_one, q, hmass]
  · have hsupport : μ {x | η.rnDeriv μ x ≠ 0} =
        μ {x | (τ.map (fun γ => γ midpointTime)).rnDeriv μ x ≠ 0} := by
      apply measure_congr
      have hr := Measure.rnDeriv_smul_left_of_ne_top
        (τ.map (fun γ => γ midpointTime)) μ hqtop
      change ∀ᵐ x ∂μ, (η.rnDeriv μ x ≠ 0) =
        ((τ.map (fun γ => γ midpointTime)).rnDeriv μ x ≠ 0)
      dsimp only [η]
      rw [Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable]
      filter_upwards [hr] with x hx
      rw [hx, Pi.smul_apply, smul_eq_mul]
      rw [mul_ne_zero_iff]
      apply propext
      exact ⟨And.right, fun h => ⟨hq0, h⟩⟩
    rw [hsupport]
    convert hvolτ using 1
    rw [ENNReal.mul_inv (Or.inr hi) (Or.inl hC₀), inv_inv, hmass]
    ac_rfl

 

theorem FullCD.improve_saturation_of_positive_minimal_excess
    (μ : Measure X) [IsFiniteMeasure μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC : C ≠ ∞) (hCpos : C ≠ 0)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₀ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (s₀ s₁ : Set X) (hs0 : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs1 : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (N D : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N)
    (hD : ∀ x ∈ s₀, ∀ y ∈ s₁, dist x y ≤ D)
    (hfill : C⁻¹ ≤ (2 * midpointFloor K N D) ^ N * C₀⁻¹)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (hpos : transportExcessMass μ (π.map (fun γ => γ midpointTime)) C ≠ 0)
    (hmin : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
      (∀ᵐ γ ∂π', IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
      transportExcessMass μ (π.map (fun γ => γ midpointTime)) C ≤
        transportExcessMass μ (π'.map (fun γ => γ midpointTime)) C) :
    ∃ π' : Measure C(Time, X), IsProbabilityMeasure π' ∧
      (∀ᵐ γ ∂π', IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) ∧
      transportExcessMass μ (π'.map (fun γ => γ midpointTime)) C =
        transportExcessMass μ (π.map (fun γ => γ midpointTime)) C ∧
      μ {x | C < (π.map (fun γ => γ midpointTime)).rnDeriv μ x} +
        transportExcessMass μ (π.map (fun γ => γ midpointTime)) C / 2 * C⁻¹ <
      μ {x | C < (π'.map (fun γ => γ midpointTime)).rnDeriv μ x} := by
  let ν := π.map (fun γ => γ midpointTime)
  have hvprob : IsProbabilityMeasure ν :=
    inferInstance
  let e := transportExcessMass μ ν C
  let v := μ {x | C < ν.rnDeriv μ x}
  have hetop : e ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top ν univ)
    (transportExcessMass_le μ ν C)
  obtain ⟨s, hs, hμs, hνs⟩ := (Measure.mutuallySingular_singularPart ν μ).symm
  have hthreshold : e / 2 + C * v < ν (s ∪ {x | C < ν.rnDeriv μ x}) := by
    rw [positive_region_mass μ ν hC hs hμs hνs]
    exact ENNReal.add_lt_add_right
      (ENNReal.mul_ne_top hC (measure_ne_top μ _)) (ENNReal.half_lt_self hpos hetop)
  obtain ⟨δ, hδ0, hδtop, hδmass⟩ :=
    exists_buffer_positive_region μ ν hC s hthreshold
  let B := s ∪ {x | C + δ < ν.rnDeriv μ x}
  have hB : MeasurableSet B := hs.union
    (measurableSet_lt measurable_const (ν.measurable_rnDeriv μ))
  have hB0 : ν B ≠ 0 := (lt_of_le_of_lt zero_le hδmass).ne'
  let a := δ / (C + δ)
  have ha : a ≤ 1 := ENNReal.div_le_of_le_mul
    (by simp)
  have ha0 : 0 < a := ENNReal.div_pos hδ0.ne' (ENNReal.add_ne_top.mpr ⟨hC, hδtop⟩)
  have hrem : a • ν.restrict B ≤ ν - C • μ :=
    buffer_fraction_le_excess μ ν hC hδ0 hδtop hs hμs
  let : IsFiniteMeasure (a • ν.restrict B) :=
    isFiniteMeasure_of_le ν (hrem.trans Measure.sub_le)
  obtain ⟨π', η, hπ', hη, hg', hp', heq, hmass, hvol⟩ :=
    hcd.replace_midpoint_region μ K n ν₀ ν₁ hC₀ h0 h1 hm0 hm1 s₀ s₁ hs0 hs1
      N D hnN hN hD π hg hp B hB hB0 ha0 ha
  let := hπ'
  let := hη
  have hmin' := hmin π' hπ' hg' hp'
  have hmass' : η univ = (a • ν.restrict B) univ := by
    simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ] using hmass
  have hequal : transportExcessMass μ (π'.map (fun γ => γ midpointTime)) C = e := by
    apply le_antisymm _ hmin'
    rw [heq]
    exact (transportExcessMass_add_le μ (ν - a • ν.restrict B) η hC).trans_eq (by
      rw [hmass', transportExcessMass_remove μ ν (a • ν.restrict B) hC hrem])
  have hsaturated : ∀ᵐ x ∂μ, η.rnDeriv μ x ≠ 0 →
      C < (π'.map (fun γ => γ midpointTime)).rnDeriv μ x := by
    rw [heq]
    apply ac_support_saturated_of_minimizing_replacement μ ν (a • ν.restrict B) η
      hC hrem hmass'
    simpa only [heq] using hmin'
  refine ⟨π', hπ', hg', hp', hequal, ?_⟩
  have hgain : v + e / 2 * C⁻¹ < ν B * C⁻¹ := by
    have hh := ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.mpr hC)
      (ENNReal.inv_ne_top.mpr hCpos) hδmass
    convert hh using 1
    rw [add_mul, mul_assoc, mul_comm v, ← mul_assoc, ENNReal.mul_inv_cancel hCpos hC]
    simp only [one_mul, add_comm]
  exact hgain.trans_le (calc
    ν B * C⁻¹ ≤ ν B * ((2 * midpointFloor K N D) ^ N * C₀⁻¹) :=
      mul_le_mul_right hfill _
    _ = (2 * midpointFloor K N D) ^ N * ν B * C₀⁻¹ := by ac_rfl
    _ ≤ μ {x | η.rnDeriv μ x ≠ 0} := hvol
    _ ≤ μ {x | C < (π'.map (fun γ => γ midpointTime)).rnDeriv μ x} :=
      measure_mono_ae hsaturated)

 

theorem FullCD.excess_minimizer_zero
    (μ : Measure X) [IsFiniteMeasure μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC : C ≠ ∞) (hCpos : C ≠ 0)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₀ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (s₀ s₁ : Set X) (hs0 : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs1 : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (N D : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N)
    (hD : ∀ x ∈ s₀, ∀ y ∈ s₁, dist x y ≤ D)
    (hfill : C⁻¹ ≤ (2 * midpointFloor K N D) ^ N * C₀⁻¹)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (hmin : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
      (∀ᵐ γ ∂π', IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
      transportExcessMass μ (π.map (fun γ => γ midpointTime)) C ≤
        transportExcessMass μ (π'.map (fun γ => γ midpointTime)) C) :
    transportExcessMass μ (π.map (fun γ => γ midpointTime)) C = 0 := by
  by_contra hpos
  let e := transportExcessMass μ (π.map (fun γ => γ midpointTime)) C
  let A := {ρ : Measure C(Time, X) // IsProbabilityMeasure ρ ∧
    (∀ᵐ γ ∂ρ, IsGeodesic γ) ∧
    IsOptimalCoupling ν₀ ν₁ (ρ.map (fun γ => (γ 0, γ 1))) ∧
    transportExcessMass μ (ρ.map (fun γ => γ midpointTime)) C = e}
  have : Nonempty A := ⟨⟨π, inferInstance, hg, hp, rfl⟩⟩
  let v (ρ : A) := μ {x | C < (ρ.val.map (fun γ => γ midpointTime)).rnDeriv μ x}
  let S := ⨆ ρ : A, v ρ
  have hS : S ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ univ)
    (iSup_le fun _ => measure_mono (subset_univ _))
  have hstep : S + e / 2 * C⁻¹ ≤ S := by
    rw [ENNReal.iSup_add]
    apply iSup_le
    intro ρ
    let : IsProbabilityMeasure ρ.val := ρ.property.1
    have hposρ : transportExcessMass μ (ρ.val.map (fun γ => γ midpointTime)) C ≠ 0 := by
      rw [ρ.property.2.2.2]
      exact hpos
    have hminρ : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
        (∀ᵐ γ ∂π', IsGeodesic γ) →
        IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
        transportExcessMass μ (ρ.val.map (fun γ => γ midpointTime)) C ≤
          transportExcessMass μ (π'.map (fun γ => γ midpointTime)) C := by
      intro π' hπ' hg' hp'
      rw [ρ.property.2.2.2]
      exact hmin π' hπ' hg' hp'
    obtain ⟨π', hπ', hg', hp', hequal, hgain⟩ :=
      hcd.improve_saturation_of_positive_minimal_excess μ K n ν₀ ν₁
        hC₀ hC hCpos h0 h1 hm0 hm1 s₀ s₁ hs0 hs1 N D hnN hN hD hfill
        ρ.val ρ.property.2.1 ρ.property.2.2.1 hposρ hminρ
    let ρ' : A := ⟨π', hπ', hg', hp', hequal.trans ρ.property.2.2.2⟩
    rw [ρ.property.2.2.2] at hgain
    exact hgain.le.trans (le_iSup v ρ')
  have hδ : 0 < e / 2 * C⁻¹ := ENNReal.mul_pos
    (ENNReal.div_pos hpos (by simp)).ne' (ENNReal.inv_ne_zero.mpr hC)
  have hstrict := ENNReal.add_lt_add_left hS hδ
  rw [add_zero] at hstrict
  exact (not_lt_of_ge hstep) hstrict


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open InformationTheory
variable {X : Type*} [MeasurableSpace X]

theorem withDensity_ofReal_rnDeriv (μ ν : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν]
    (hac : ν ≪ μ) : μ.withDensity (fun x => ENNReal.ofReal (ν.rnDeriv μ x).toReal) = ν := by
  calc
    _ = μ.withDensity (ν.rnDeriv μ) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    _ = ν := Measure.withDensity_rnDeriv_eq ν μ hac

 

theorem entropyPerturb_withDensity (μ : Measure X) {ρ h : X → ℝ}
    (hρ : Measurable ρ) (hh : Measurable h)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hh0 : ∀ x, 0 ≤ h x) (hρi : Integrable ρ μ)
    (C : ℝ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    μ.withDensity (fun x => ENNReal.ofReal (entropyPerturb C a (ρ x) (h x))) =
      μ.withDensity (fun x => ENNReal.ofReal (ρ x)) -
        ENNReal.ofReal a • (μ.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict {x | C < ρ x} +
        ENNReal.ofReal a • μ.withDensity (fun x => ENNReal.ofReal (h x)) := by
  let A : Set X := {x | C < ρ x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hρ
  let f : X → ℝ≥0∞ := fun x => ENNReal.ofReal (ρ x)
  let g : X → ℝ≥0∞ := fun x => ENNReal.ofReal a * A.indicator f x
  let j : X → ℝ≥0∞ := fun x => ENNReal.ofReal a * ENNReal.ofReal (h x)
  have hf : Measurable f := hρ.ennreal_ofReal
  have hg : Measurable g := (hf.indicator hA).const_mul _
  have hj : Measurable j := hh.ennreal_ofReal.const_mul _
  have hG : μ.withDensity g = ENNReal.ofReal a • (μ.withDensity f).restrict A := by
    change μ.withDensity (ENNReal.ofReal a • A.indicator f) = _
    rw [withDensity_smul _ (hf.indicator hA), withDensity_indicator hA,
      ← restrict_withDensity hA]
  let : IsFiniteMeasure (μ.withDensity f) := isFiniteMeasure_withDensity_ofReal hρi.2
  let : IsFiniteMeasure (μ.withDensity g) := by
    rw [hG]
    exact Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hJ : μ.withDensity j = ENNReal.ofReal a • μ.withDensity (fun x => ENNReal.ofReal (h x)) := by
    exact withDensity_smul _ hh.ennreal_ofReal
  rw [← hG, ← hJ, ← Measure.withDensity_sub hf hg, ← withDensity_add_left (hf.sub hg) j]
  apply withDensity_congr_ae
  filter_upwards [] with x
  change ENNReal.ofReal (entropyPerturb C a (ρ x) (h x)) = f x - g x + j x
  by_cases hx : C < ρ x
  · have hxA : x ∈ A := hx
    simp only [entropyPerturb, ite_eq_left hx, g, indicator_of_mem hxA, f, j]
    have hsub : 0 ≤ ρ x - a * ρ x := by nlinarith [hρ0 x]
    rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_sub (ρ x) (mul_nonneg ha (hρ0 x)),
      ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_add hsub (mul_nonneg ha (hh0 x))]
    congr 1
    ring
  · have hxA : x ∉ A := hx
    simp only [entropyPerturb, ite_eq_right hx, g, indicator_of_notMem hxA, mul_zero, tsub_zero, f, j]
    rw [ENNReal.ofReal_add (hρ0 x) (mul_nonneg ha (hh0 x)), ENNReal.ofReal_mul ha]

 
theorem klDiv_eq_of_real_density (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ρ : X → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hEi : Integrable (fun x => klFun (ρ x)) μ)
    (heq : μ.withDensity (fun x => ENNReal.ofReal (ρ x)) = ν) :
    klDiv ν μ = ENNReal.ofReal (∫ x, klFun (ρ x) ∂μ) := by
  have hac : ν ≪ μ := by rw [← heq]; exact withDensity_absolutelyContinuous _ _
  have hrn : (fun x => (ν.rnDeriv μ x).toReal) =ᵐ[μ] ρ := by
    rw [← heq]
    filter_upwards [Measure.rnDeriv_withDensity μ hρ.ennreal_ofReal] with x hx
    rw [hx, ENNReal.toReal_ofReal (hρ0 x)]
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (klFun (ρ x)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hrn] with x hx
      rw [hx]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal hEi
      (Eventually.of_forall fun x => klFun_nonneg (hρ0 x))).symm

 

theorem exists_measure_entropy_decrease (μ ν η : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure η]
    {C : ℝ} (hC : 0 < C) (hfin : klDiv ν μ ≠ ∞)
    (hη : η ≤ ENNReal.ofReal C • μ)
    (hmass : η univ = ν {x | C < (ν.rnDeriv μ x).toReal})
    (hbad : ¬ ν ≤ ENNReal.ofReal C • μ) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      klDiv (ν - ENNReal.ofReal a • ν.restrict {x | C < (ν.rnDeriv μ x).toReal} +
        ENNReal.ofReal a • η) μ < klDiv ν μ := by
  let ρ : X → ℝ := fun x => (ν.rnDeriv μ x).toReal
  let h : X → ℝ := fun x => min C (η.rnDeriv μ x).toReal
  have hρ : Measurable ρ := (ν.measurable_rnDeriv μ).ennreal_toReal
  have hh : Measurable h := measurable_const.min (η.measurable_rnDeriv μ).ennreal_toReal
  have hρ0 : ∀ x, 0 ≤ ρ x := fun _ => ENNReal.toReal_nonneg
  have hh0 : ∀ x, 0 ≤ h x := fun _ => le_min hC.le ENNReal.toReal_nonneg
  have hhC : ∀ x, h x ≤ C := fun _ => min_le_left _ _
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.mp hfin
  have hE : Integrable (fun x => klFun (ρ x)) μ :=
    (integrable_klFun_rnDeriv_iff hac).mpr hllr
  have hηac : η ≪ μ := hη.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  have hh_eq : h =ᵐ[μ] fun x => (η.rnDeriv μ x).toReal := by
    filter_upwards [rnDeriv_le_const_of_le_smul μ η hη, Measure.rnDeriv_lt_top η μ] with x hx hxt
    apply min_eq_right
    exact (ENNReal.toReal_le_toReal hxt.ne ENNReal.ofReal_ne_top).mpr hx |>.trans_eq
      (ENNReal.toReal_ofReal hC.le)
  have hνeq : μ.withDensity (fun x => ENNReal.ofReal (ρ x)) = ν :=
    withDensity_ofReal_rnDeriv μ ν hac
  have hηeq : μ.withDensity (fun x => ENNReal.ofReal (h x)) = η := by
    calc
      _ = μ.withDensity (fun x => ENNReal.ofReal (η.rnDeriv μ x).toReal) :=
        withDensity_congr_ae (hh_eq.fun_comp ENNReal.ofReal)
      _ = η := withDensity_ofReal_rnDeriv μ η hηac
  have hD : ∃ D : ℝ, C < D ∧ μ {x | D ≤ ρ x} ≠ 0 := by
    by_contra hn
    push Not at hn
    have hae : ∀ᵐ x ∂μ, ρ x ≤ C := (ae_le_const_iff_forall_gt_measure_zero ρ C).mpr hn
    apply hbad
    rw [← hνeq, ← withDensity_const]
    exact withDensity_mono (hae.mono fun x hx => ENNReal.ofReal_le_ofReal hx)
  obtain ⟨D, hDC, hDp⟩ := hD
  have hMi : (∫ x, h x ∂μ) = ∫ x in {x | C < ρ x}, ρ x ∂μ := by
    rw [integral_congr_ae hh_eq, Measure.integral_toReal_rnDeriv hηac,
      Measure.setIntegral_toReal_rnDeriv hac]
    exact congrArg ENNReal.toReal hmass
  obtain ⟨a, ha0, ha1, hpEi, hp⟩ := exists_entropy_decreasing_perturbation μ hρ hh
    hρ0 hh0 Measure.integrable_toReal_rnDeriv hE hC hDC hhC hDp hMi
  refine ⟨a, ha0, ha1, ?_⟩
  let A : Set X := {x | C < ρ x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hρ
  let ξ := ν - ENNReal.ofReal a • ν.restrict A + ENNReal.ofReal a • η
  let : IsFiniteMeasure (ENNReal.ofReal a • η) := Measure.smul_finite _ ENNReal.ofReal_ne_top
  let : IsFiniteMeasure ξ := inferInstance
  have hpM : Measurable (fun x => entropyPerturb C a (ρ x) (h x)) := by
    change Measurable (A.piecewise (fun x => (1 - a) * ρ x + a * h x)
      (fun x => ρ x + a * h x))
    exact ((hρ.const_mul _).add (hh.const_mul _)).piecewise hA (hρ.add (hh.const_mul _))
  have hp0 : ∀ x, 0 ≤ entropyPerturb C a (ρ x) (h x) :=
    fun x => entropyPerturb_nonneg (C := C) ha0.le ha1.le (hρ0 x) (hh0 x)
  have hpEq : μ.withDensity (fun x => ENNReal.ofReal (entropyPerturb C a (ρ x) (h x))) = ξ := by
    rw [entropyPerturb_withDensity μ hρ hh hρ0 hh0 Measure.integrable_toReal_rnDeriv C ha0.le ha1.le,
      hνeq, hηeq]
  change klDiv ξ μ < klDiv ν μ
  rw [klDiv_eq_of_real_density μ ξ hpM hp0 hpEi hpEq,
    klDiv_eq_of_real_density μ ν hρ hρ0 hE hνeq]
  apply (ENNReal.ofReal_lt_ofReal_iff _).mpr hp
  exact lt_of_le_of_lt (integral_nonneg fun x => klFun_nonneg (hp0 x)) hp


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

omit [SeparableSpace X] in
theorem optimal_geodesic_plan_bounded
    (ν₀ ν₁ : Measure X) (π : Measure C(Time, X))
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (p : X) {R : ℝ} (_ : 0 ≤ R)
    (h0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (h1 : ∀ᵐ x ∂ν₁, dist x p ≤ R) :
    ∀ᵐ γ ∂π, IsGeodesic γ ∧ ∀ t, dist (γ t) p ≤ 3 * R := by
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have he0 : ∀ᵐ γ ∂π, dist (γ 0) p ≤ R := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 0).aemeasurable
      (p := fun x => dist x p ≤ R)
    simpa only [hend.1] using h0
  have he1 : ∀ᵐ γ ∂π, dist (γ 1) p ≤ R := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 1).aemeasurable
      (p := fun x => dist x p ≤ R)
    simpa only [hend.2] using h1
  filter_upwards [hg, he0, he1] with γ hgeo hγ0 hγ1
  refine ⟨hgeo, fun t => ?_⟩
  have hd : dist (γ 0) (γ 1) ≤ 2 * R := by
    have hh := dist_triangle (γ 0) p (γ 1)
    rw [dist_comm p (γ 1)] at hh
    linarith
  have ht : |(t : ℝ) - (0 : Time)| ≤ 1 := by
    change |(t : ℝ) - 0| ≤ 1
    rw [sub_zero, abs_of_nonneg t.property.1]
    exact t.property.2
  calc
    dist (γ t) p ≤ dist (γ t) (γ 0) + dist (γ 0) p := dist_triangle _ _ _
    _ = |(t : ℝ) - (0 : Time)| * dist (γ 0) (γ 1) + dist (γ 0) p := by
      rw [hgeo t 0]
    _ ≤ 1 * (2 * R) + R := add_le_add (mul_le_mul ht hd dist_nonneg (by norm_num)) hγ0
    _ = _ := by ring

 

noncomputable def clippedPathCost (B : ℝ≥0) : C(Time, X) →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun γ => min (nndist (γ 0) (γ 1) ^ 2) B,
      ((continuous_eval_const 0).nndist (continuous_eval_const 1)).pow 2 |>.min continuous_const⟩
    B (by
      intro γ ζ
      change |((min (nndist (γ 0) (γ 1) ^ 2) B : ℝ≥0) : ℝ) -
        ((min (nndist (ζ 0) (ζ 1) ^ 2) B : ℝ≥0) : ℝ)| ≤ (B : ℝ)
      have hγ : ((min (nndist (γ 0) (γ 1) ^ 2) B : ℝ≥0) : ℝ) ≤ B :=
        NNReal.coe_le_coe.mpr (min_le_right _ _)
      have hζ : ((min (nndist (ζ 0) (ζ 1) ^ 2) B : ℝ≥0) : ℝ) ≤ B :=
        NNReal.coe_le_coe.mpr (min_le_right _ _)
      have hnγ := (min (nndist (γ 0) (γ 1) ^ 2) B).property
      have hnζ := (min (nndist (ζ 0) (ζ 1) ^ 2) B).property
      exact abs_le.mpr ⟨by linarith, by linarith⟩)

theorem lintegral_clippedPathCost (π : Measure C(Time, X)) (B : ℝ≥0)
    (hB : ∀ᵐ γ ∂π, nndist (γ 0) (γ 1) ^ 2 ≤ B) :
    ∫⁻ γ, (clippedPathCost B γ : ℝ≥0∞) ∂π =
      transportCost (π.map (fun γ => (γ 0, γ 1))) := by
  rw [transportCost, lintegral_map
    (by fun_prop : Measurable (fun xy : X × X => ENNReal.ofReal (dist xy.1 xy.2) ^ 2))
    ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
  apply lintegral_congr_ae
  filter_upwards [hB] with γ hγ
  change ((min (nndist (γ 0) (γ 1) ^ 2) B : ℝ≥0) : ℝ≥0∞) = _
  rw [min_eq_left hγ, ENNReal.coe_pow, ← edist_dist, edist_nndist]

 

def OptimalGeodesicPlans (ν₀ ν₁ : ProbabilityMeasure X) : Set (ProbabilityMeasure C(Time, X)) :=
  {π | (∀ᵐ γ ∂(π : Measure C(Time, X)), IsGeodesic γ) ∧
    IsOptimalCoupling ν₀ ν₁ ((π : Measure C(Time, X)).map (fun γ => (γ 0, γ 1)))}

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] in
theorem bounded_path_cost (π : Measure C(Time, X)) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hπ : ∀ᵐ γ ∂π, ∀ t, dist (γ t) p ≤ R) :
    ∀ᵐ γ ∂π, nndist (γ 0) (γ 1) ^ 2 ≤ (⟨2 * R, by positivity⟩ : ℝ≥0) ^ 2 := by
  filter_upwards [hπ] with γ hγ
  apply pow_le_pow_left' _ 2
  apply NNReal.coe_le_coe.mp
  change dist (γ 0) (γ 1) ≤ 2 * R
  have hd := dist_triangle (γ 0) p (γ 1)
  rw [dist_comm p (γ 1)] at hd
  have h0 := hγ 0
  have h1 := hγ 1
  linarith

 

theorem isCompact_optimal_geodesic_plans [ProperSpace X]
    (ν₀ ν₁ : ProbabilityMeasure X) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (h0 : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ R)
    (h1 : ∀ᵐ x ∂(ν₁ : Measure X), dist x p ≤ R) :
    IsCompact (OptimalGeodesicPlans ν₀ ν₁) := by
  rcases (OptimalGeodesicPlans ν₀ ν₁).eq_empty_or_nonempty with he | ⟨q, hq⟩
  · rw [he]
    exact isCompact_empty
  let B : ℝ≥0 := (⟨2 * (3 * R), by positivity⟩ : ℝ≥0) ^ 2
  let f : ProbabilityMeasure C(Time, X) → ℝ≥0∞ :=
    fun π => ∫⁻ γ, (clippedPathCost B γ : ℝ≥0∞) ∂(π : Measure C(Time, X))
  let c := transportCost ((q : Measure C(Time, X)).map (fun γ => (γ 0, γ 1)))
  have hc : IsClosed {π | f π ≤ c} :=
    isClosed_le (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
      (clippedPathCost B)) continuous_const
  have h3R : 0 ≤ 3 * R := by positivity
  have hcompact := (isCompact_bounded_geodesic_plans_marginals p h3R ν₀ ν₁).inter_right hc
  convert hcompact using 1
  ext π
  constructor
  · intro hπ
    have hb := optimal_geodesic_plan_bounded ν₀ ν₁ π hπ.1 hπ.2 p hR h0 h1
    have he := optimalPlan_endpoints (ν₀ : Measure X) (ν₁ : Measure X) (π : Measure C(Time, X)) hπ.2
    have hmap0 : π.map (fun γ => γ 0) = ν₀ := by
      apply ProbabilityMeasure.toMeasure_injective
      simpa only [ProbabilityMeasure.toMeasure_map] using he.1
    have hmap1 : π.map (fun γ => γ 1) = ν₁ := by
      apply ProbabilityMeasure.toMeasure_injective
      simpa only [ProbabilityMeasure.toMeasure_map] using he.2
    refine ⟨⟨hb, hmap0, hmap1⟩, ?_⟩
    change f π ≤ c
    change (∫⁻ γ, (clippedPathCost B γ : ℝ≥0∞) ∂(π : Measure C(Time, X))) ≤ c
    rw [lintegral_clippedPathCost (π : Measure C(Time, X)) B (bounded_path_cost π p h3R (hb.mono fun γ hγ => hγ.2))]
    exact hπ.2.2.2 _ hq.2.1 hq.2.2.1
  · rintro ⟨⟨hb, he0, he1⟩, hcost⟩
    have hpairs := (measurable_path_eval (X := X) 0).prodMk (measurable_path_eval 1)
    have hmap0 : ((π : Measure C(Time, X)).map (fun γ => (γ 0, γ 1))).map Prod.fst = ν₀ := by
      rw [Measure.map_map measurable_fst hpairs]
      exact congrArg ProbabilityMeasure.toMeasure he0
    have hmap1 : ((π : Measure C(Time, X)).map (fun γ => (γ 0, γ 1))).map Prod.snd = ν₁ := by
      rw [Measure.map_map measurable_snd hpairs]
      exact congrArg ProbabilityMeasure.toMeasure he1
    refine ⟨hb.mono (fun γ hγ => hγ.1), hmap0, hmap1, ?_⟩
    intro η hη0 hη1
    have hfc := lintegral_clippedPathCost (π : Measure C(Time, X)) B
      (bounded_path_cost π p h3R (hb.mono fun γ hγ => hγ.2))
    exact hfc.symm.trans_le (hcost.trans (hq.2.2.2 η hη0 hη1))

 
theorem exists_optimal_geodesic_plan_minimizing_excess [ProperSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.OuterRegular μ]
    (ν₀ ν₁ : ProbabilityMeasure X) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (h0 : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ R)
    (h1 : ∀ᵐ x ∂(ν₁ : Measure X), dist x p ≤ R)
    (hne : (OptimalGeodesicPlans ν₀ ν₁).Nonempty)
    (t : Time) {C : ℝ≥0∞} (hC : C ≠ ∞) :
    ∃ π ∈ OptimalGeodesicPlans ν₀ ν₁, ∀ q ∈ OptimalGeodesicPlans ν₀ ν₁,
      transportExcessMass μ ((π : Measure C(Time, X)).map (fun γ => γ t)) C ≤
        transportExcessMass μ ((q : Measure C(Time, X)).map (fun γ => γ t)) C := by
  have hc := isCompact_optimal_geodesic_plans ν₀ ν₁ p hR h0 h1
  have hmap : Continuous (fun π : ProbabilityMeasure C(Time, X) =>
      π.map (fun γ => γ t)) :=
    ProbabilityMeasure.continuous_map (continuous_eval_const t)
  have hl := (lowerSemicontinuous_transportExcessMass μ hC).comp hmap
  exact (hl.lowerSemicontinuousOn (OptimalGeodesicPlans ν₀ ν₁)).exists_isMinOn hne hc


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem exists_optimal_geodesic_plan_minimizing_entropy [ProperSpace X] [SeparableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (ν₀ ν₁ : ProbabilityMeasure X) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (h0 : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ R)
    (h1 : ∀ᵐ x ∂(ν₁ : Measure X), dist x p ≤ R)
    (hne : (OptimalGeodesicPlans ν₀ ν₁).Nonempty) (t : Time) :
    ∃ π ∈ OptimalGeodesicPlans ν₀ ν₁, ∀ q ∈ OptimalGeodesicPlans ν₀ ν₁,
      InformationTheory.klDiv ((π : Measure C(Time, X)).map (fun γ => γ t)) μ ≤
        InformationTheory.klDiv ((q : Measure C(Time, X)).map (fun γ => γ t)) μ := by
  have hc := isCompact_optimal_geodesic_plans ν₀ ν₁ p hR h0 h1
  have hmap : Continuous (fun π : ProbabilityMeasure C(Time, X) =>
      π.map (fun γ => γ t)) :=
    ProbabilityMeasure.continuous_map (continuous_eval_const t)
  have hl := (lowerSemicontinuous_klDiv μ).comp hmap
  exact (hl.lowerSemicontinuousOn (OptimalGeodesicPlans ν₀ ν₁)).exists_isMinOn hne hc


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal

section Localization
variable {X : Type*} [MeasurableSpace X]

 
theorem rnDeriv_restrict_reference (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    {B : Set X} (hB : MeasurableSet B) :
    ν.rnDeriv μ =ᵐ[μ.restrict B] ν.rnDeriv (μ.restrict B) := by
  have hs : μ.restrict B ⟂ₘ μ.restrict Bᶜ :=
    ⟨Bᶜ, hB.compl, by simp [Measure.restrict_apply, hB.compl],
      by simp [Measure.restrict_apply, hB]⟩
  have hr := Measure.rnDeriv_add_right_of_mutuallySingular (μ := ν) hs
  rwa [Measure.restrict_add_restrict_compl hB] at hr

 

theorem ac_support_volume_restrict (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    {B : Set X} (hB : MeasurableSet B) (hν : ∀ᵐ x ∂ν, x ∈ B) :
    μ {x | ν.rnDeriv μ x ≠ 0} =
      (μ.restrict B) {x | ν.rnDeriv (μ.restrict B) x ≠ 0} := by
  have hi := Measure.ae_rnDeriv_ne_zero_imp_of_ae μ hν
  have he : {x | ν.rnDeriv μ x ≠ 0} =ᵐ[μ] ({x | ν.rnDeriv μ x ≠ 0} ∩ B : Set X) := by
    filter_upwards [hi] with x hx
    apply propext
    exact ⟨fun h => ⟨h, hx h⟩, And.left⟩
  have hm : MeasurableSet {x | ν.rnDeriv μ x ≠ 0} :=
    ((ν.measurable_rnDeriv μ) (measurableSet_singleton 0)).compl
  rw [measure_congr he, ← Measure.restrict_apply hm]
  apply measure_congr
  filter_upwards [rnDeriv_restrict_reference μ ν hB] with x hx
  rw [hx]
end Localization

section LocalizedReplacement
variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

theorem FullCD.improve_localized_saturation
    (μ : Measure X) [SigmaFinite μ]
    (W : Set X) (hW : MeasurableSet W) [IsFiniteMeasure (μ.restrict W)]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC : C ≠ ∞) (hCpos : C ≠ 0)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₀ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (s₀ s₁ : Set X) (hs0 : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs1 : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (N D : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N)
    (hD : ∀ x ∈ s₀, ∀ y ∈ s₁, dist x y ≤ D)
    (hsupport : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      ∀ᵐ x ∂q.map (fun γ => γ midpointTime), x ∈ W)
    (hfill : C⁻¹ ≤ (2 * midpointFloor K N D) ^ N * C₀⁻¹)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (hpos : transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C ≠ 0)
    (hmin : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
      (∀ᵐ γ ∂π', IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
      transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C ≤
        transportExcessMass (μ.restrict W) (π'.map (fun γ => γ midpointTime)) C) :
    ∃ π' : Measure C(Time, X), IsProbabilityMeasure π' ∧
      (∀ᵐ γ ∂π', IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) ∧
      transportExcessMass (μ.restrict W) (π'.map (fun γ => γ midpointTime)) C =
        transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C ∧
      (μ.restrict W) {x | C < (π.map (fun γ => γ midpointTime)).rnDeriv (μ.restrict W) x} +
        transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C / 2 * C⁻¹ <
      (μ.restrict W) {x | C < (π'.map (fun γ => γ midpointTime)).rnDeriv (μ.restrict W) x} := by
  let ν := π.map (fun γ => γ midpointTime)
  have hvprob : IsProbabilityMeasure ν :=
    inferInstance
  let e := transportExcessMass (μ.restrict W) ν C
  let v := (μ.restrict W) {x | C < ν.rnDeriv (μ.restrict W) x}
  have hetop : e ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top ν univ)
    (transportExcessMass_le (μ.restrict W) ν C)
  obtain ⟨s, hs, hμs, hνs⟩ := (Measure.mutuallySingular_singularPart ν (μ.restrict W)).symm
  have hthreshold : e / 2 + C * v < ν (s ∪ {x | C < ν.rnDeriv (μ.restrict W) x}) := by
    rw [positive_region_mass (μ.restrict W) ν hC hs hμs hνs]
    exact ENNReal.add_lt_add_right
      (ENNReal.mul_ne_top hC (measure_ne_top (μ.restrict W) _)) (ENNReal.half_lt_self hpos hetop)
  obtain ⟨δ, hδ0, hδtop, hδmass⟩ :=
    exists_buffer_positive_region (μ.restrict W) ν hC s hthreshold
  let B := s ∪ {x | C + δ < ν.rnDeriv (μ.restrict W) x}
  have hB : MeasurableSet B := hs.union
    (measurableSet_lt measurable_const (ν.measurable_rnDeriv (μ.restrict W)))
  have hB0 : ν B ≠ 0 := (lt_of_le_of_lt zero_le hδmass).ne'
  let a := δ / (C + δ)
  have ha : a ≤ 1 := ENNReal.div_le_of_le_mul
    (by simp)
  have ha0 : 0 < a := ENNReal.div_pos hδ0.ne' (ENNReal.add_ne_top.mpr ⟨hC, hδtop⟩)
  have hrem : a • ν.restrict B ≤ ν - C • μ.restrict W :=
    buffer_fraction_le_excess (μ.restrict W) ν hC hδ0 hδtop hs hμs
  let : IsFiniteMeasure (a • ν.restrict B) :=
    isFiniteMeasure_of_le ν (hrem.trans Measure.sub_le)
  obtain ⟨π', η, hπ', hη, hg', hp', heq, hmass, hvol⟩ :=
    hcd.replace_midpoint_region μ K n ν₀ ν₁ hC₀ h0 h1 hm0 hm1 s₀ s₁ hs0 hs1
      N D hnN hN hD π hg hp B hB hB0 ha0 ha
  let := hπ'
  let := hη
  have hηle : η ≤ π'.map (fun γ => γ midpointTime) := by
    rw [heq]
    exact Measure.le_add_left le_rfl
  have hηsupp : ∀ᵐ x ∂η, x ∈ W :=
    (hsupport π' hπ' hg' hp').filter_mono hηle.absolutelyContinuous.ae_le
  have hvolLoc := hvol.trans_eq (ac_support_volume_restrict μ η hW hηsupp)
  have hmin' := hmin π' hπ' hg' hp'
  have hmass' : η univ = (a • ν.restrict B) univ := by
    simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ] using hmass
  have hequal : transportExcessMass (μ.restrict W) (π'.map (fun γ => γ midpointTime)) C = e := by
    apply le_antisymm _ hmin'
    rw [heq]
    exact (transportExcessMass_add_le (μ.restrict W) (ν - a • ν.restrict B) η hC).trans_eq (by
      rw [hmass', transportExcessMass_remove (μ.restrict W) ν (a • ν.restrict B) hC hrem])
  have hsaturated : ∀ᵐ x ∂μ.restrict W, η.rnDeriv (μ.restrict W) x ≠ 0 →
      C < (π'.map (fun γ => γ midpointTime)).rnDeriv (μ.restrict W) x := by
    rw [heq]
    apply ac_support_saturated_of_minimizing_replacement (μ.restrict W) ν (a • ν.restrict B) η
      hC hrem hmass'
    simpa only [heq] using hmin'
  refine ⟨π', hπ', hg', hp', hequal, ?_⟩
  have hgain : v + e / 2 * C⁻¹ < ν B * C⁻¹ := by
    have hh := ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.mpr hC)
      (ENNReal.inv_ne_top.mpr hCpos) hδmass
    convert hh using 1
    rw [add_mul, mul_assoc, mul_comm v, ← mul_assoc, ENNReal.mul_inv_cancel hCpos hC]
    simp only [one_mul, add_comm]
  exact hgain.trans_le (calc
    ν B * C⁻¹ ≤ ν B * ((2 * midpointFloor K N D) ^ N * C₀⁻¹) :=
      mul_le_mul_right hfill _
    _ = (2 * midpointFloor K N D) ^ N * ν B * C₀⁻¹ := by ac_rfl
    _ ≤ (μ.restrict W) {x | η.rnDeriv (μ.restrict W) x ≠ 0} := hvolLoc
    _ ≤ (μ.restrict W) {x | C < (π'.map (fun γ => γ midpointTime)).rnDeriv (μ.restrict W) x} :=
      measure_mono_ae hsaturated)

 

theorem FullCD.localized_excess_minimizer_zero
    (μ : Measure X) [SigmaFinite μ]
    (W : Set X) (hW : MeasurableSet W) [IsFiniteMeasure (μ.restrict W)]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC : C ≠ ∞) (hCpos : C ≠ 0)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₀ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (s₀ s₁ : Set X) (hs0 : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs1 : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (N D : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N)
    (hD : ∀ x ∈ s₀, ∀ y ∈ s₁, dist x y ≤ D)
    (hsupport : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      ∀ᵐ x ∂q.map (fun γ => γ midpointTime), x ∈ W)
    (hfill : C⁻¹ ≤ (2 * midpointFloor K N D) ^ N * C₀⁻¹)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (hmin : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
      (∀ᵐ γ ∂π', IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
      transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C ≤
        transportExcessMass (μ.restrict W) (π'.map (fun γ => γ midpointTime)) C) :
    transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C = 0 := by
  by_contra hpos
  let e := transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C
  let A := {ρ : Measure C(Time, X) // IsProbabilityMeasure ρ ∧
    (∀ᵐ γ ∂ρ, IsGeodesic γ) ∧
    IsOptimalCoupling ν₀ ν₁ (ρ.map (fun γ => (γ 0, γ 1))) ∧
    transportExcessMass (μ.restrict W) (ρ.map (fun γ => γ midpointTime)) C = e}
  have : Nonempty A := ⟨⟨π, inferInstance, hg, hp, rfl⟩⟩
  let v (ρ : A) := (μ.restrict W) {x | C < (ρ.val.map (fun γ => γ midpointTime)).rnDeriv (μ.restrict W) x}
  let S := ⨆ ρ : A, v ρ
  have hS : S ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top (μ.restrict W) univ)
    (iSup_le fun _ => measure_mono (subset_univ _))
  have hstep : S + e / 2 * C⁻¹ ≤ S := by
    rw [ENNReal.iSup_add]
    apply iSup_le
    intro ρ
    let : IsProbabilityMeasure ρ.val := ρ.property.1
    have hposρ : transportExcessMass (μ.restrict W) (ρ.val.map (fun γ => γ midpointTime)) C ≠ 0 := by
      rw [ρ.property.2.2.2]
      exact hpos
    have hminρ : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
        (∀ᵐ γ ∂π', IsGeodesic γ) →
        IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
        transportExcessMass (μ.restrict W) (ρ.val.map (fun γ => γ midpointTime)) C ≤
          transportExcessMass (μ.restrict W) (π'.map (fun γ => γ midpointTime)) C := by
      intro π' hπ' hg' hp'
      rw [ρ.property.2.2.2]
      exact hmin π' hπ' hg' hp'
    obtain ⟨π', hπ', hg', hp', hequal, hgain⟩ :=
      hcd.improve_localized_saturation μ W hW K n ν₀ ν₁
        hC₀ hC hCpos h0 h1 hm0 hm1 s₀ s₁ hs0 hs1 N D hnN hN hD hsupport hfill
        ρ.val ρ.property.2.1 ρ.property.2.2.1 hposρ hminρ
    let ρ' : A := ⟨π', hπ', hg', hp', hequal.trans ρ.property.2.2.2⟩
    rw [ρ.property.2.2.2] at hgain
    exact hgain.le.trans (le_iSup v ρ')
  have hδ : 0 < e / 2 * C⁻¹ := ENNReal.mul_pos
    (ENNReal.div_pos hpos (by simp)).ne' (ENNReal.inv_ne_zero.mpr hC)
  have hstrict := ENNReal.add_lt_add_left hS hδ
  rw [add_zero] at hstrict
  exact (not_lt_of_ge hstep) hstrict

end LocalizedReplacement

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

theorem FullCD.exists_compressed_midpoint_at_capacity
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC : C ≠ ∞) (hCpos : C ≠ 0)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₀ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    [IsFiniteMeasure (μ.restrict (closedBall p (3 * R)))]
    [Measure.OuterRegular (μ.restrict (closedBall p (3 * R)))]
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (N : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N)
    (hfill : C⁻¹ ≤ (2 * midpointFloor K N (2 * R)) ^ N * C₀⁻¹) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤ C • μ := by
  let W := closedBall p (3 * R)
  have hW : MeasurableSet W := isClosed_closedBall.measurableSet
  have hsupport : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      ∀ᵐ x ∂q.map (fun γ => γ midpointTime), x ∈ W := by
    intro q hq hgq hpq
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable hW).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ q hgq hpq p hR hs0 hs1).mono
      (fun γ hγ => hγ.2 midpointTime)
  let v0 : ProbabilityMeasure X := ⟨ν₀, inferInstance⟩
  let v1 : ProbabilityMeasure X := ⟨ν₁, inferInstance⟩
  obtain ⟨q, hq, hgq, hpq, _⟩ := hcd ν₀ ν₁ inferInstance inferInstance
    (Measure.absolutelyContinuous_of_le_smul h0)
    (Measure.absolutelyContinuous_of_le_smul h1) hm0 hm1
  have hne : (OptimalGeodesicPlans v0 v1).Nonempty := ⟨⟨q, hq⟩, hgq, hpq⟩
  obtain ⟨π, hπ, hmπ⟩ := exists_optimal_geodesic_plan_minimizing_excess
    (μ.restrict W) v0 v1 p hR hs0 hs1 hne midpointTime hC
  have hmin : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      transportExcessMass (μ.restrict W) ((π : Measure C(Time, X)).map (fun γ => γ midpointTime)) C ≤
        transportExcessMass (μ.restrict W) (q.map (fun γ => γ midpointTime)) C := by
    intro q hq hgq hpq
    exact hmπ ⟨q, hq⟩ ⟨hgq, hpq⟩
  have hD : ∀ x ∈ closedBall p R, ∀ y ∈ closedBall p R, dist x y ≤ 2 * R := by
    intro x hx y hy
    have hd := dist_triangle x p y
    rw [dist_comm p y] at hd
    change dist x p ≤ R at hx
    change dist y p ≤ R at hy
    linarith
  have hz := hcd.localized_excess_minimizer_zero μ W hW K n ν₀ ν₁ hC₀ hC hCpos
    h0 h1 hm0 hm1 (closedBall p R) (closedBall p R) hs0 hs1 N (2 * R) hnN hN hD
    hsupport hfill (π : Measure C(Time, X)) hπ.1 hπ.2 hmin
  refine ⟨π, inferInstance, hπ.1, hπ.2, ?_⟩
  have hs := hsupport (π : Measure C(Time, X)) inferInstance hπ.1 hπ.2
  have ht := localized_excess_zero_iff μ ((π : Measure C(Time, X)).map (fun γ => γ midpointTime))
    (B := W) (C := C) hs hC
  exact ht.mp hz


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

noncomputable def midpointCapacity (K N D : ℝ) (C₀ : ℝ≥0∞) : ℝ≥0∞ :=
  C₀ / (2 * midpointFloor K N D) ^ N

theorem midpointCapacity_ne_top (K N D : ℝ) {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) :
    midpointCapacity K N D C₀ ≠ ∞ := by
  apply ENNReal.div_ne_top hC₀
  exact (ENNReal.rpow_pos (ENNReal.mul_pos (by norm_num)
    (midpointFloor_pos K N D).ne')
    (ENNReal.mul_ne_top (by norm_num) (midpointFloor_ne_top K N D))).ne'

theorem midpointCapacity_pos (K N D : ℝ) {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ 0) :
    0 < midpointCapacity K N D C₀ := by
  apply ENNReal.div_pos hC₀
  apply ENNReal.rpow_ne_top_of_ne_zero
  · exact mul_ne_zero (by norm_num) (midpointFloor_pos K N D).ne'
  · exact ENNReal.mul_ne_top (by norm_num) (midpointFloor_ne_top K N D)

theorem midpointCapacity_fill (K N D : ℝ) (C₀ : ℝ≥0∞) :
    (midpointCapacity K N D C₀)⁻¹ = (2 * midpointFloor K N D) ^ N * C₀⁻¹ := by
  have hnz : (2 * midpointFloor K N D) ^ N ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.mul_pos (by norm_num)
      (midpointFloor_pos K N D).ne')
      (ENNReal.mul_ne_top (by norm_num) (midpointFloor_ne_top K N D))).ne'
  have hnt : (2 * midpointFloor K N D) ^ N ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero
      (mul_ne_zero (by norm_num) (midpointFloor_pos K N D).ne')
      (ENNReal.mul_ne_top (by norm_num) (midpointFloor_ne_top K N D))
  rw [midpointCapacity, ENNReal.inv_div (Or.inl hnt) (Or.inl hnz), div_eq_mul_inv]

omit [MetricSpace X] [BorelSpace X] in
theorem probability_capacity_ne_zero (μ ν : Measure X) [IsProbabilityMeasure ν]
    {C : ℝ≥0∞} (h : ν ≤ C • μ) : C ≠ 0 := by
  intro hz
  have hh := h univ
  rw [hz, zero_smul] at hh
  simp at hh

 

theorem NoncollapsedRCD.exists_compressed_midpoint (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤
        midpointCapacity K n (2 * R) C₀ • hausdorff n X := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let : IsFiniteMeasure ((hausdorff n X).restrict (closedBall p (3 * R))) :=
    ⟨by simpa using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  have hCpos := probability_capacity_ne_zero _ _ h0
  apply hX.cd.exists_compressed_midpoint_at_capacity (hausdorff n X) K n ν₀ ν₁
    hC₀ (midpointCapacity_ne_top K n (2 * R) hC₀)
    (midpointCapacity_pos K n (2 * R) hCpos).ne' h0 h1 hm0 hm1 p hR hs0 hs1
    (n : ℝ) le_rfl
  · exact_mod_cast (show 1 < n by omega)
  · exact (midpointCapacity_fill K n (2 * R) C₀).le


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
open InformationTheory
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

theorem NoncollapsedRCD.compressed_replacement_subplan
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (_ : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (B : Set X) (hB : MeasurableSet B)
    (hm : (π.map (fun γ => γ midpointTime)) B ≠ 0) :
    ∃ σ : Measure C(Time, X), IsFiniteMeasure σ ∧
      (∀ᵐ γ ∂σ, IsGeodesic γ) ∧
      IsOptimalCoupling
        ((π.restrict ((fun γ => γ midpointTime) ⁻¹' B)).map (fun γ => γ 0))
        ((π.restrict ((fun γ => γ midpointTime) ⁻¹' B)).map (fun γ => γ 1))
        (σ.map (fun γ => (γ 0, γ 1))) ∧
      (σ.map (fun γ => γ midpointTime)) univ = (π.map (fun γ => γ midpointTime)) B ∧
      σ.map (fun γ => γ midpointTime) ≤ midpointCapacity K n (2 * R) C₀ •
        (hausdorff n X).restrict (closedBall p (3 * R)) := by
  let : SeparableSpace X := hX.separable
  let κ := π.restrict ((fun γ => γ midpointTime) ⁻¹' B)
  have hκ : κ ≤ π := Measure.restrict_le_self
  have hmass : κ univ = (π.map (fun γ => γ midpointTime)) B := by
    rw [Measure.map_apply (measurable_path_eval midpointTime) hB]
    exact Measure.restrict_apply_univ _
  have hκ0 : κ univ ≠ 0 := hmass ▸ hm
  have hκtop : κ univ ≠ ∞ := measure_ne_top κ univ
  let : NeZero κ := ⟨by intro he; exact hκ0 (by rw [he]; rfl)⟩
  let η₀ := (κ univ)⁻¹ • κ.map (fun γ => γ 0)
  let η₁ := (κ univ)⁻¹ • κ.map (fun γ => γ 1)
  have htprob : IsProbabilityMeasure ((κ univ)⁻¹ • κ) := inferInstance
  have he0 : (((κ univ)⁻¹ • κ).map (fun γ => γ 0)) = η₀ := Measure.map_smul _ (measurable_path_eval 0).aemeasurable
  have he1 : (((κ univ)⁻¹ • κ).map (fun γ => γ 1)) = η₁ := Measure.map_smul _ (measurable_path_eval 1).aemeasurable
  have hprob0 : IsProbabilityMeasure η₀ := he0 ▸
    inferInstance
  have hprob1 : IsProbabilityMeasure η₁ := he1 ▸
    inferInstance
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have hle0 : κ.map (fun γ => γ 0) ≤ ν₀ := by
    rw [← hend.1]
    exact Measure.map_mono hκ (measurable_path_eval 0)
  have hle1 : κ.map (fun γ => γ 1) ≤ ν₁ := by
    rw [← hend.2]
    exact Measure.map_mono hκ (measurable_path_eval 1)
  have hden0 : η₀ ≤ (C₀ * (κ univ)⁻¹) • hausdorff n X := fun S => by
    simpa only [η₀, Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right ((hle0.trans h0) S) (κ univ)⁻¹
  have hden1 : η₁ ≤ (C₀ * (κ univ)⁻¹) • hausdorff n X := fun S => by
    simpa only [η₁, Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right ((hle1.trans h1) S) (κ univ)⁻¹
  have hi : (κ univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hκ0
  have hk0 : ∀ᵐ x ∂κ.map (fun γ => γ 0), dist x p ≤ R :=
    hs0.filter_mono hle0.absolutelyContinuous.ae_le
  have hk1 : ∀ᵐ x ∂κ.map (fun γ => γ 1), dist x p ≤ R :=
    hs1.filter_mono hle1.absolutelyContinuous.ae_le
  have hs0' : ∀ᵐ x ∂η₀, dist x p ≤ R :=
    hk0.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hs1' : ∀ᵐ x ∂η₁, dist x p ≤ R :=
    hk1.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨τ, hτ, hgτ, hpτ, hcapτ⟩ := hX.exists_compressed_midpoint K n hn η₀ η₁
    (ENNReal.mul_ne_top hC₀ hi) hden0 hden1
    ((hm0.of_le hle0).smul hi) ((hm1.of_le hle1).smul hi) p hR hs0' hs1'
  let := hτ
  let σ := κ univ • τ
  let : IsFiniteMeasure σ := Measure.smul_finite _ hκtop
  have hscaled : IsOptimalCoupling (κ.map (fun γ => γ 0)) (κ.map (fun γ => γ 1))
      (σ.map (fun γ => (γ 0, γ 1))) := by
    have hh := hpτ.smul hκ0 hκtop
    simpa only [σ, η₀, η₁, Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable, smul_smul,
      ENNReal.mul_inv_cancel hκ0 hκtop, one_smul] using hh
  have hgσ : ∀ᵐ γ ∂σ, IsGeodesic γ :=
    hgτ.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hσcap : σ.map (fun γ => γ midpointTime) ≤
      midpointCapacity K n (2 * R) C₀ • hausdorff n X := by
    rw [show σ = κ univ • τ from rfl, Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable]
    have hmul : κ univ * midpointCapacity K n (2 * R) (C₀ * (κ univ)⁻¹) =
        midpointCapacity K n (2 * R) C₀ := by
      dsimp only [midpointCapacity]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        _ = C₀ * ((κ univ) * (κ univ)⁻¹) * ((2 * midpointFloor K n (2 * R)) ^ (n : ℝ))⁻¹ := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel hκ0 hκtop, mul_one]
    calc
      _ ≤ κ univ • (midpointCapacity K n (2 * R) (C₀ * (κ univ)⁻¹) • hausdorff n X) :=
        fun S => by
          simpa only [Measure.smul_apply, smul_eq_mul, mul_comm] using
            mul_le_mul_left (hcapτ S) (κ univ)
      _ = _ := by rw [smul_smul, hmul]
  have hσsupport : ∀ᵐ x ∂σ.map (fun γ => γ midpointTime), x ∈ closedBall p (3 * R) := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ σ hgσ hscaled p hR hk0 hk1).mono
      (fun γ hγ => hγ.2 midpointTime)
  refine ⟨σ, inferInstance, hgσ, hscaled, ?_,
    (compression_iff_localized _ _ hσsupport _).mp hσcap⟩
  simp only [σ, Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply_of_aemeasurable (measurable_path_eval midpointTime).aemeasurable
      MeasurableSet.univ, preimage_univ, measure_univ, mul_one, hmass]

omit [MetricSpace X] [BorelSpace X] in
theorem klDiv_ne_top_of_bounded_density (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hν : ν ≤ C • μ) : klDiv ν μ ≠ ∞ := by
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) C.toReal)).exists_bound_of_continuousOn
    continuous_klFun.continuousOn
  have hi : Integrable (fun x => klFun (ν.rnDeriv μ x).toReal) μ := by
    apply Integrable.of_bound ((measurable_klFun.comp
      (ν.measurable_rnDeriv μ).ennreal_toReal).aestronglyMeasurable) M
    filter_upwards [rnDeriv_le_const_of_le_smul μ ν hν, Measure.rnDeriv_lt_top ν μ] with x hx hxt
    exact hM _ ⟨ENNReal.toReal_nonneg, (ENNReal.toReal_le_toReal hxt.ne hC).mpr hx⟩
  exact klDiv_ne_top_iff.mpr ⟨hac, (integrable_klFun_rnDeriv_iff hac).mp hi⟩

omit [MetricSpace X] [BorelSpace X] in
theorem superlevel_mass_ne_zero_of_not_compressed (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : ν ≪ μ)
    {C : ℝ} (hC : 0 < C) (hbad : ¬ ν ≤ ENNReal.ofReal C • μ) :
    ν {x | C < (ν.rnDeriv μ x).toReal} ≠ 0 := by
  intro hz
  have hν : ∀ᵐ x ∂ν, ¬ C < (ν.rnDeriv μ x).toReal := by
    simpa only [ae_iff, not_not] using hz
  have hμ := Measure.ae_rnDeriv_ne_zero_imp_of_ae μ hν
  apply hbad
  rw [← withDensity_ofReal_rnDeriv μ ν hac, ← withDensity_const]
  apply withDensity_mono
  filter_upwards [hμ] with x hx
  apply ENNReal.ofReal_le_ofReal
  by_cases hn : ν.rnDeriv μ x = 0
  · simp only [hn, ENNReal.toReal_zero]
    exact hC.le
  · exact le_of_not_gt (hx hn)

 

theorem NoncollapsedRCD.entropy_minimizer_compressed
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (hfin : klDiv (π.map (fun γ => γ midpointTime))
      ((hausdorff n X).restrict (closedBall p (3 * R))) ≠ ∞)
    (hmin : ∀ q : Measure C(Time, X), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      klDiv (π.map (fun γ => γ midpointTime)) ((hausdorff n X).restrict (closedBall p (3 * R))) ≤
      klDiv (q.map (fun γ => γ midpointTime)) ((hausdorff n X).restrict (closedBall p (3 * R)))) :
    π.map (fun γ => γ midpointTime) ≤ midpointCapacity K n (2 * R) C₀ • hausdorff n X := by
  let : SeparableSpace X := hX.separable
  let μ := (hausdorff n X).restrict (closedBall p (3 * R))
  let : IsFiniteMeasure μ := ⟨by
    simpa [μ] using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  let ν := π.map (fun γ => γ midpointTime)
  let C := midpointCapacity K n (2 * R) C₀
  have hCtop : C ≠ ∞ := midpointCapacity_ne_top K n (2 * R) hC₀
  have hC0 : C ≠ 0 := (midpointCapacity_pos K n (2 * R) (probability_capacity_ne_zero _ _ h0)).ne'
  have hCreal : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  have hCe : ENNReal.ofReal C.toReal = C := ENNReal.ofReal_toReal hCtop
  have hsupport : ∀ᵐ x ∂ν, x ∈ closedBall p (3 * R) := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ π hg hp p hR hs0 hs1).mono
      (fun γ hγ => hγ.2 midpointTime)
  by_contra hbad
  have hbad' : ¬ ν ≤ ENNReal.ofReal C.toReal • μ := by
    rw [hCe]
    exact fun h => hbad ((compression_iff_localized _ _ hsupport C).mpr h)
  let B := {x | C.toReal < (ν.rnDeriv μ x).toReal}
  have hB : MeasurableSet B := measurableSet_lt measurable_const (ν.measurable_rnDeriv μ).ennreal_toReal
  have hm : ν B ≠ 0 := superlevel_mass_ne_zero_of_not_compressed μ ν
    (klDiv_ne_top_iff.mp hfin).1 hCreal hbad'
  obtain ⟨σ, hσfin, hgσ, hpσ, hmσ, hcapσ⟩ := hX.compressed_replacement_subplan K n hn
    ν₀ ν₁ hC₀ h0 h1 hm0 hm1 p hR hs0 hs1 π hg hp B hB hm
  let := hσfin
  let η := σ.map (fun γ => γ midpointTime)
  obtain ⟨a, ha0, ha1, hdrop⟩ := exists_measure_entropy_decrease μ ν η hCreal hfin
    (by simpa only [hCe] using hcapσ) hmσ hbad'
  let κ := π.restrict ((fun γ => γ midpointTime) ⁻¹' B)
  have hκ : κ ≤ π := Measure.restrict_le_self
  have haE : ENNReal.ofReal a ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal ha1.le
  have hsub : ENNReal.ofReal a • κ ≤ π := by
    calc
      _ ≤ (1 : ℝ≥0∞) • κ := fun S => by
        simpa only [Measure.smul_apply, smul_eq_mul] using mul_le_mul_left haE (κ S)
      _ = κ := one_smul _ _
      _ ≤ π := hκ
  have hs : IsOptimalCoupling ((ENNReal.ofReal a • κ).map (fun γ => γ 0))
      ((ENNReal.ofReal a • κ).map (fun γ => γ 1))
      ((ENNReal.ofReal a • σ).map (fun γ => (γ 0, γ 1))) := by
    simpa only [Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_smul _ (measurable_path_eval 1).aemeasurable, Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable] using hpσ.smul (ENNReal.ofReal_pos.mpr ha0).ne' ENNReal.ofReal_ne_top
  have hgs : ∀ᵐ γ ∂(ENNReal.ofReal a • σ), IsGeodesic γ :=
    hgσ.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨hq, hgq, hpq⟩ := optimalPlan_replace_subplan hp hg hsub hs hgs
  have hle := hmin _ hq hgq hpq
  have hκmid : κ.map (fun γ => γ midpointTime) = ν.restrict B :=
    (Measure.restrict_map (measurable_path_eval midpointTime) hB).symm
  rw [Measure.map_add _ _ (measurable_path_eval midpointTime),
    map_sub_of_le π (ENNReal.ofReal a • κ) hsub _ (measurable_path_eval midpointTime),
    Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable, Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable, hκmid] at hle
  exact (not_lt_of_ge hle) hdrop

 

theorem NoncollapsedRCD.exists_compressed_entropy_minimizing_midpoint
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤ midpointCapacity K n (2 * R) C₀ • hausdorff n X ∧
      ∀ q : Measure C(Time, X), IsProbabilityMeasure q →
        (∀ᵐ γ ∂q, IsGeodesic γ) →
        IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
        klDiv (π.map (fun γ => γ midpointTime)) ((hausdorff n X).restrict (closedBall p (3 * R))) ≤
        klDiv (q.map (fun γ => γ midpointTime)) ((hausdorff n X).restrict (closedBall p (3 * R))) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := (hausdorff n X).restrict (closedBall p (3 * R))
  let : IsFiniteMeasure μ := ⟨by
    simpa [μ] using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  let v0 : ProbabilityMeasure X := ⟨ν₀, inferInstance⟩
  let v1 : ProbabilityMeasure X := ⟨ν₁, inferInstance⟩
  obtain ⟨q, hq, hgq, hpq, hqcap⟩ := hX.exists_compressed_midpoint K n hn ν₀ ν₁
    hC₀ h0 h1 hm0 hm1 p hR hs0 hs1
  let := hq
  have hne : (OptimalGeodesicPlans v0 v1).Nonempty := ⟨⟨q, hq⟩, hgq, hpq⟩
  obtain ⟨π, hπ, hmπ⟩ := exists_optimal_geodesic_plan_minimizing_entropy μ v0 v1 p hR hs0 hs1 hne midpointTime
  have hmin : ∀ q' : Measure C(Time, X), IsProbabilityMeasure q' →
      (∀ᵐ γ ∂q', IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q'.map (fun γ => (γ 0, γ 1))) →
      klDiv ((π : Measure C(Time, X)).map (fun γ => γ midpointTime)) μ ≤
      klDiv (q'.map (fun γ => γ midpointTime)) μ := by
    intro q' hq' hgq' hpq'
    exact hmπ ⟨q', hq'⟩ ⟨hgq', hpq'⟩
  have hqS : ∀ᵐ x ∂q.map (fun γ => γ midpointTime), x ∈ closedBall p (3 * R) := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ q hgq hpq p hR hs0 hs1).mono
      (fun γ hγ => hγ.2 midpointTime)
  have hqcap' := (compression_iff_localized _ _ hqS _).mp hqcap
  have hqfin := klDiv_ne_top_of_bounded_density μ (q.map (fun γ => γ midpointTime))
    (midpointCapacity_ne_top K n (2 * R) hC₀) hqcap'
  have hfin : klDiv ((π : Measure C(Time, X)).map (fun γ => γ midpointTime)) μ ≠ ∞ :=
    ne_top_of_le_ne_top hqfin (hmin q hq hgq hpq)
  refine ⟨π, inferInstance, hπ.1, hπ.2,
    hX.entropy_minimizer_compressed K n hn ν₀ ν₁ hC₀ h0 h1 hm0 hm1 p hR hs0 hs1
      (π : Measure C(Time, X)) hπ.1 hπ.2 hfin hmin, hmin⟩


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
open InformationTheory
variable {X : Type*} [MeasurableSpace X]

theorem rnDeriv_eq_indicator_of_supported (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] {B : Set X} (hB : MeasurableSet B)
    (hs : ∀ᵐ x ∂ν, x ∈ B) :
    ν.rnDeriv μ =ᵐ[μ] B.indicator (ν.rnDeriv μ) := by
  simpa only [Measure.restrict_eq_self_of_ae_mem hs] using Measure.rnDeriv_restrict ν μ hB

theorem density_transform_eq_indicator (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] {B : Set X} (hB : MeasurableSet B)
    (hs : ∀ᵐ x ∂ν, x ∈ B) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (fun x => f (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      B.indicator (fun x => f (ν.rnDeriv μ x).toReal) := by
  filter_upwards [rnDeriv_eq_indicator_of_supported μ ν hB hs] with x hx
  by_cases h : x ∈ B
  · simp only [indicator_of_mem h]
  · simp only [indicator_of_notMem h] at hx ⊢
    rw [hx, ENNReal.toReal_zero, hf]

theorem density_rpow_half_integrable_of_supported (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] {B : Set X} (hB : MeasurableSet B)
    [IsFiniteMeasure (μ.restrict B)] (hs : ∀ᵐ x ∂ν, x ∈ B) :
    Integrable (fun x => (ν.rnDeriv μ x).toReal ^ (1 / 2 : ℝ)) μ := by
  apply Integrable.congr _ (density_transform_eq_indicator μ ν hB hs
    (fun r => r ^ (1 / 2 : ℝ)) (by norm_num)).symm
  apply (integrable_indicator_iff hB).mpr
  have hi : Integrable (fun x => (ν.rnDeriv μ x).toReal) μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (ν := μ) (measure_ne_top ν univ))
  apply ((integrable_const (1 : ℝ)).add hi.restrict).mono'
    (((ν.measurable_rnDeriv μ).ennreal_toReal.pow_const _).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
  change (ν.rnDeriv μ x).toReal ^ (1 / 2 : ℝ) ≤ 1 + (ν.rnDeriv μ x).toReal
  rcases le_total (ν.rnDeriv μ x).toReal 1 with h | h
  · exact (Real.rpow_le_one ENNReal.toReal_nonneg h (by norm_num)).trans
      (by linarith [ENNReal.toReal_nonneg (a := ν.rnDeriv μ x)])
  · exact (Real.rpow_le_self_of_one_le h (by norm_num)).trans (by linarith)

theorem rnDeriv_localized (μ ν : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν]
    {B : Set X} (hB : MeasurableSet B) (hac : ν ≪ μ.restrict B) :
    ν.rnDeriv μ =ᵐ[μ] B.indicator (ν.rnDeriv (μ.restrict B)) := by
  have he : μ.withDensity (B.indicator (ν.rnDeriv (μ.restrict B))) = ν := by
    rw [withDensity_indicator hB,
      Measure.withDensity_rnDeriv_eq _ _ hac]
  simpa only [he] using
    Measure.rnDeriv_withDensity μ ((ν.measurable_rnDeriv (μ.restrict B)).indicator hB)

theorem localized_density_transform (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] {B : Set X} (hB : MeasurableSet B)
    (hac : ν ≪ μ.restrict B) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (fun x => f (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      B.indicator (fun x => f (ν.rnDeriv (μ.restrict B) x).toReal) := by
  filter_upwards [rnDeriv_localized μ ν hB hac] with x hx
  rw [hx]
  by_cases h : x ∈ B
  · simp only [indicator_of_mem h]
  · simp only [indicator_of_notMem h, ENNReal.toReal_zero, hf]

variable [MetricSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem boltzmannEntropy_localized (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] {B : Set X} (hB : MeasurableSet B)
    (hac : ν ≪ μ.restrict B) :
    boltzmannEntropy μ ν = boltzmannEntropy (μ.restrict B) ν := by
  unfold boltzmannEntropy
  rw [integral_congr_ae (localized_density_transform μ ν hB hac
    (fun r => r * Real.log r) (by simp)), integral_indicator hB]

omit [MetricSpace X] [BorelSpace X] in
theorem entropy_integrable_localized_iff (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] {B : Set X} (hB : MeasurableSet B)
    (hac : ν ≪ μ.restrict B) :
    Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ ↔
      Integrable (fun x => (ν.rnDeriv (μ.restrict B) x).toReal *
        Real.log (ν.rnDeriv (μ.restrict B) x).toReal) (μ.restrict B) := by
  rw [integrable_congr (localized_density_transform μ ν hB hac
    (fun r => r * Real.log r) (by simp)), integrable_indicator_iff hB]
  rfl

omit [MetricSpace X] [BorelSpace X] in
theorem toReal_klDiv_eq_boltzmannEntropy (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hfin : klDiv ν μ ≠ ∞) :
    (klDiv ν μ).toReal = boltzmannEntropy μ ν + μ.real univ - ν.real univ := by
  obtain ⟨hac, hi⟩ := klDiv_ne_top_iff.mp hfin
  rw [toReal_klDiv hac hi]
  congr 2
  exact (integral_rnDeriv_smul (f := fun x => Real.log (ν.rnDeriv μ x).toReal) hac).symm

omit [MetricSpace X] [BorelSpace X] in
theorem entropy_integrable_of_klDiv_ne_top (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hfin : klDiv ν μ ≠ ∞) :
    Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ :=
  (integrable_toReal_rnDeriv_mul_iff (klDiv_ne_top_iff.mp hfin).1).mpr
    (klDiv_ne_top_iff.mp hfin).2

omit [MetricSpace X] [BorelSpace X] in
theorem entropy_integrable_of_bounded_support (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • μ)
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (hs : ∀ᵐ x ∂ν, x ∈ B) :
    Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ := by
  have hloc : ν ≤ C • μ.restrict B := (compression_iff_localized μ ν hs C).mp hν
  have hac := Measure.absolutelyContinuous_of_le_smul hloc
  exact (entropy_integrable_localized_iff μ ν hB hac).mpr
    (entropy_integrable_of_klDiv_ne_top _ _ (klDiv_ne_top_of_bounded_density _ _ hC hloc))


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
open InformationTheory
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem integrable_dist_sq_of_ae_bounded (ν : Measure X) [IsFiniteMeasure ν]
    (p : X) {R : ℝ} (hs : ∀ᵐ x ∂ν, dist x p ≤ R) :
    Integrable (fun x => dist p x ^ 2) ν := by
  apply Integrable.of_bound ((continuous_const.dist continuous_id).pow 2).aestronglyMeasurable (R ^ 2)
  filter_upwards [hs] with x hx
  change ‖dist p x ^ 2‖ ≤ R ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), dist_comm p x]
  exact pow_le_pow_left₀ dist_nonneg hx 2

variable [SeparableSpace X]

theorem FullCD.exists_bounded_support_entropy_plan (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (h0 : ν₀ ≤ C • μ) (h1 : ν₁ ≤ C • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    [IsFiniteMeasure (μ.restrict (closedBall p (3 * R)))]
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R) :
    ∃ q : Measure C(Time, X), IsProbabilityMeasure q ∧
      (∀ᵐ γ ∂q, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) ∧
      ∀ t : Time, let ν := q.map (fun γ => γ t)
        ν ≪ μ ∧
        Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ ∧
        boltzmannEntropy μ ν ≤ (1 - (t : ℝ)) * boltzmannEntropy μ ν₀ +
          (t : ℝ) * boltzmannEntropy μ ν₁ +
          ((-K) * (t : ℝ) * (1 - (t : ℝ)) / 2) * (wassersteinSq ν₀ ν₁).toReal := by
  have ha0 := Measure.absolutelyContinuous_of_le_smul h0
  have ha1 := Measure.absolutelyContinuous_of_le_smul h1
  have hs0' : ∀ᵐ x ∂ν₀, x ∈ closedBall p (3 * R) := hs0.mono fun x hx => by
    change dist x p ≤ 3 * R
    linarith
  have hs1' : ∀ᵐ x ∂ν₁, x ∈ closedBall p (3 * R) := hs1.mono fun x hx => by
    change dist x p ≤ 3 * R
    linarith
  have he0 := entropy_integrable_of_bounded_support μ ν₀ hC h0 measurableSet_closedBall hs0'
  have he1 := entropy_integrable_of_bounded_support μ ν₁ hC h1 measurableSet_closedBall hs1'
  obtain ⟨q, hq, hgq, hpq, hineq⟩ := hcd ν₀ ν₁ inferInstance inferInstance ha0 ha1 hm0 hm1
  let := hq
  have hd := optimalPlan_dist_sq_integrable ν₀ ν₁ q hpq p
    (integrable_dist_sq_of_ae_bounded ν₀ p hs0) (integrable_dist_sq_of_ae_bounded ν₁ p hs1)
  have hc : (wassersteinSq ν₀ ν₁).toReal = ∫ γ, dist (γ 0) (γ 1) ^ 2 ∂q := by
    rw [wassersteinSq_eq_cost hpq, transportCost_plan_eq_integral q hd,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hInt0 : (∫ x, Real.log (ν₀.rnDeriv μ x).toReal ∂ν₀) = boltzmannEntropy μ ν₀ := by
    exact (integral_rnDeriv_smul (f := fun x => Real.log (ν₀.rnDeriv μ x).toReal) ha0).symm
  have hInt1 : (∫ x, Real.log (ν₁.rnDeriv μ x).toReal ∂ν₁) = boltzmannEntropy μ ν₁ := by
    exact (integral_rnDeriv_smul (f := fun x => Real.log (ν₁.rnDeriv μ x).toReal) ha1).symm
  refine ⟨q, hq, hgq, hpq, fun t => ?_⟩
  let ν := q.map (fun γ => γ t)
  let : IsProbabilityMeasure ν := inferInstance
  have hs : ∀ᵐ x ∂ν, x ∈ closedBall p (3 * R) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ q hgq hpq p hR hs0 hs1).mono fun γ hγ => hγ.2 t
  have hhalf := density_rpow_half_integrable_of_supported μ ν measurableSet_closedBall hs
  have hac := cd_plan_absolutelyContinuous_half μ K n ν₀ ν₁ ha0 ha1 q hpq t
    (fun N hN => hineq N hN t) hhalf
  have hent := cd_plan_entropy_bound_half μ K n ν₀ ν₁ ha0 ha1
    ((integrable_toReal_rnDeriv_mul_iff ha0).mp he0)
    ((integrable_toReal_rnDeriv_mul_iff ha1).mp he1)
    q hpq hd t (fun N hN => hineq N hN t) hhalf
  refine ⟨hac, hent.1, ?_⟩
  simpa only [hInt0, hInt1, hc, boltzmannEntropy] using hent.2

omit [SeparableSpace X] in
 

theorem NoncollapsedRCD.exists_compressed_entropy_midpoint
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤ midpointCapacity K n (2 * R) C₀ • hausdorff n X ∧
      boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ midpointTime)) ≤
        (boltzmannEntropy (hausdorff n X) ν₀ + boltzmannEntropy (hausdorff n X) ν₁) / 2 -
        (K / 8) * (wassersteinSq ν₀ ν₁).toReal := by
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let μ := hausdorff n X
  let B := closedBall p (3 * R)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ, B] using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  obtain ⟨π, hπ, hgπ, hpπ, hcap, hmin⟩ := hX.exists_compressed_entropy_minimizing_midpoint K n hn
    ν₀ ν₁ hC₀ h0 h1 hm0 hm1 p hR hs0 hs1
  let := hπ
  obtain ⟨q, hq, hgq, hpq, hqent⟩ := hX.cd.exists_bounded_support_entropy_plan μ K n
    ν₀ ν₁ hC₀ h0 h1 hm0 hm1 p hR hs0 hs1
  let := hq
  let ν := π.map (fun γ => γ midpointTime)
  let η := q.map (fun γ => γ midpointTime)
  let : IsProbabilityMeasure ν := inferInstance
  let : IsProbabilityMeasure η := inferInstance
  have hνs : ∀ᵐ x ∂ν, x ∈ B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ π hgπ hpπ p hR hs0 hs1).mono fun γ hγ => hγ.2 midpointTime
  have hηs : ∀ᵐ x ∂η, x ∈ B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ q hgq hpq p hR hs0 hs1).mono fun γ hγ => hγ.2 midpointTime
  have hνloc : ν ≤ midpointCapacity K n (2 * R) C₀ • μ.restrict B :=
    (compression_iff_localized _ _ hνs _).mp hcap
  have hνac := Measure.absolutelyContinuous_of_le_smul hνloc
  have hηac : η ≪ μ.restrict B := by
    have hh : η.restrict B ≪ μ.restrict B := (hqent midpointTime).1.restrict B
    rwa [Measure.restrict_eq_self_of_ae_mem hηs] at hh
  have hνfin := klDiv_ne_top_of_bounded_density _ _ (midpointCapacity_ne_top K n (2 * R) hC₀) hνloc
  have hηfin : klDiv η (μ.restrict B) ≠ ∞ := by
    apply klDiv_ne_top hηac
    apply (integrable_toReal_rnDeriv_mul_iff hηac).mp
    exact (entropy_integrable_localized_iff μ η measurableSet_closedBall hηac).mp (hqent midpointTime).2.1
  have hle := ENNReal.toReal_mono hηfin (hmin q hq hgq hpq)
  rw [toReal_klDiv_eq_boltzmannEntropy _ _ hνfin,
    toReal_klDiv_eq_boltzmannEntropy _ _ hηfin,
    ← boltzmannEntropy_localized μ ν measurableSet_closedBall hνac,
    ← boltzmannEntropy_localized μ η measurableSet_closedBall hηac] at hle
  have he : boltzmannEntropy μ ν ≤ boltzmannEntropy μ η := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, sub_le_sub_iff_right, add_le_add_iff_right] using hle
  refine ⟨π, hπ, hgπ, hpπ, hcap, he.trans ?_⟩
  have hqbound := (hqent midpointTime).2.2
  change boltzmannEntropy μ η ≤ _ at hqbound
  convert hqbound using 1 ; (try dsimp only [midpointTime, μ]) ; first | rfl | ring


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

def OptimalPlanDistanceBound (ν₀ ν₁ : Measure X) (D : ℝ) : Prop :=
  ∀ q : Measure C(Time, X), IsProbabilityMeasure q →
    (∀ᵐ γ ∂q, IsGeodesic γ) →
    IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
    ∀ᵐ γ ∂q, dist (γ 0) (γ 1) ≤ D

theorem FullCD.replace_midpoint_region_short (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₀ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (N D : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N)
    (hD : OptimalPlanDistanceBound ν₀ ν₁ D)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (B : Set X) (hB : MeasurableSet B)
    (hm : (π.map (fun γ => γ midpointTime)) B ≠ 0)
    {a : ℝ≥0∞} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∃ π' : Measure C(Time, X), ∃ η : Measure X,
      IsProbabilityMeasure π' ∧ IsFiniteMeasure η ∧
      (∀ᵐ γ ∂π', IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) ∧
      π'.map (fun γ => γ midpointTime) =
        π.map (fun γ => γ midpointTime) - a • (π.map (fun γ => γ midpointTime)).restrict B + η ∧
      η univ = a * (π.map (fun γ => γ midpointTime)) B ∧
      (2 * midpointFloor K N D) ^ N * (π.map (fun γ => γ midpointTime)) B * C₀⁻¹ ≤
        μ {x | η.rnDeriv μ x ≠ 0} := by
  let κ := π.restrict ((fun γ => γ midpointTime) ⁻¹' B)
  have hκ : κ ≤ π := Measure.restrict_le_self
  have hmass : κ univ = (π.map (fun γ => γ midpointTime)) B := by
    rw [Measure.map_apply (measurable_path_eval midpointTime) hB]
    exact Measure.restrict_apply_univ _
  have hκ0 : κ univ ≠ 0 := hmass ▸ hm
  have hκtop : κ univ ≠ ∞ := measure_ne_top κ univ
  let : NeZero κ := ⟨by intro he; exact hκ0 (by rw [he]; rfl)⟩
  let η₀ := (κ univ)⁻¹ • κ.map (fun γ => γ 0)
  let η₁ := (κ univ)⁻¹ • κ.map (fun γ => γ 1)
  have htprob : IsProbabilityMeasure ((κ univ)⁻¹ • κ) := inferInstance
  have he0 : (((κ univ)⁻¹ • κ).map (fun γ => γ 0)) = η₀ := Measure.map_smul _ (measurable_path_eval 0).aemeasurable
  have he1 : (((κ univ)⁻¹ • κ).map (fun γ => γ 1)) = η₁ := Measure.map_smul _ (measurable_path_eval 1).aemeasurable
  have hprob0 : IsProbabilityMeasure η₀ := he0 ▸
    inferInstance
  have hprob1 : IsProbabilityMeasure η₁ := he1 ▸
    inferInstance
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have hle0 : κ.map (fun γ => γ 0) ≤ ν₀ := by
    rw [← hend.1]
    exact Measure.map_mono hκ (measurable_path_eval 0)
  have hle1 : κ.map (fun γ => γ 1) ≤ ν₁ := by
    rw [← hend.2]
    exact Measure.map_mono hκ (measurable_path_eval 1)
  have hden0 : η₀ ≤ (C₀ * (κ univ)⁻¹) • μ := fun S => by
    simpa only [η₀, Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right ((hle0.trans h0) S) (κ univ)⁻¹
  have hden1 : η₁ ≤ (C₀ * (κ univ)⁻¹) • μ := fun S => by
    simpa only [η₁, Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right ((hle1.trans h1) S) (κ univ)⁻¹
  have hi : (κ univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hκ0
  obtain ⟨τ, hτ, hgτ, hpτ, hRenyi⟩ := hcd η₀ η₁ hprob0 hprob1
    (Measure.absolutelyContinuous_of_le_smul hden0)
    (Measure.absolutelyContinuous_of_le_smul hden1)
    ((hm0.of_le hle0).smul hi) ((hm1.of_le hle1).smul hi)
  let := hτ
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top (by simp) ha1
  let q := a * κ univ
  have hq0 : q ≠ 0 := mul_ne_zero ha0.ne' hκ0
  have hqtop : q ≠ ∞ := ENNReal.mul_ne_top hatop hκtop
  have hcancel : q * (κ univ)⁻¹ = a := by
    dsimp only [q]
    rw [mul_assoc, ENNReal.mul_inv_cancel hκ0 hκtop, mul_one]
  have hasub : a • κ ≤ π := by
    calc
      _ ≤ (1 : ℝ≥0∞) • κ := fun S => by
        simpa only [Measure.smul_apply, smul_eq_mul] using mul_le_mul_left ha1 (κ S)
      _ = κ := one_smul _ _
      _ ≤ π := hκ
  have hscaled : IsOptimalCoupling ((a • κ).map (fun γ => γ 0))
      ((a • κ).map (fun γ => γ 1)) ((q • τ).map (fun γ => (γ 0, γ 1))) := by
    have hh := hpτ.smul hq0 hqtop
    simpa only [η₀, η₁, Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_smul _ (measurable_path_eval 1).aemeasurable, Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable, smul_smul, hcancel] using hh
  have hgscaled : ∀ᵐ γ ∂(q • τ), IsGeodesic γ :=
    hgτ.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨hprob', hg', hp'⟩ := optimalPlan_replace_subplan hp hg hasub hscaled hgscaled
  have hDsplice := hD (π - a • κ + q • τ) hprob' hg' hp'
  have hτDscaled : ∀ᵐ γ ∂q • τ, dist (γ 0) (γ 1) ≤ D :=
    hDsplice.filter_mono (Measure.le_add_left le_rfl).absolutelyContinuous.ae_le
  have hτD : ∀ᵐ γ ∂τ, dist (γ 0) (γ 1) ≤ D := hτDscaled.filter_mono (Measure.absolutelyContinuous_smul hq0).ae_le
  let : IsProbabilityMeasure (τ.map (fun γ => γ midpointTime)) :=
    inferInstance
  have hh := (cd_midpoint_renyi_lower μ η₀ η₁ τ hpτ hden0 hden1 K N D hN hτD
    (hRenyi N hnN midpointTime)).trans
    (renyiIntegral_le_ac_support_volume μ (τ.map (fun γ => γ midpointTime)) N hN)
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hvolτ := ENNReal.rpow_le_rpow hh hN0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hN0.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, one_div_mul_cancel hN0.ne', ENNReal.rpow_one] at hvolτ
  have hneg : -(1 / N) * N = -1 := by rw [neg_mul, one_div_mul_cancel hN0.ne']
  rw [hneg, ENNReal.rpow_neg_one] at hvolτ
  let η := (q • τ).map (fun γ => γ midpointTime)
  let : IsFiniteMeasure (q • τ) := ⟨by
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact hqtop.lt_top⟩
  have hκmid : κ.map (fun γ => γ midpointTime) =
      (π.map (fun γ => γ midpointTime)).restrict B :=
    (Measure.restrict_map (measurable_path_eval midpointTime) hB).symm
  refine ⟨π - a • κ + q • τ, η, hprob', inferInstance, hg', hp', ?_, ?_, ?_⟩
  · rw [Measure.map_add _ _ (measurable_path_eval midpointTime),
      map_sub_of_le π (a • κ) hasub _ (measurable_path_eval midpointTime),
      Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable, hκmid]
  · simp only [η, Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply_of_aemeasurable (measurable_path_eval midpointTime).aemeasurable
        MeasurableSet.univ, preimage_univ, measure_univ, mul_one, q, hmass]
  · have hsupport : μ {x | η.rnDeriv μ x ≠ 0} =
        μ {x | (τ.map (fun γ => γ midpointTime)).rnDeriv μ x ≠ 0} := by
      apply measure_congr
      have hr := Measure.rnDeriv_smul_left_of_ne_top
        (τ.map (fun γ => γ midpointTime)) μ hqtop
      change ∀ᵐ x ∂μ, (η.rnDeriv μ x ≠ 0) =
        ((τ.map (fun γ => γ midpointTime)).rnDeriv μ x ≠ 0)
      dsimp only [η]
      rw [Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable]
      filter_upwards [hr] with x hx
      rw [hx, Pi.smul_apply, smul_eq_mul]
      rw [mul_ne_zero_iff]
      apply propext
      exact ⟨And.right, fun h => ⟨hq0, h⟩⟩
    rw [hsupport]
    convert hvolτ using 1
    rw [ENNReal.mul_inv (Or.inr hi) (Or.inl hC₀), inv_inv, hmass]
    ac_rfl

theorem FullCD.improve_localized_saturation_short
    (μ : Measure X) [SigmaFinite μ]
    (W : Set X) (hW : MeasurableSet W) [IsFiniteMeasure (μ.restrict W)]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC : C ≠ ∞) (hCpos : C ≠ 0)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₀ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (N D : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N)
    (hD : OptimalPlanDistanceBound ν₀ ν₁ D)
    (hsupport : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      ∀ᵐ x ∂q.map (fun γ => γ midpointTime), x ∈ W)
    (hfill : C⁻¹ ≤ (2 * midpointFloor K N D) ^ N * C₀⁻¹)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (hpos : transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C ≠ 0)
    (hmin : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
      (∀ᵐ γ ∂π', IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
      transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C ≤
        transportExcessMass (μ.restrict W) (π'.map (fun γ => γ midpointTime)) C) :
    ∃ π' : Measure C(Time, X), IsProbabilityMeasure π' ∧
      (∀ᵐ γ ∂π', IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) ∧
      transportExcessMass (μ.restrict W) (π'.map (fun γ => γ midpointTime)) C =
        transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C ∧
      (μ.restrict W) {x | C < (π.map (fun γ => γ midpointTime)).rnDeriv (μ.restrict W) x} +
        transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C / 2 * C⁻¹ <
      (μ.restrict W) {x | C < (π'.map (fun γ => γ midpointTime)).rnDeriv (μ.restrict W) x} := by
  let ν := π.map (fun γ => γ midpointTime)
  have hvprob : IsProbabilityMeasure ν :=
    inferInstance
  let e := transportExcessMass (μ.restrict W) ν C
  let v := (μ.restrict W) {x | C < ν.rnDeriv (μ.restrict W) x}
  have hetop : e ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top ν univ)
    (transportExcessMass_le (μ.restrict W) ν C)
  obtain ⟨s, hs, hμs, hνs⟩ := (Measure.mutuallySingular_singularPart ν (μ.restrict W)).symm
  have hthreshold : e / 2 + C * v < ν (s ∪ {x | C < ν.rnDeriv (μ.restrict W) x}) := by
    rw [positive_region_mass (μ.restrict W) ν hC hs hμs hνs]
    exact ENNReal.add_lt_add_right
      (ENNReal.mul_ne_top hC (measure_ne_top (μ.restrict W) _)) (ENNReal.half_lt_self hpos hetop)
  obtain ⟨δ, hδ0, hδtop, hδmass⟩ :=
    exists_buffer_positive_region (μ.restrict W) ν hC s hthreshold
  let B := s ∪ {x | C + δ < ν.rnDeriv (μ.restrict W) x}
  have hB : MeasurableSet B := hs.union
    (measurableSet_lt measurable_const (ν.measurable_rnDeriv (μ.restrict W)))
  have hB0 : ν B ≠ 0 := (lt_of_le_of_lt zero_le hδmass).ne'
  let a := δ / (C + δ)
  have ha : a ≤ 1 := ENNReal.div_le_of_le_mul
    (by simp)
  have ha0 : 0 < a := ENNReal.div_pos hδ0.ne' (ENNReal.add_ne_top.mpr ⟨hC, hδtop⟩)
  have hrem : a • ν.restrict B ≤ ν - C • μ.restrict W :=
    buffer_fraction_le_excess (μ.restrict W) ν hC hδ0 hδtop hs hμs
  let : IsFiniteMeasure (a • ν.restrict B) :=
    isFiniteMeasure_of_le ν (hrem.trans Measure.sub_le)
  obtain ⟨π', η, hπ', hη, hg', hp', heq, hmass, hvol⟩ :=
    hcd.replace_midpoint_region_short μ K n ν₀ ν₁ hC₀ h0 h1 hm0 hm1
      N D hnN hN hD π hg hp B hB hB0 ha0 ha
  let := hπ'
  let := hη
  have hηle : η ≤ π'.map (fun γ => γ midpointTime) := by
    rw [heq]
    exact Measure.le_add_left le_rfl
  have hηsupp : ∀ᵐ x ∂η, x ∈ W :=
    (hsupport π' hπ' hg' hp').filter_mono hηle.absolutelyContinuous.ae_le
  have hvolLoc := hvol.trans_eq (ac_support_volume_restrict μ η hW hηsupp)
  have hmin' := hmin π' hπ' hg' hp'
  have hmass' : η univ = (a • ν.restrict B) univ := by
    simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ] using hmass
  have hequal : transportExcessMass (μ.restrict W) (π'.map (fun γ => γ midpointTime)) C = e := by
    apply le_antisymm _ hmin'
    rw [heq]
    exact (transportExcessMass_add_le (μ.restrict W) (ν - a • ν.restrict B) η hC).trans_eq (by
      rw [hmass', transportExcessMass_remove (μ.restrict W) ν (a • ν.restrict B) hC hrem])
  have hsaturated : ∀ᵐ x ∂μ.restrict W, η.rnDeriv (μ.restrict W) x ≠ 0 →
      C < (π'.map (fun γ => γ midpointTime)).rnDeriv (μ.restrict W) x := by
    rw [heq]
    apply ac_support_saturated_of_minimizing_replacement (μ.restrict W) ν (a • ν.restrict B) η
      hC hrem hmass'
    simpa only [heq] using hmin'
  refine ⟨π', hπ', hg', hp', hequal, ?_⟩
  have hgain : v + e / 2 * C⁻¹ < ν B * C⁻¹ := by
    have hh := ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.mpr hC)
      (ENNReal.inv_ne_top.mpr hCpos) hδmass
    convert hh using 1
    rw [add_mul, mul_assoc, mul_comm v, ← mul_assoc, ENNReal.mul_inv_cancel hCpos hC]
    simp only [one_mul, add_comm]
  exact hgain.trans_le (calc
    ν B * C⁻¹ ≤ ν B * ((2 * midpointFloor K N D) ^ N * C₀⁻¹) :=
      mul_le_mul_right hfill _
    _ = (2 * midpointFloor K N D) ^ N * ν B * C₀⁻¹ := by ac_rfl
    _ ≤ (μ.restrict W) {x | η.rnDeriv (μ.restrict W) x ≠ 0} := hvolLoc
    _ ≤ (μ.restrict W) {x | C < (π'.map (fun γ => γ midpointTime)).rnDeriv (μ.restrict W) x} :=
      measure_mono_ae hsaturated)

 

theorem FullCD.localized_excess_minimizer_zero_short
    (μ : Measure X) [SigmaFinite μ]
    (W : Set X) (hW : MeasurableSet W) [IsFiniteMeasure (μ.restrict W)]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC : C ≠ ∞) (hCpos : C ≠ 0)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₀ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (N D : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N)
    (hD : OptimalPlanDistanceBound ν₀ ν₁ D)
    (hsupport : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      ∀ᵐ x ∂q.map (fun γ => γ midpointTime), x ∈ W)
    (hfill : C⁻¹ ≤ (2 * midpointFloor K N D) ^ N * C₀⁻¹)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (hmin : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
      (∀ᵐ γ ∂π', IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
      transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C ≤
        transportExcessMass (μ.restrict W) (π'.map (fun γ => γ midpointTime)) C) :
    transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C = 0 := by
  by_contra hpos
  let e := transportExcessMass (μ.restrict W) (π.map (fun γ => γ midpointTime)) C
  let A := {ρ : Measure C(Time, X) // IsProbabilityMeasure ρ ∧
    (∀ᵐ γ ∂ρ, IsGeodesic γ) ∧
    IsOptimalCoupling ν₀ ν₁ (ρ.map (fun γ => (γ 0, γ 1))) ∧
    transportExcessMass (μ.restrict W) (ρ.map (fun γ => γ midpointTime)) C = e}
  have : Nonempty A := ⟨⟨π, inferInstance, hg, hp, rfl⟩⟩
  let v (ρ : A) := (μ.restrict W) {x | C < (ρ.val.map (fun γ => γ midpointTime)).rnDeriv (μ.restrict W) x}
  let S := ⨆ ρ : A, v ρ
  have hS : S ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top (μ.restrict W) univ)
    (iSup_le fun _ => measure_mono (subset_univ _))
  have hstep : S + e / 2 * C⁻¹ ≤ S := by
    rw [ENNReal.iSup_add]
    apply iSup_le
    intro ρ
    let : IsProbabilityMeasure ρ.val := ρ.property.1
    have hposρ : transportExcessMass (μ.restrict W) (ρ.val.map (fun γ => γ midpointTime)) C ≠ 0 := by
      rw [ρ.property.2.2.2]
      exact hpos
    have hminρ : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
        (∀ᵐ γ ∂π', IsGeodesic γ) →
        IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
        transportExcessMass (μ.restrict W) (ρ.val.map (fun γ => γ midpointTime)) C ≤
          transportExcessMass (μ.restrict W) (π'.map (fun γ => γ midpointTime)) C := by
      intro π' hπ' hg' hp'
      rw [ρ.property.2.2.2]
      exact hmin π' hπ' hg' hp'
    obtain ⟨π', hπ', hg', hp', hequal, hgain⟩ :=
      hcd.improve_localized_saturation_short μ W hW K n ν₀ ν₁
        hC₀ hC hCpos h0 h1 hm0 hm1 N D hnN hN hD hsupport hfill
        ρ.val ρ.property.2.1 ρ.property.2.2.1 hposρ hminρ
    let ρ' : A := ⟨π', hπ', hg', hp', hequal.trans ρ.property.2.2.2⟩
    rw [ρ.property.2.2.2] at hgain
    exact hgain.le.trans (le_iSup v ρ')
  have hδ : 0 < e / 2 * C⁻¹ := ENNReal.mul_pos
    (ENNReal.div_pos hpos (by simp)).ne' (ENNReal.inv_ne_zero.mpr hC)
  have hstrict := ENNReal.add_lt_add_left hS hδ
  rw [add_zero] at hstrict
  exact (not_lt_of_ge hstep) hstrict

section
variable [ProperSpace X] [SeparableSpace X]
theorem FullCD.exists_compressed_midpoint_at_capacity_short
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC : C ≠ ∞) (hCpos : C ≠ 0)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₀ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    [IsFiniteMeasure (μ.restrict (closedBall p (3 * R)))]
    [Measure.OuterRegular (μ.restrict (closedBall p (3 * R)))]
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (N D : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N)
    (hD : OptimalPlanDistanceBound ν₀ ν₁ D)
    (hfill : C⁻¹ ≤ (2 * midpointFloor K N D) ^ N * C₀⁻¹) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤ C • μ := by
  let W := closedBall p (3 * R)
  have hW : MeasurableSet W := isClosed_closedBall.measurableSet
  have hsupport : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      ∀ᵐ x ∂q.map (fun γ => γ midpointTime), x ∈ W := by
    intro q hq hgq hpq
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable hW).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ q hgq hpq p hR hs0 hs1).mono
      (fun γ hγ => hγ.2 midpointTime)
  let v0 : ProbabilityMeasure X := ⟨ν₀, inferInstance⟩
  let v1 : ProbabilityMeasure X := ⟨ν₁, inferInstance⟩
  obtain ⟨q, hq, hgq, hpq, _⟩ := hcd ν₀ ν₁ inferInstance inferInstance
    (Measure.absolutelyContinuous_of_le_smul h0)
    (Measure.absolutelyContinuous_of_le_smul h1) hm0 hm1
  have hne : (OptimalGeodesicPlans v0 v1).Nonempty := ⟨⟨q, hq⟩, hgq, hpq⟩
  obtain ⟨π, hπ, hmπ⟩ := exists_optimal_geodesic_plan_minimizing_excess
    (μ.restrict W) v0 v1 p hR hs0 hs1 hne midpointTime hC
  have hmin : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      transportExcessMass (μ.restrict W) ((π : Measure C(Time, X)).map (fun γ => γ midpointTime)) C ≤
        transportExcessMass (μ.restrict W) (q.map (fun γ => γ midpointTime)) C := by
    intro q hq hgq hpq
    exact hmπ ⟨q, hq⟩ ⟨hgq, hpq⟩
  have hz := hcd.localized_excess_minimizer_zero_short μ W hW K n ν₀ ν₁ hC₀ hC hCpos
    h0 h1 hm0 hm1 N D hnN hN hD
    hsupport hfill (π : Measure C(Time, X)) hπ.1 hπ.2 hmin
  refine ⟨π, inferInstance, hπ.1, hπ.2, ?_⟩
  have hs := hsupport (π : Measure C(Time, X)) inferInstance hπ.1 hπ.2
  have ht := localized_excess_zero_iff μ ((π : Measure C(Time, X)).map (fun γ => γ midpointTime))
    (B := W) (C := C) hs hC
  exact ht.mp hz
end

theorem NoncollapsedRCD.exists_compressed_midpoint_short (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (D : ℝ) (hD : OptimalPlanDistanceBound ν₀ ν₁ D) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤
        midpointCapacity K n D C₀ • hausdorff n X := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let : IsFiniteMeasure ((hausdorff n X).restrict (closedBall p (3 * R))) :=
    ⟨by simpa using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  have hCpos := probability_capacity_ne_zero _ _ h0
  apply hX.cd.exists_compressed_midpoint_at_capacity_short (hausdorff n X) K n ν₀ ν₁
    hC₀ (midpointCapacity_ne_top K n D hC₀)
    (midpointCapacity_pos K n D hCpos).ne' h0 h1 hm0 hm1 p hR hs0 hs1
    (n : ℝ) D le_rfl
  · exact_mod_cast (show 1 < n by omega)
  · exact hD
  · exact (midpointCapacity_fill K n D C₀).le


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
open InformationTheory
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem OptimalPlanDistanceBound.normalized_subplan {ν₀ ν₁ : Measure X}
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] {D : ℝ}
    (hD : OptimalPlanDistanceBound ν₀ ν₁ D)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (κ : Measure C(Time, X)) (hκ : κ ≤ π) (hκ0 : κ univ ≠ 0) :
    OptimalPlanDistanceBound ((κ univ)⁻¹ • κ.map (fun γ => γ 0))
      ((κ univ)⁻¹ • κ.map (fun γ => γ 1)) D := by
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have hκtop : κ univ ≠ ∞ := measure_ne_top κ univ
  intro q hq hgq hpq
  let := hq
  have hscaled : IsOptimalCoupling (κ.map (fun γ => γ 0)) (κ.map (fun γ => γ 1))
      ((κ univ • q).map (fun γ => (γ 0, γ 1))) := by
    have hh := hpq.smul hκ0 hκtop
    simpa only [Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable, smul_smul, ENNReal.mul_inv_cancel hκ0 hκtop,
      one_smul] using hh
  have hgscaled : ∀ᵐ γ ∂κ univ • q, IsGeodesic γ :=
    hgq.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨hprob, hg', hp'⟩ := optimalPlan_replace_subplan hp hg hκ hscaled hgscaled
  have hdist := hD (π - κ + κ univ • q) hprob hg' hp'
  have hdist' : ∀ᵐ γ ∂κ univ • q, dist (γ 0) (γ 1) ≤ D :=
    hdist.filter_mono (Measure.le_add_left le_rfl).absolutelyContinuous.ae_le
  exact hdist'.filter_mono (Measure.absolutelyContinuous_smul hκ0).ae_le

theorem NoncollapsedRCD.compressed_replacement_subplan_short
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (D : ℝ) (hD : OptimalPlanDistanceBound ν₀ ν₁ D)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (B : Set X) (hB : MeasurableSet B)
    (hm : (π.map (fun γ => γ midpointTime)) B ≠ 0) :
    ∃ σ : Measure C(Time, X), IsFiniteMeasure σ ∧
      (∀ᵐ γ ∂σ, IsGeodesic γ) ∧
      IsOptimalCoupling
        ((π.restrict ((fun γ => γ midpointTime) ⁻¹' B)).map (fun γ => γ 0))
        ((π.restrict ((fun γ => γ midpointTime) ⁻¹' B)).map (fun γ => γ 1))
        (σ.map (fun γ => (γ 0, γ 1))) ∧
      (σ.map (fun γ => γ midpointTime)) univ = (π.map (fun γ => γ midpointTime)) B ∧
      σ.map (fun γ => γ midpointTime) ≤ midpointCapacity K n D C₀ •
        (hausdorff n X).restrict (closedBall p (3 * R)) := by
  let : SeparableSpace X := hX.separable
  let κ := π.restrict ((fun γ => γ midpointTime) ⁻¹' B)
  have hκ : κ ≤ π := Measure.restrict_le_self
  have hmass : κ univ = (π.map (fun γ => γ midpointTime)) B := by
    rw [Measure.map_apply (measurable_path_eval midpointTime) hB]
    exact Measure.restrict_apply_univ _
  have hκ0 : κ univ ≠ 0 := hmass ▸ hm
  have hκtop : κ univ ≠ ∞ := measure_ne_top κ univ
  let : NeZero κ := ⟨by intro he; exact hκ0 (by rw [he]; rfl)⟩
  let η₀ := (κ univ)⁻¹ • κ.map (fun γ => γ 0)
  let η₁ := (κ univ)⁻¹ • κ.map (fun γ => γ 1)
  have htprob : IsProbabilityMeasure ((κ univ)⁻¹ • κ) := inferInstance
  have he0 : (((κ univ)⁻¹ • κ).map (fun γ => γ 0)) = η₀ := Measure.map_smul _ (measurable_path_eval 0).aemeasurable
  have he1 : (((κ univ)⁻¹ • κ).map (fun γ => γ 1)) = η₁ := Measure.map_smul _ (measurable_path_eval 1).aemeasurable
  have hprob0 : IsProbabilityMeasure η₀ := he0 ▸
    inferInstance
  have hprob1 : IsProbabilityMeasure η₁ := he1 ▸
    inferInstance
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have hle0 : κ.map (fun γ => γ 0) ≤ ν₀ := by
    rw [← hend.1]
    exact Measure.map_mono hκ (measurable_path_eval 0)
  have hle1 : κ.map (fun γ => γ 1) ≤ ν₁ := by
    rw [← hend.2]
    exact Measure.map_mono hκ (measurable_path_eval 1)
  have hden0 : η₀ ≤ (C₀ * (κ univ)⁻¹) • hausdorff n X := fun S => by
    simpa only [η₀, Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right ((hle0.trans h0) S) (κ univ)⁻¹
  have hden1 : η₁ ≤ (C₀ * (κ univ)⁻¹) • hausdorff n X := fun S => by
    simpa only [η₁, Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right ((hle1.trans h1) S) (κ univ)⁻¹
  have hi : (κ univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hκ0
  have hk0 : ∀ᵐ x ∂κ.map (fun γ => γ 0), dist x p ≤ R :=
    hs0.filter_mono hle0.absolutelyContinuous.ae_le
  have hk1 : ∀ᵐ x ∂κ.map (fun γ => γ 1), dist x p ≤ R :=
    hs1.filter_mono hle1.absolutelyContinuous.ae_le
  have hs0' : ∀ᵐ x ∂η₀, dist x p ≤ R :=
    hk0.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hs1' : ∀ᵐ x ∂η₁, dist x p ≤ R :=
    hk1.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨τ, hτ, hgτ, hpτ, hcapτ⟩ := hX.exists_compressed_midpoint_short K n hn η₀ η₁
    (ENNReal.mul_ne_top hC₀ hi) hden0 hden1
    ((hm0.of_le hle0).smul hi) ((hm1.of_le hle1).smul hi) p hR hs0' hs1' D (hD.normalized_subplan π hg hp κ hκ hκ0)
  let := hτ
  let σ := κ univ • τ
  let : IsFiniteMeasure σ := Measure.smul_finite _ hκtop
  have hscaled : IsOptimalCoupling (κ.map (fun γ => γ 0)) (κ.map (fun γ => γ 1))
      (σ.map (fun γ => (γ 0, γ 1))) := by
    have hh := hpτ.smul hκ0 hκtop
    simpa only [σ, η₀, η₁, Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable, smul_smul,
      ENNReal.mul_inv_cancel hκ0 hκtop, one_smul] using hh
  have hgσ : ∀ᵐ γ ∂σ, IsGeodesic γ :=
    hgτ.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hσcap : σ.map (fun γ => γ midpointTime) ≤
      midpointCapacity K n D C₀ • hausdorff n X := by
    rw [show σ = κ univ • τ from rfl, Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable]
    have hmul : κ univ * midpointCapacity K n D (C₀ * (κ univ)⁻¹) =
        midpointCapacity K n D C₀ := by
      dsimp only [midpointCapacity]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        _ = C₀ * ((κ univ) * (κ univ)⁻¹) * ((2 * midpointFloor K n D) ^ (n : ℝ))⁻¹ := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel hκ0 hκtop, mul_one]
    calc
      _ ≤ κ univ • (midpointCapacity K n D (C₀ * (κ univ)⁻¹) • hausdorff n X) :=
        fun S => by
          simpa only [Measure.smul_apply, smul_eq_mul, mul_comm] using
            mul_le_mul_left (hcapτ S) (κ univ)
      _ = _ := by rw [smul_smul, hmul]
  have hσsupport : ∀ᵐ x ∂σ.map (fun γ => γ midpointTime), x ∈ closedBall p (3 * R) := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ σ hgσ hscaled p hR hk0 hk1).mono
      (fun γ hγ => hγ.2 midpointTime)
  refine ⟨σ, inferInstance, hgσ, hscaled, ?_,
    (compression_iff_localized _ _ hσsupport _).mp hσcap⟩
  simp only [σ, Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply_of_aemeasurable (measurable_path_eval midpointTime).aemeasurable
      MeasurableSet.univ, preimage_univ, measure_univ, mul_one, hmass]

theorem NoncollapsedRCD.entropy_minimizer_compressed_short
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (D : ℝ) (hD : OptimalPlanDistanceBound ν₀ ν₁ D)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (hfin : klDiv (π.map (fun γ => γ midpointTime))
      ((hausdorff n X).restrict (closedBall p (3 * R))) ≠ ∞)
    (hmin : ∀ q : Measure C(Time, X), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      klDiv (π.map (fun γ => γ midpointTime)) ((hausdorff n X).restrict (closedBall p (3 * R))) ≤
      klDiv (q.map (fun γ => γ midpointTime)) ((hausdorff n X).restrict (closedBall p (3 * R)))) :
    π.map (fun γ => γ midpointTime) ≤ midpointCapacity K n D C₀ • hausdorff n X := by
  let : SeparableSpace X := hX.separable
  let μ := (hausdorff n X).restrict (closedBall p (3 * R))
  let : IsFiniteMeasure μ := ⟨by
    simpa [μ] using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  let ν := π.map (fun γ => γ midpointTime)
  let C := midpointCapacity K n D C₀
  have hCtop : C ≠ ∞ := midpointCapacity_ne_top K n D hC₀
  have hC0 : C ≠ 0 := (midpointCapacity_pos K n D (probability_capacity_ne_zero _ _ h0)).ne'
  have hCreal : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  have hCe : ENNReal.ofReal C.toReal = C := ENNReal.ofReal_toReal hCtop
  have hsupport : ∀ᵐ x ∂ν, x ∈ closedBall p (3 * R) := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ π hg hp p hR hs0 hs1).mono
      (fun γ hγ => hγ.2 midpointTime)
  by_contra hbad
  have hbad' : ¬ ν ≤ ENNReal.ofReal C.toReal • μ := by
    rw [hCe]
    exact fun h => hbad ((compression_iff_localized _ _ hsupport C).mpr h)
  let B := {x | C.toReal < (ν.rnDeriv μ x).toReal}
  have hB : MeasurableSet B := measurableSet_lt measurable_const (ν.measurable_rnDeriv μ).ennreal_toReal
  have hm : ν B ≠ 0 := superlevel_mass_ne_zero_of_not_compressed μ ν
    (klDiv_ne_top_iff.mp hfin).1 hCreal hbad'
  obtain ⟨σ, hσfin, hgσ, hpσ, hmσ, hcapσ⟩ := hX.compressed_replacement_subplan_short K n hn
    ν₀ ν₁ hC₀ h0 h1 hm0 hm1 p hR hs0 hs1 D hD π hg hp B hB hm
  let := hσfin
  let η := σ.map (fun γ => γ midpointTime)
  obtain ⟨a, ha0, ha1, hdrop⟩ := exists_measure_entropy_decrease μ ν η hCreal hfin
    (by simpa only [hCe] using hcapσ) hmσ hbad'
  let κ := π.restrict ((fun γ => γ midpointTime) ⁻¹' B)
  have hκ : κ ≤ π := Measure.restrict_le_self
  have haE : ENNReal.ofReal a ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal ha1.le
  have hsub : ENNReal.ofReal a • κ ≤ π := by
    calc
      _ ≤ (1 : ℝ≥0∞) • κ := fun S => by
        simpa only [Measure.smul_apply, smul_eq_mul] using mul_le_mul_left haE (κ S)
      _ = κ := one_smul _ _
      _ ≤ π := hκ
  have hs : IsOptimalCoupling ((ENNReal.ofReal a • κ).map (fun γ => γ 0))
      ((ENNReal.ofReal a • κ).map (fun γ => γ 1))
      ((ENNReal.ofReal a • σ).map (fun γ => (γ 0, γ 1))) := by
    simpa only [Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_smul _ (measurable_path_eval 1).aemeasurable, Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable] using hpσ.smul (ENNReal.ofReal_pos.mpr ha0).ne' ENNReal.ofReal_ne_top
  have hgs : ∀ᵐ γ ∂(ENNReal.ofReal a • σ), IsGeodesic γ :=
    hgσ.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨hq, hgq, hpq⟩ := optimalPlan_replace_subplan hp hg hsub hs hgs
  have hle := hmin _ hq hgq hpq
  have hκmid : κ.map (fun γ => γ midpointTime) = ν.restrict B :=
    (Measure.restrict_map (measurable_path_eval midpointTime) hB).symm
  rw [Measure.map_add _ _ (measurable_path_eval midpointTime),
    map_sub_of_le π (ENNReal.ofReal a • κ) hsub _ (measurable_path_eval midpointTime),
    Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable, Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable, hκmid] at hle
  exact (not_lt_of_ge hle) hdrop

 

theorem NoncollapsedRCD.exists_compressed_entropy_minimizing_midpoint_short
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (D : ℝ) (hD : OptimalPlanDistanceBound ν₀ ν₁ D) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤ midpointCapacity K n D C₀ • hausdorff n X ∧
      ∀ q : Measure C(Time, X), IsProbabilityMeasure q →
        (∀ᵐ γ ∂q, IsGeodesic γ) →
        IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
        klDiv (π.map (fun γ => γ midpointTime)) ((hausdorff n X).restrict (closedBall p (3 * R))) ≤
        klDiv (q.map (fun γ => γ midpointTime)) ((hausdorff n X).restrict (closedBall p (3 * R))) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := (hausdorff n X).restrict (closedBall p (3 * R))
  let : IsFiniteMeasure μ := ⟨by
    simpa [μ] using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  let v0 : ProbabilityMeasure X := ⟨ν₀, inferInstance⟩
  let v1 : ProbabilityMeasure X := ⟨ν₁, inferInstance⟩
  obtain ⟨q, hq, hgq, hpq, hqcap⟩ := hX.exists_compressed_midpoint_short K n hn ν₀ ν₁
    hC₀ h0 h1 hm0 hm1 p hR hs0 hs1 D hD
  let := hq
  have hne : (OptimalGeodesicPlans v0 v1).Nonempty := ⟨⟨q, hq⟩, hgq, hpq⟩
  obtain ⟨π, hπ, hmπ⟩ := exists_optimal_geodesic_plan_minimizing_entropy μ v0 v1 p hR hs0 hs1 hne midpointTime
  have hmin : ∀ q' : Measure C(Time, X), IsProbabilityMeasure q' →
      (∀ᵐ γ ∂q', IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q'.map (fun γ => (γ 0, γ 1))) →
      klDiv ((π : Measure C(Time, X)).map (fun γ => γ midpointTime)) μ ≤
      klDiv (q'.map (fun γ => γ midpointTime)) μ := by
    intro q' hq' hgq' hpq'
    exact hmπ ⟨q', hq'⟩ ⟨hgq', hpq'⟩
  have hqS : ∀ᵐ x ∂q.map (fun γ => γ midpointTime), x ∈ closedBall p (3 * R) := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ q hgq hpq p hR hs0 hs1).mono
      (fun γ hγ => hγ.2 midpointTime)
  have hqcap' := (compression_iff_localized _ _ hqS _).mp hqcap
  have hqfin := klDiv_ne_top_of_bounded_density μ (q.map (fun γ => γ midpointTime))
    (midpointCapacity_ne_top K n D hC₀) hqcap'
  have hfin : klDiv ((π : Measure C(Time, X)).map (fun γ => γ midpointTime)) μ ≠ ∞ :=
    ne_top_of_le_ne_top hqfin (hmin q hq hgq hpq)
  refine ⟨π, inferInstance, hπ.1, hπ.2,
    hX.entropy_minimizer_compressed_short K n hn ν₀ ν₁ hC₀ h0 h1 hm0 hm1 p hR hs0 hs1 D hD
      (π : Measure C(Time, X)) hπ.1 hπ.2 hfin hmin, hmin⟩

theorem NoncollapsedRCD.exists_compressed_entropy_midpoint_short
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (D : ℝ) (hD : OptimalPlanDistanceBound ν₀ ν₁ D) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤ midpointCapacity K n D C₀ • hausdorff n X ∧
      boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ midpointTime)) ≤
        (boltzmannEntropy (hausdorff n X) ν₀ + boltzmannEntropy (hausdorff n X) ν₁) / 2 -
        (K / 8) * (wassersteinSq ν₀ ν₁).toReal := by
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let μ := hausdorff n X
  let B := closedBall p (3 * R)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ, B] using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  obtain ⟨π, hπ, hgπ, hpπ, hcap, hmin⟩ := hX.exists_compressed_entropy_minimizing_midpoint_short K n hn
    ν₀ ν₁ hC₀ h0 h1 hm0 hm1 p hR hs0 hs1 D hD
  let := hπ
  obtain ⟨q, hq, hgq, hpq, hqent⟩ := hX.cd.exists_bounded_support_entropy_plan μ K n
    ν₀ ν₁ hC₀ h0 h1 hm0 hm1 p hR hs0 hs1
  let := hq
  let ν := π.map (fun γ => γ midpointTime)
  let η := q.map (fun γ => γ midpointTime)
  let : IsProbabilityMeasure ν := inferInstance
  let : IsProbabilityMeasure η := inferInstance
  have hνs : ∀ᵐ x ∂ν, x ∈ B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ π hgπ hpπ p hR hs0 hs1).mono fun γ hγ => hγ.2 midpointTime
  have hηs : ∀ᵐ x ∂η, x ∈ B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ q hgq hpq p hR hs0 hs1).mono fun γ hγ => hγ.2 midpointTime
  have hνloc : ν ≤ midpointCapacity K n D C₀ • μ.restrict B :=
    (compression_iff_localized _ _ hνs _).mp hcap
  have hνac := Measure.absolutelyContinuous_of_le_smul hνloc
  have hηac : η ≪ μ.restrict B := by
    have hh : η.restrict B ≪ μ.restrict B := (hqent midpointTime).1.restrict B
    rwa [Measure.restrict_eq_self_of_ae_mem hηs] at hh
  have hνfin := klDiv_ne_top_of_bounded_density _ _ (midpointCapacity_ne_top K n D hC₀) hνloc
  have hηfin : klDiv η (μ.restrict B) ≠ ∞ := by
    apply klDiv_ne_top hηac
    apply (integrable_toReal_rnDeriv_mul_iff hηac).mp
    exact (entropy_integrable_localized_iff μ η measurableSet_closedBall hηac).mp (hqent midpointTime).2.1
  have hle := ENNReal.toReal_mono hηfin (hmin q hq hgq hpq)
  rw [toReal_klDiv_eq_boltzmannEntropy _ _ hνfin,
    toReal_klDiv_eq_boltzmannEntropy _ _ hηfin,
    ← boltzmannEntropy_localized μ ν measurableSet_closedBall hνac,
    ← boltzmannEntropy_localized μ η measurableSet_closedBall hηac] at hle
  have he : boltzmannEntropy μ ν ≤ boltzmannEntropy μ η := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, sub_le_sub_iff_right, add_le_add_iff_right] using hle
  refine ⟨π, hπ, hgπ, hpπ, hcap, he.trans ?_⟩
  have hqbound := (hqent midpointTime).2.2
  change boltzmannEntropy μ η ≤ _ at hqbound
  convert hqbound using 1 ; (try dsimp only [midpointTime, μ]) ; first | rfl | ring


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal

variable {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
  [StandardBorelSpace B] [Nonempty B] [MeasurableEq Z]

theorem exists_coupling_common_map (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : A → Z) (g : B → Z) (hf : Measurable f) (hg : Measurable g)
    (heq : μ.map f = ν.map g) :
    ∃ ζ : Measure (A × B), IsFiniteMeasure ζ ∧ ζ.map Prod.fst = μ ∧
      ζ.map Prod.snd = ν ∧ ∀ᵐ z ∂ζ, f z.1 = g z.2 := by
  let π := μ.map (fun x => (x, f x))
  let κ := ν.map (fun y => (g y, y))
  have hπ : π.map Prod.snd = μ.map f := by
    dsimp only [π]
    rw [Measure.map_map measurable_snd (measurable_id'.prodMk hf)]
    rfl
  have hκ : κ.map Prod.fst = ν.map g := by
    dsimp only [κ]
    rw [Measure.map_map measurable_fst (hg.prodMk measurable_id')]
    rfl
  obtain ⟨ρ, hρ, hρ0, hρ1⟩ := exists_glued_measure π κ (hπ.trans (heq.trans hκ.symm))
  let := hρ
  let ζ := ρ.map (fun z => (z.1.1, z.2))
  have hζ0 : ζ.map Prod.fst = μ := by
    dsimp only [ζ]
    rw [Measure.map_map measurable_fst (measurable_fst.fst.prodMk measurable_snd)]
    have hh := congrArg (fun m : Measure (A × Z) => m.map Prod.fst) hρ0
    dsimp only [π] at hh
    rw [Measure.map_map measurable_fst measurable_fst,
      Measure.map_map measurable_fst (measurable_id'.prodMk hf)] at hh
    simpa only [Function.comp_def, Measure.map_id'] using hh
  have hζ1 : ζ.map Prod.snd = ν := by
    dsimp only [ζ]
    rw [Measure.map_map measurable_snd (measurable_fst.fst.prodMk measurable_snd)]
    have hh := congrArg (fun m : Measure (Z × B) => m.map Prod.snd) hρ1
    dsimp only [κ] at hh
    rw [Measure.map_map measurable_snd (measurable_fst.snd.prodMk measurable_snd),
      Measure.map_map measurable_snd (hg.prodMk measurable_id')] at hh
    simpa only [Function.comp_def, Measure.map_id'] using hh
  have ha : ∀ᵐ z ∂π, f z.1 = z.2 := by
    apply ae_map_iff (measurable_id'.prodMk hf).aemeasurable
      (measurableSet_eq_fun (hf.comp measurable_fst) measurable_snd) |>.mpr
    exact Filter.Eventually.of_forall fun _ => rfl
  have hb : ∀ᵐ z ∂κ, z.1 = g z.2 := by
    apply ae_map_iff (hg.prodMk measurable_id').aemeasurable
      (measurableSet_eq_fun measurable_fst (hg.comp measurable_snd)) |>.mpr
    exact Filter.Eventually.of_forall fun _ => rfl
  have ha' : ∀ᵐ z ∂ρ, f z.1.1 = z.1.2 := by
    apply ae_of_ae_map measurable_fst.aemeasurable (p := fun z : A × Z => f z.1 = z.2)
    rwa [hρ0]
  have hb' : ∀ᵐ z ∂ρ, z.1.2 = g z.2 := by
    apply ae_of_ae_map (measurable_fst.snd.prodMk measurable_snd).aemeasurable (p := fun z : Z × B => z.1 = g z.2)
    rwa [hρ1]
  refine ⟨ζ, inferInstance, hζ0, hζ1, ?_⟩
  apply (ae_map_iff (measurable_fst.fst.prodMk measurable_snd).aemeasurable
    (measurableSet_eq_fun (hf.comp measurable_fst) (hg.comp measurable_snd))).mpr
  filter_upwards [ha', hb'] with z hz1 hz2
  exact hz1.trans hz2


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X]

abbrev MatchedPaths (X : Type*) [MetricSpace X] :=
  {z : C(Time, X) × C(Time, X) // z.1 1 = z.2 0}

noncomputable def leftHalfTime (t : Time) : Time := projIcc 0 1 zero_le_one (2 * (t : ℝ))
noncomputable def rightHalfTime (t : Time) : Time := projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)

theorem continuous_leftHalfTime : Continuous leftHalfTime :=
  continuous_projIcc.comp (continuous_const.mul continuous_subtype_val)
theorem continuous_rightHalfTime : Continuous rightHalfTime :=
  continuous_projIcc.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)

@[simp] theorem leftHalfTime_zero : leftHalfTime 0 = 0 := by simp [leftHalfTime]
@[simp] theorem rightHalfTime_one : rightHalfTime 1 = 1 := by norm_num [rightHalfTime]
@[simp] theorem leftHalfTime_midpoint : leftHalfTime midpointTime = 1 := by
  norm_num [leftHalfTime, midpointTime]
@[simp] theorem rightHalfTime_midpoint : rightHalfTime midpointTime = 0 := by
  norm_num [rightHalfTime, midpointTime]

theorem leftHalfTime_coe (t : Time) (ht : (t : ℝ) ≤ 1 / 2) :
    (leftHalfTime t : ℝ) = 2 * (t : ℝ) := by
  rw [leftHalfTime, projIcc_of_mem zero_le_one ⟨by linarith [t.property.1], by linarith⟩]

theorem rightHalfTime_coe (t : Time) (ht : 1 / 2 ≤ (t : ℝ)) :
    (rightHalfTime t : ℝ) = 2 * (t : ℝ) - 1 := by
  rw [rightHalfTime, projIcc_of_mem zero_le_one ⟨by linarith, by linarith [t.property.2]⟩]

noncomputable def joinMatched (z : MatchedPaths X) : C(Time, X) where
  toFun t := if (t : ℝ) ≤ 1 / 2 then z.val.1 (leftHalfTime t) else z.val.2 (rightHalfTime t)
  continuous_toFun := by
    apply Continuous.if_le (z.val.1.continuous.comp continuous_leftHalfTime)
      (z.val.2.continuous.comp continuous_rightHalfTime) continuous_subtype_val continuous_const
    intro t ht
    have he : t = midpointTime := Subtype.ext ht
    subst t
    simpa using z.property

theorem joinMatched_continuous : Continuous (joinMatched (X := X)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : MatchedPaths X × Time =>
    if (z.2 : ℝ) ≤ 1 / 2 then z.1.val.1 (leftHalfTime z.2) else z.1.val.2 (rightHalfTime z.2))
  apply Continuous.if_le
    (continuous_eval.comp (((continuous_subtype_val.comp continuous_fst).fst).prodMk
      (continuous_leftHalfTime.comp continuous_snd)))
    (continuous_eval.comp (((continuous_subtype_val.comp continuous_fst).snd).prodMk
      (continuous_rightHalfTime.comp continuous_snd)))
    (continuous_subtype_val.comp continuous_snd) continuous_const
  intro z hz
  have he : z.2 = midpointTime := Subtype.ext hz
  change z.1.val.1 (leftHalfTime z.2) = z.1.val.2 (rightHalfTime z.2)
  rw [he, leftHalfTime_midpoint, rightHalfTime_midpoint]
  exact z.1.property

@[simp] theorem joinMatched_zero (z : MatchedPaths X) : joinMatched z 0 = z.val.1 0 := by
  simp [joinMatched]
@[simp] theorem joinMatched_one (z : MatchedPaths X) : joinMatched z 1 = z.val.2 1 := by
  norm_num [joinMatched]
@[simp] theorem joinMatched_midpoint (z : MatchedPaths X) :
    joinMatched z midpointTime = z.val.1 1 := by
  simp [joinMatched]

theorem joinMatched_apply_left (z : MatchedPaths X) (t : Time) (ht : (t : ℝ) ≤ 1 / 2) :
    joinMatched z t = z.val.1 (leftHalfTime t) := ite_eq_left ht

theorem joinMatched_apply_right (z : MatchedPaths X) (t : Time) (ht : 1 / 2 ≤ (t : ℝ)) :
    joinMatched z t = z.val.2 (rightHalfTime t) := by
  rcases eq_or_lt_of_le ht with he | he
  · have ht : t = midpointTime := Subtype.ext he.symm
    subst t
    simpa using z.property
  · exact ite_eq_right (not_le.mpr he)

 
theorem isGeodesic_of_dist_le (γ : C(Time, X))
    (h : ∀ s t : Time, dist (γ s) (γ t) ≤ |(s : ℝ) - (t : ℝ)| * dist (γ 0) (γ 1)) :
    IsGeodesic γ := by
  suffices hh : ∀ s t : Time, s ≤ t → dist (γ s) (γ t) =
      ((t : ℝ) - (s : ℝ)) * dist (γ 0) (γ 1) by
    intro s t
    rcases le_total s t with hst | hts
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from hst))]
      exact hh s t hst
    · rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ (s : ℝ) from hts))]
      exact hh t s hts
  intro s t hst
  change (s : ℝ) ≤ (t : ℝ) at hst
  have hup := h s t
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from hst))] at hup
  have h0 := h 0 s
  have h1 := h t 1
  change dist (γ 0) (γ s) ≤ |0 - (s : ℝ)| * dist (γ 0) (γ 1) at h0
  change dist (γ t) (γ 1) ≤ |(t : ℝ) - 1| * dist (γ 0) (γ 1) at h1
  rw [zero_sub, abs_neg, abs_of_nonneg s.property.1] at h0
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr t.property.2)] at h1
  have htri := (dist_triangle (γ 0) (γ s) (γ 1)).trans
    (add_le_add le_rfl (dist_triangle (γ s) (γ t) (γ 1)))
  nlinarith

 

theorem joinMatched_isGeodesic (z : MatchedPaths X)
    (h0 : IsGeodesic z.val.1) (h1 : IsGeodesic z.val.2)
    (hlen : dist (z.val.1 0) (z.val.1 1) = dist (z.val.2 0) (z.val.2 1))
    (hstraight : dist (z.val.1 0) (z.val.2 1) = 2 * dist (z.val.1 0) (z.val.1 1)) :
    IsGeodesic (joinMatched z) := by
  apply isGeodesic_of_dist_le
  suffices hh : ∀ s t : Time, s ≤ t → dist (joinMatched z s) (joinMatched z t) ≤
      ((t : ℝ) - (s : ℝ)) * dist (joinMatched z 0) (joinMatched z 1) by
    intro s t
    rcases le_total s t with hst | hts
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from hst))]
      exact hh s t hst
    · rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ (s : ℝ) from hts))]
      exact hh t s hts
  intro s t hst
  change (s : ℝ) ≤ (t : ℝ) at hst
  rw [joinMatched_zero, joinMatched_one, hstraight]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · have hs : (s : ℝ) ≤ 1 / 2 := le_trans hst ht
    rw [joinMatched_apply_left z s hs, joinMatched_apply_left z t ht, h0,
      leftHalfTime_coe s hs, leftHalfTime_coe t ht,
      abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ 2 * (t : ℝ) - 2 * (s : ℝ))]
    nlinarith
  · by_cases hs : 1 / 2 ≤ (s : ℝ)
    · have ht' : 1 / 2 ≤ (t : ℝ) := le_trans hs hst
      rw [joinMatched_apply_right z s hs, joinMatched_apply_right z t ht', h1,
        rightHalfTime_coe s hs, rightHalfTime_coe t ht', ← hlen,
        abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ (2 * (t : ℝ) - 1) - (2 * (s : ℝ) - 1))]
      nlinarith
    · have hs' : (s : ℝ) ≤ 1 / 2 := (lt_of_not_ge hs).le
      have ht' : 1 / 2 ≤ (t : ℝ) := (lt_of_not_ge ht).le
      rw [joinMatched_apply_left z s hs', joinMatched_apply_right z t ht']
      have hz := dist_triangle (z.val.1 (leftHalfTime s)) (z.val.1 1) (z.val.2 (rightHalfTime t))
      rw [z.property, h1 0 _, ← hlen] at hz
      have hw := h0 (leftHalfTime s) 1
      rw [leftHalfTime_coe s hs'] at hw
      rw [← z.property] at hz
      rw [hw, rightHalfTime_coe t ht'] at hz
      norm_num only [show ((0 : Time) : ℝ) = 0 from rfl, show ((1 : Time) : ℝ) = 1 from rfl, zero_sub, abs_neg] at hz
      rw [abs_of_nonpos (by linarith : 2 * (s : ℝ) - 1 ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ 2 * (t : ℝ) - 1)] at hz
      nlinarith


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem transportCost_plan_lintegral (π : Measure C(Time, X)) (s t : Time) :
    transportCost (π.map (fun γ => (γ s, γ t))) =
      ∫⁻ γ, ENNReal.ofReal (dist (γ s) (γ t)) ^ 2 ∂π := by
  rw [transportCost, lintegral_map
    ((measurable_fst.dist measurable_snd).ennreal_ofReal.pow_const 2)
    ((measurable_path_eval s).prodMk (measurable_path_eval t))]

theorem geodesic_plan_cost (π : Measure C(Time, X))
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ) (s t : Time) :
    transportCost (π.map (fun γ => (γ s, γ t))) =
      ENNReal.ofReal |(s : ℝ) - (t : ℝ)| ^ 2 *
        transportCost (π.map (fun γ => (γ 0, γ 1))) := by
  rw [transportCost_plan_lintegral, transportCost_plan_lintegral,
    ← lintegral_const_mul _ (((measurable_path_eval 0).dist
      (measurable_path_eval 1)).ennreal_ofReal.pow_const 2)]
  apply lintegral_congr_ae
  filter_upwards [hg] with γ hγ
  rw [hγ s t, ENNReal.ofReal_mul (abs_nonneg _), mul_pow]

variable [StandardBorelSpace X] [Nonempty X]

theorem geodesic_plan_optimal_marginals (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0, γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0, γ 1))) ≠ ∞) (s t : Time) :
    IsOptimalCoupling (π.map (fun γ => γ s)) (π.map (fun γ => γ t))
      (π.map (fun γ => (γ s, γ t))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst ((measurable_path_eval s).prodMk (measurable_path_eval t))]
    rfl
  · rw [Measure.map_map measurable_snd ((measurable_path_eval s).prodMk (measurable_path_eval t))]
    rfl
  · intro κ hκ0 hκ1
    apply (ENNReal.rpow_le_rpow_iff (show (0 : ℝ) < 1 / 2 by norm_num)).mp
    rw [geodesic_plan_cost_root π hg s t,
      ← wassersteinSq_eq_cost hp, ← wassersteinEDist,
      ← wassersteinEDist_geodesic_plan π hg hp hfin s t]
    exact wassersteinEDist_le_cost hκ0 hκ1


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal

theorem quadratic_gluing_saturation {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (a b c : A → ℝ) (ha : Measurable a) (hb : Measurable b)
    (_ : Measurable c)
    (han : ∀ᵐ x ∂μ, 0 ≤ a x) (hbn : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hcn : ∀ᵐ x ∂μ, 0 ≤ c x) (htri : ∀ᵐ x ∂μ, c x ≤ a x + b x)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h0 : ∫⁻ x, ENNReal.ofReal (a x) ^ 2 ∂μ ≤ (4 : ℝ≥0∞)⁻¹ * C)
    (h1 : ∫⁻ x, ENNReal.ofReal (b x) ^ 2 ∂μ ≤ (4 : ℝ≥0∞)⁻¹ * C)
    (hmin : C ≤ ∫⁻ x, ENNReal.ofReal (c x) ^ 2 ∂μ) :
    (∫⁻ x, ENNReal.ofReal (c x) ^ 2 ∂μ) = C ∧
      ∀ᵐ x ∂μ, a x = b x ∧ c x = 2 * a x := by
  let f := fun x => ENNReal.ofReal (c x) ^ 2
  let g := fun x => (2 : ℝ≥0∞) * ENNReal.ofReal (a x) ^ 2 +
    2 * ENNReal.ofReal (b x) ^ 2
  have hg : Measurable g :=
    ((ha.ennreal_ofReal.pow_const 2).const_mul 2).add ((hb.ennreal_ofReal.pow_const 2).const_mul 2)
  have hfg : f ≤ᵐ[μ] g := by
    filter_upwards [han, hbn, hcn, htri] with x hax hbx hcx hx
    dsimp only [f, g]
    rw [← ENNReal.ofReal_pow hcx, ← ENNReal.ofReal_pow hax, ← ENNReal.ofReal_pow hbx,
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (a x - b x)]
  have hgc : ∫⁻ x, g x ∂μ ≤ C := by
    dsimp only [g]
    rw [lintegral_add_left ((ha.ennreal_ofReal.pow_const 2).const_mul 2),
      lintegral_const_mul 2 (ha.ennreal_ofReal.pow_const 2),
      lintegral_const_mul 2 (hb.ennreal_ofReal.pow_const 2)]
    calc
      _ ≤ 2 * ((4 : ℝ≥0∞)⁻¹ * C) + 2 * ((4 : ℝ≥0∞)⁻¹ * C) :=
        by gcongr
      _ = C := by
        rw [← add_mul, ← mul_assoc]
        rw [show (2 : ℝ≥0∞) + 2 = 4 by norm_num,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hfc : ∫⁻ x, f x ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hC ((lintegral_mono_ae hfg).trans hgc)
  have heq := ae_eq_of_ae_le_of_lintegral_le hfg hfc hg.aemeasurable (hgc.trans hmin)
  refine ⟨le_antisymm ((lintegral_mono_ae hfg).trans hgc) hmin, ?_⟩
  filter_upwards [heq, han, hbn, hcn, htri] with x hx hax hbx hcx htx
  have hr := congrArg ENNReal.toReal hx
  dsimp only [f, g] at hr
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hax, ENNReal.toReal_ofReal hbx,
    ENNReal.toReal_ofReal hcx] at hr
  have hab : a x = b x := by nlinarith [sq_nonneg (a x - b x)]
  refine ⟨hab, ?_⟩
  nlinarith [sq_nonneg (c x - 2 * a x)]


end

 
section

 
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X] [Nonempty X]
attribute [local instance] pathBorel pathBorelSpace

omit [Nonempty X] in
theorem measurableSet_matchedPaths :
    MeasurableSet {z : C(Time, X) × C(Time, X) | z.1 1 = z.2 0} :=
  measurableSet_eq_fun ((measurable_path_eval 1).comp measurable_fst)
    ((measurable_path_eval 0).comp measurable_snd)

theorem exists_matched_path_law (q₀ q₁ : Measure C(Time, X))
    [IsProbabilityMeasure q₀] [IsProbabilityMeasure q₁]
    (hend : q₀.map (fun γ => γ 1) = q₁.map (fun γ => γ 0)) :
    ∃ ρ : Measure (MatchedPaths X), IsProbabilityMeasure ρ ∧
      ρ.map (fun z => z.val.1) = q₀ ∧ ρ.map (fun z => z.val.2) = q₁ := by
  let : Nonempty C(Time, X) := ⟨ContinuousMap.const _ (Classical.choice ‹Nonempty X›)⟩
  obtain ⟨ζ, hζ, hζ0, hζ1, hζmatch⟩ := exists_coupling_common_map q₀ q₁
    (fun γ => γ 1) (fun γ => γ 0) (measurable_path_eval 1) (measurable_path_eval 0) hend
  let := hζ
  let ρ : Measure (MatchedPaths X) := ζ.comap Subtype.val
  have hρ : ρ.map Subtype.val = ζ := by
    dsimp only [ρ]
    exact (map_comap_subtype_coe (measurableSet_matchedPaths (X := X)) ζ).trans
      (Measure.restrict_eq_self_of_ae_mem hζmatch)
  have h0 : ρ.map (fun z => z.val.1) = q₀ := by
    rw [← hζ0, ← hρ, Measure.map_map measurable_fst measurable_subtype_coe]
    rfl
  have h1 : ρ.map (fun z => z.val.2) = q₁ := by
    rw [← hζ1, ← hρ, Measure.map_map measurable_snd measurable_subtype_coe]
    rfl
  have : IsProbabilityMeasure (ρ.map (fun z => z.val.1)) := h0.symm ▸ inferInstance
  exact ⟨ρ, Measure.isProbabilityMeasure_of_map measurable_subtype_coe.fst.aemeasurable, h0, h1⟩

omit [SeparableSpace X] [CompleteSpace X] [Nonempty X] in
theorem matched_law_eval (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time, X)) (hρ : ρ.map (fun z => z.val.1) = q) (t : Time) :
    ρ.map (fun z => z.val.1 t) = q.map (fun γ => γ t) := by
  rw [← hρ, Measure.map_map (measurable_path_eval t) measurable_subtype_coe.fst]
  rfl

omit [SeparableSpace X] [CompleteSpace X] [Nonempty X] in
theorem matched_law_eval_right (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time, X)) (hρ : ρ.map (fun z => z.val.2) = q) (t : Time) :
    ρ.map (fun z => z.val.2 t) = q.map (fun γ => γ t) := by
  rw [← hρ, Measure.map_map (measurable_path_eval t) measurable_subtype_coe.snd]
  rfl


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X] [Nonempty X]
attribute [local instance] pathBorel pathBorelSpace

omit [Nonempty X] in
theorem joined_law_eval_zero (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time, X)) (hρ : ρ.map (fun z => z.val.1) = q) :
    (ρ.map joinMatched).map (fun γ => γ 0) = q.map (fun γ => γ 0) := by
  rw [Measure.map_map (measurable_path_eval 0) joinMatched_continuous.measurable]
  simpa only [Function.comp_def, joinMatched_zero] using matched_law_eval ρ q hρ 0

omit [Nonempty X] in
theorem joined_law_eval_one (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time, X)) (hρ : ρ.map (fun z => z.val.2) = q) :
    (ρ.map joinMatched).map (fun γ => γ 1) = q.map (fun γ => γ 1) := by
  rw [Measure.map_map (measurable_path_eval 1) joinMatched_continuous.measurable]
  simpa only [Function.comp_def, joinMatched_one] using matched_law_eval_right ρ q hρ 1

omit [Nonempty X] in
theorem joined_law_eval_midpoint (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time, X)) (hρ : ρ.map (fun z => z.val.1) = q) :
    (ρ.map joinMatched).map (fun γ => γ midpointTime) = q.map (fun γ => γ 1) := by
  rw [Measure.map_map (measurable_path_eval midpointTime) joinMatched_continuous.measurable]
  simpa only [Function.comp_def, joinMatched_midpoint] using matched_law_eval ρ q hρ 1

omit [Nonempty X] in
theorem midpoint_matched_law_optimal
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0, γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0, γ 1))) ≠ ∞)
    (q₀ q₁ : Measure C(Time, X))
    (hg₀ : ∀ᵐ γ ∂q₀, IsGeodesic γ) (hg₁ : ∀ᵐ γ ∂q₁, IsGeodesic γ)
    (hp₀ : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ midpointTime))
      (q₀.map (fun γ => (γ 0, γ 1))))
    (hp₁ : IsOptimalCoupling (π.map (fun γ => γ midpointTime)) (π.map (fun γ => γ 1))
      (q₁.map (fun γ => (γ 0, γ 1))))
    (ρ : Measure (MatchedPaths X))
    (hρ₀ : ρ.map (fun z => z.val.1) = q₀) (hρ₁ : ρ.map (fun z => z.val.2) = q₁) :
    IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      ((ρ.map joinMatched).map (fun γ => (γ 0, γ 1))) ∧
    (∀ᵐ γ ∂ρ.map joinMatched, IsGeodesic γ) ∧
    ∀ᵐ z ∂ρ, dist (z.val.1 0) (z.val.1 1) = dist (z.val.2 0) (z.val.2 1) ∧
      dist (z.val.1 0) (z.val.2 1) = 2 * dist (z.val.1 0) (z.val.1 1) := by
  let C := transportCost (π.map (fun γ => (γ 0, γ 1)))
  let a := fun z : MatchedPaths X => dist (z.val.1 0) (z.val.1 1)
  let b := fun z : MatchedPaths X => dist (z.val.2 0) (z.val.2 1)
  let c := fun z : MatchedPaths X => dist (z.val.1 0) (z.val.2 1)
  have hq₀ : q₀.map (fun γ => γ 0) = π.map (fun γ => γ 0) := by
    simpa only [Measure.map_map measurable_fst ((measurable_path_eval 0).prodMk
      (measurable_path_eval 1)), Function.comp_def] using hp₀.1
  have hq₁ : q₁.map (fun γ => γ 1) = π.map (fun γ => γ 1) := by
    simpa only [Measure.map_map measurable_snd ((measurable_path_eval 0).prodMk
      (measurable_path_eval 1)), Function.comp_def] using hp₁.2.1
  have hend₀ : ((ρ.map joinMatched).map (fun γ => (γ 0, γ 1))).map Prod.fst =
      π.map (fun γ => γ 0) := by
    rw [Measure.map_map measurable_fst ((measurable_path_eval 0).prodMk
      (measurable_path_eval 1))]
    exact (joined_law_eval_zero ρ q₀ hρ₀).trans hq₀
  have hend₁ : ((ρ.map joinMatched).map (fun γ => (γ 0, γ 1))).map Prod.snd =
      π.map (fun γ => γ 1) := by
    rw [Measure.map_map measurable_snd ((measurable_path_eval 0).prodMk
      (measurable_path_eval 1))]
    exact (joined_law_eval_one ρ q₁ hρ₁).trans hq₁
  have ha : Measurable a := ((measurable_path_eval 0).comp measurable_subtype_coe.fst).dist
    ((measurable_path_eval 1).comp measurable_subtype_coe.fst)
  have hb : Measurable b := ((measurable_path_eval 0).comp measurable_subtype_coe.snd).dist
    ((measurable_path_eval 1).comp measurable_subtype_coe.snd)
  have hc : Measurable c := ((measurable_path_eval 0).comp measurable_subtype_coe.fst).dist
    ((measurable_path_eval 1).comp measurable_subtype_coe.snd)
  have haCost : ∫⁻ z, ENNReal.ofReal (a z) ^ 2 ∂ρ =
      transportCost (q₀.map (fun γ => (γ 0, γ 1))) := by
    rw [transportCost_plan_lintegral, ← hρ₀, lintegral_map
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).ennreal_ofReal.pow_const 2)
      measurable_subtype_coe.fst]
  have hbCost : ∫⁻ z, ENNReal.ofReal (b z) ^ 2 ∂ρ =
      transportCost (q₁.map (fun γ => (γ 0, γ 1))) := by
    rw [transportCost_plan_lintegral, ← hρ₁, lintegral_map
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).ennreal_ofReal.pow_const 2)
      measurable_subtype_coe.snd]
  have hcCost : ∫⁻ z, ENNReal.ofReal (c z) ^ 2 ∂ρ =
      transportCost ((ρ.map joinMatched).map (fun γ => (γ 0, γ 1))) := by
    rw [transportCost_plan_lintegral, lintegral_map
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).ennreal_ofReal.pow_const 2)
      joinMatched_continuous.measurable]
    simp only [joinMatched_zero, joinMatched_one, c]
  have h0 : ∫⁻ z, ENNReal.ofReal (a z) ^ 2 ∂ρ ≤ (4 : ℝ≥0∞)⁻¹ * C := by
    rw [haCost]
    have hh := hp₀.2.2 (π.map (fun γ => (γ 0, γ midpointTime)))
      (by rw [Measure.map_map measurable_fst ((measurable_path_eval 0).prodMk
        (measurable_path_eval midpointTime))]; rfl)
      (by rw [Measure.map_map measurable_snd ((measurable_path_eval 0).prodMk
        (measurable_path_eval midpointTime))]; rfl)
    rw [geodesic_plan_cost π hg] at hh
    convert hh using 1 ; norm_num [midpointTime, C, ENNReal.ofReal_div_of_pos, div_eq_mul_inv, ← ENNReal.inv_pow]
  have h1 : ∫⁻ z, ENNReal.ofReal (b z) ^ 2 ∂ρ ≤ (4 : ℝ≥0∞)⁻¹ * C := by
    rw [hbCost]
    have hh := hp₁.2.2 (π.map (fun γ => (γ midpointTime, γ 1)))
      (by rw [Measure.map_map measurable_fst ((measurable_path_eval midpointTime).prodMk
        (measurable_path_eval 1))]; rfl)
      (by rw [Measure.map_map measurable_snd ((measurable_path_eval midpointTime).prodMk
        (measurable_path_eval 1))]; rfl)
    rw [geodesic_plan_cost π hg] at hh
    convert hh using 1 ; norm_num [midpointTime, C, ENNReal.ofReal_div_of_pos, div_eq_mul_inv, ← ENNReal.inv_pow]
  have htri : ∀ z, c z ≤ a z + b z := by
    intro z
    dsimp [a, b, c]
    rw [← z.property]
    exact dist_triangle _ _ _
  obtain ⟨hcost, heq⟩ := quadratic_gluing_saturation ρ a b c ha hb hc
    (ae_of_all _ (fun _ => dist_nonneg)) (ae_of_all _ (fun _ => dist_nonneg))
    (ae_of_all _ (fun _ => dist_nonneg)) (ae_of_all _ htri) C hfin h0 h1
    (by rw [hcCost]; exact hp.2.2 _ hend₀ hend₁)
  refine ⟨⟨hend₀, hend₁, ?_⟩, ?_, heq⟩
  · intro κ hκ₀ hκ₁
    rw [← hcCost, hcost]
    exact hp.2.2 κ hκ₀ hκ₁
  · apply (ae_map_iff joinMatched_continuous.measurable.aemeasurable
      isClosed_geodesicSet.measurableSet).mpr
    have hgeo₀ : ∀ᵐ z ∂ρ, IsGeodesic z.val.1 :=
      ae_of_ae_map measurable_subtype_coe.fst.aemeasurable (hρ₀ ▸ hg₀)
    have hgeo₁ : ∀ᵐ z ∂ρ, IsGeodesic z.val.2 :=
      ae_of_ae_map measurable_subtype_coe.snd.aemeasurable (hρ₁ ▸ hg₁)
    filter_upwards [hgeo₀, hgeo₁, heq] with z hz₀ hz₁ hz
    exact joinMatched_isGeodesic z hz₀ hz₁ hz.1 hz.2


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X] [Nonempty X]
attribute [local instance] pathBorel pathBorelSpace

theorem midpoint_laws_distance_bound
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0, γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0, γ 1))) ≠ ∞)
    {D : ℝ} (hD : OptimalPlanDistanceBound (π.map (fun γ => γ 0))
      (π.map (fun γ => γ 1)) D)
    (q₀ q₁ : Measure C(Time, X)) [IsProbabilityMeasure q₀] [IsProbabilityMeasure q₁]
    (hg₀ : ∀ᵐ γ ∂q₀, IsGeodesic γ) (hg₁ : ∀ᵐ γ ∂q₁, IsGeodesic γ)
    (hp₀ : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ midpointTime))
      (q₀.map (fun γ => (γ 0, γ 1))))
    (hp₁ : IsOptimalCoupling (π.map (fun γ => γ midpointTime)) (π.map (fun γ => γ 1))
      (q₁.map (fun γ => (γ 0, γ 1)))) :
    (∀ᵐ γ ∂q₀, dist (γ 0) (γ 1) ≤ D / 2) ∧
      ∀ᵐ γ ∂q₁, dist (γ 0) (γ 1) ≤ D / 2 := by
  have he₀ := (optimalPlan_endpoints _ _ q₀ hp₀).2
  have he₁ := (optimalPlan_endpoints _ _ q₁ hp₁).1
  obtain ⟨ρ, hρ, hρ₀, hρ₁⟩ := exists_matched_path_law q₀ q₁ (he₀.trans he₁.symm)
  let := hρ
  obtain ⟨hpj, hgj, heq⟩ := midpoint_matched_law_optimal π hg hp hfin
    q₀ q₁ hg₀ hg₁ hp₀ hp₁ ρ hρ₀ hρ₁
  have hprob : IsProbabilityMeasure (ρ.map joinMatched) :=
    inferInstance
  have hd := ae_of_ae_map joinMatched_continuous.measurable.aemeasurable
    (hD _ hprob hgj hpj)
  have hhalf : ∀ᵐ z ∂ρ, dist (z.val.1 0) (z.val.1 1) ≤ D / 2 ∧
      dist (z.val.2 0) (z.val.2 1) ≤ D / 2 := by
    filter_upwards [hd, heq] with z hz he
    simp only [joinMatched_zero, joinMatched_one] at hz
    constructor <;> linarith [he.1, he.2]
  have hm : MeasurableSet {γ : C(Time, X) | dist (γ 0) (γ 1) ≤ D / 2} :=
    measurableSet_le ((measurable_path_eval 0).dist (measurable_path_eval 1)) measurable_const
  constructor
  · rw [← hρ₀]
    exact (ae_map_iff measurable_subtype_coe.fst.aemeasurable hm).mpr (hhalf.mono fun _ h => h.1)
  · rw [← hρ₁]
    exact (ae_map_iff measurable_subtype_coe.snd.aemeasurable hm).mpr (hhalf.mono fun _ h => h.2)

theorem geodesic_subpath_law
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0, γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0, γ 1))) ≠ ∞) (s t : Time) :
    IsProbabilityMeasure (π.map (subpath s t)) ∧
    (∀ᵐ γ ∂π.map (subpath s t), IsGeodesic γ) ∧
    IsOptimalCoupling (π.map (fun γ => γ s)) (π.map (fun γ => γ t))
      ((π.map (subpath s t)).map (fun γ => (γ 0, γ 1))) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · exact (ae_map_iff (subpath_measurable s t).aemeasurable
      isClosed_geodesicSet.measurableSet).mpr (hg.mono fun _ h => h.subpath s t)
  · rw [Measure.map_map ((measurable_path_eval 0).prodMk
      (measurable_path_eval 1)) (subpath_measurable s t)]
    simpa only [Function.comp_def, subpath_zero, subpath_one] using
      geodesic_plan_optimal_marginals π hg hp hfin s t

theorem OptimalPlanDistanceBound.midpoint_halves
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0, γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0, γ 1))) ≠ ∞)
    {D : ℝ} (hD : OptimalPlanDistanceBound (π.map (fun γ => γ 0))
      (π.map (fun γ => γ 1)) D) :
    OptimalPlanDistanceBound (π.map (fun γ => γ 0)) (π.map (fun γ => γ midpointTime)) (D / 2) ∧
    OptimalPlanDistanceBound (π.map (fun γ => γ midpointTime)) (π.map (fun γ => γ 1)) (D / 2) := by
  constructor
  · intro q hq hgq hpq
    let := hq
    obtain ⟨hprob, hg', hp'⟩ := geodesic_subpath_law π hg hp hfin midpointTime 1
    let := hprob
    exact (midpoint_laws_distance_bound π hg hp hfin hD
      q (π.map (subpath midpointTime 1)) hgq hg' hpq hp').1
  · intro q hq hgq hpq
    let := hq
    obtain ⟨hprob, hg', hp'⟩ := geodesic_subpath_law π hg hp hfin 0 midpointTime
    let := hprob
    exact (midpoint_laws_distance_bound π hg hp hfin hD
      (π.map (subpath 0 midpointTime)) q hg' hgq hp' hpq).2


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal

noncomputable def compressionStep (K N D : ℝ) (C : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (N * D * Real.sqrt (|K| / (N - 1)))) * C

noncomputable def compressionBudget (K N D : ℝ) (C : ℝ≥0∞) : ℝ≥0∞ :=
  compressionStep K N (2 * D) C

theorem midpointCapacity_eq (K N D : ℝ) (C : ℝ≥0∞) :
    midpointCapacity K N D C =
      ENNReal.ofReal (Real.cosh (D * Real.sqrt (|K| / (N - 1))) ^ N) * C := by
  let a := D * Real.sqrt (|K| / (N - 1))
  have hf : 2 * midpointFloor K N D = (ENNReal.ofReal (Real.cosh a))⁻¹ := by
    rw [midpointFloor, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    have he : (2 : ℝ) * (1 / (2 * Real.cosh a)) = (Real.cosh a)⁻¹ := by
      field_simp
    change ENNReal.ofReal (2 * (1 / (2 * Real.cosh a))) = _
    rw [he, ENNReal.ofReal_inv_of_pos (Real.cosh_pos a)]
  rw [midpointCapacity, hf, ENNReal.inv_rpow, div_eq_mul_inv, inv_inv,
    ENNReal.ofReal_rpow_of_pos (Real.cosh_pos a), mul_comm]

theorem midpointCapacity_le_compressionStep (K N D : ℝ) (C : ℝ≥0∞)
    (hN : 0 ≤ N) (hD : 0 ≤ D) :
    midpointCapacity K N D C ≤ compressionStep K N D C := by
  rw [midpointCapacity_eq, compressionStep]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have ha : 0 ≤ D * Real.sqrt (|K| / (N - 1)) := mul_nonneg hD (Real.sqrt_nonneg _)
  have he := Real.exp_le_exp.mpr (neg_le_self ha)
  have hcos : Real.cosh (D * Real.sqrt (|K| / (N - 1))) ≤
      Real.exp (D * Real.sqrt (|K| / (N - 1))) := by
    rw [Real.cosh_eq]
    linarith
  have hh := Real.rpow_le_rpow (Real.cosh_pos _).le hcos hN
  rw [← Real.exp_mul] at hh
  convert hh using 1 ; congr 1 ; ring

theorem le_compressionStep (K N D : ℝ) (C : ℝ≥0∞)
    (hN : 0 ≤ N) (hD : 0 ≤ D) : C ≤ compressionStep K N D C := by
  have h : 1 ≤ ENNReal.ofReal (Real.exp (N * D * Real.sqrt (|K| / (N - 1)))) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
  simpa only [one_mul, compressionStep] using mul_le_mul_left h C

theorem compressionStep_ne_top (K N D : ℝ) {C : ℝ≥0∞} (hC : C ≠ ∞) :
    compressionStep K N D C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC

theorem compressionBudget_halve (K N D : ℝ) (C : ℝ≥0∞) :
    compressionBudget K N (D / 2) (compressionStep K N D C) = compressionBudget K N D C := by
  unfold compressionBudget compressionStep
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring_nf

theorem le_compressionBudget (K N D : ℝ) (C : ℝ≥0∞)
    (hN : 0 ≤ N) (hD : 0 ≤ D) : C ≤ compressionBudget K N D C :=
  le_compressionStep K N (2 * D) C hN (by positivity)

theorem compressionBudget_ne_top (K N D : ℝ) {C : ℝ≥0∞} (hC : C ≠ ∞) :
    compressionBudget K N D C ≠ ∞ := compressionStep_ne_top K N (2 * D) hC



 
noncomputable abbrev lowerTime (t : Time) : Time := timeSegment 0 midpointTime t
noncomputable abbrev upperTime (t : Time) : Time := timeSegment midpointTime 1 t

@[simp] theorem coe_lowerTime (t : Time) : (lowerTime t : ℝ) = (t : ℝ) / 2 := by
  change (1 - (t : ℝ)) * 0 + (t : ℝ) * (1 / 2) = _
  ring
@[simp] theorem coe_upperTime (t : Time) : (upperTime t : ℝ) = ((t : ℝ) + 1) / 2 := by
  change (1 - (t : ℝ)) * (1 / 2) + (t : ℝ) * 1 = _
  ring

noncomputable def dyadicGrid : ℕ → Set Time
  | 0 => {0, 1}
  | m + 1 => lowerTime '' dyadicGrid m ∪ upperTime '' dyadicGrid m

theorem dyadicGrid_endpoints (m : ℕ) : (0 : Time) ∈ dyadicGrid m ∧ (1 : Time) ∈ dyadicGrid m := by
  induction m with
  | zero => simp [dyadicGrid]
  | succ m ih =>
    constructor
    · exact Or.inl ⟨0, ih.1, by apply Subtype.ext; simp⟩
    · exact Or.inr ⟨1, ih.2, by apply Subtype.ext; simp⟩

theorem dyadicGrid_mono : Monotone dyadicGrid := by
  apply monotone_nat_of_le_succ
  intro m
  induction m with
  | zero =>
    intro t ht
    rcases ht with ht | ht
    · exact ht ▸ (dyadicGrid_endpoints 1).1
    · exact ht ▸ (dyadicGrid_endpoints 1).2
  | succ m ih =>
    exact union_subset_union (image_mono ih) (image_mono ih)

theorem dyadicGrid_approx (m : ℕ) (t : Time) :
    ∃ s ∈ dyadicGrid m, |(s : ℝ) - (t : ℝ)| ≤ (1 / 2 : ℝ) ^ m := by
  induction m generalizing t with
  | zero =>
    refine ⟨0, (dyadicGrid_endpoints 0).1, ?_⟩
    change |(0 : ℝ) - (t : ℝ)| ≤ (1 / 2 : ℝ) ^ 0
    simpa only [pow_zero, zero_sub, abs_neg, abs_of_nonneg t.property.1] using t.property.2
  | succ m ih =>
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · let t' : Time := ⟨2 * (t : ℝ), by constructor <;> linarith [t.property.1]⟩
      obtain ⟨s, hs, hd⟩ := ih t'
      refine ⟨lowerTime s, Or.inl ⟨s, hs, rfl⟩, ?_⟩
      rw [coe_lowerTime, pow_succ]
      have he : (s : ℝ) / 2 - (t : ℝ) = ((s : ℝ) - (t' : ℝ)) / 2 := by dsimp [t']; ring
      rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · let t' : Time := ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.2]⟩
      obtain ⟨s, hs, hd⟩ := ih t'
      refine ⟨upperTime s, Or.inr ⟨s, hs, rfl⟩, ?_⟩
      rw [coe_upperTime, pow_succ]
      have he : ((s : ℝ) + 1) / 2 - (t : ℝ) = ((s : ℝ) - (t' : ℝ)) / 2 := by dsimp [t']; ring
      rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith

theorem dense_dyadicGrid : Dense (⋃ m, dyadicGrid m) := by
  rw [Metric.dense_iff]
  intro t ε hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨s, hs, hd⟩ := dyadicGrid_approx m t
  exact ⟨s, by simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using hd.trans_lt hm,
    mem_iUnion.mpr ⟨m, hs⟩⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X] [Nonempty X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] [CompleteSpace X] [Nonempty X] in
@[simp] theorem joinMatched_lowerTime (z : MatchedPaths X) (t : Time) :
    joinMatched z (lowerTime t) = z.val.1 t := by
  rw [joinMatched_apply_left z _ (by rw [coe_lowerTime]; linarith [t.property.2])]
  congr 1
  apply Subtype.ext
  change (projIcc 0 1 zero_le_one (2 * (lowerTime t : ℝ)) : ℝ) = (t : ℝ)
  rw [coe_lowerTime, show 2 * ((t : ℝ) / 2) = (t : ℝ) by ring]
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one t.property)

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] [CompleteSpace X] [Nonempty X] in
@[simp] theorem joinMatched_upperTime (z : MatchedPaths X) (t : Time) :
    joinMatched z (upperTime t) = z.val.2 t := by
  rw [joinMatched_apply_right z _ (by rw [coe_upperTime]; linarith [t.property.1])]
  congr 1
  apply Subtype.ext
  change (projIcc 0 1 zero_le_one (2 * (upperTime t : ℝ) - 1) : ℝ) = (t : ℝ)
  rw [coe_upperTime, show 2 * (((t : ℝ) + 1) / 2) - 1 = (t : ℝ) by ring]
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one t.property)

omit [Nonempty X] in
theorem joined_law_eval_lowerTime (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time, X)) (hρ : ρ.map (fun z => z.val.1) = q) (t : Time) :
    (ρ.map joinMatched).map (fun γ => γ (lowerTime t)) = q.map (fun γ => γ t) := by
  rw [Measure.map_map (measurable_path_eval _) joinMatched_continuous.measurable]
  simpa only [Function.comp_def, joinMatched_lowerTime] using matched_law_eval ρ q hρ t

omit [Nonempty X] in
theorem joined_law_eval_upperTime (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time, X)) (hρ : ρ.map (fun z => z.val.2) = q) (t : Time) :
    (ρ.map joinMatched).map (fun γ => γ (upperTime t)) = q.map (fun γ => γ t) := by
  rw [Measure.map_map (measurable_path_eval _) joinMatched_continuous.measurable]
  simpa only [Function.comp_def, joinMatched_upperTime] using matched_law_eval_right ρ q hρ t


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal

noncomputable def entropyChord (K A B W t : ℝ) : ℝ :=
  (1 - t) * A + t * B - K / 2 * t * (1 - t) * W

@[simp] theorem entropyChord_zero (K A B W : ℝ) : entropyChord K A B W 0 = A := by
  simp [entropyChord]
@[simp] theorem entropyChord_one (K A B W : ℝ) : entropyChord K A B W 1 = B := by
  simp [entropyChord]

theorem entropyChord_lower (K A B M W t : ℝ) (ht : 0 ≤ t)
    (hM : M ≤ (A + B) / 2 - (K / 8) * W) :
    entropyChord K A M (W / 4) t ≤ entropyChord K A B W (t / 2) := by
  have hh := mul_le_mul_of_nonneg_left hM ht
  unfold entropyChord
  nlinarith only [hh]

theorem entropyChord_upper (K A B M W t : ℝ) (ht : t ≤ 1)
    (hM : M ≤ (A + B) / 2 - (K / 8) * W) :
    entropyChord K M B (W / 4) t ≤ entropyChord K A B W ((t + 1) / 2) := by
  have hh := mul_le_mul_of_nonneg_left hM (sub_nonneg.mpr ht)
  unfold entropyChord
  nlinarith only [hh]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [BorelSpace X] in
theorem finiteSecondMoment_of_bounded (ν : Measure X) [IsFiniteMeasure ν]
    (p : X) {R : ℝ} (h : ∀ᵐ x ∂ν, dist x p ≤ R) : FiniteSecondMoment ν := by
  refine ⟨p, lt_of_le_of_lt (lintegral_mono_ae (g := fun _ => ENNReal.ofReal R ^ 2) ?_) ?_⟩
  · exact h.mono (fun _ hx => pow_le_pow_left' (ENNReal.ofReal_le_ofReal hx) 2)
  · rw [lintegral_const]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      (measure_lt_top _ _)

variable [SeparableSpace X] [CompleteSpace X] [Nonempty X]

theorem geodesic_midpoint_wasserstein_sq
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0, γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0, γ 1))) ≠ ∞) :
    (wassersteinSq (π.map (fun γ => γ 0)) (π.map (fun γ => γ midpointTime))).toReal =
      (wassersteinSq (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))).toReal / 4 ∧
    (wassersteinSq (π.map (fun γ => γ midpointTime)) (π.map (fun γ => γ 1))).toReal =
      (wassersteinSq (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))).toReal / 4 := by
  have he (s t : Time) :
      (wassersteinSq (π.map (fun γ => γ s)) (π.map (fun γ => γ t))).toReal =
        |(s : ℝ) - (t : ℝ)| ^ 2 *
          (wassersteinSq (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))).toReal := by
    rw [wassersteinSq_eq_cost (geodesic_plan_optimal_marginals π hg hp hfin s t),
      geodesic_plan_cost π hg, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _), wassersteinSq_eq_cost hp]
  constructor
  · rw [he]
    norm_num [midpointTime]
    ring
  · rw [he]
    norm_num [midpointTime]
    ring


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.exists_dyadic_compressed_entropy_plan
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (m : ℕ) :
    ∀ (ν₀ ν₁ : Measure X), IsProbabilityMeasure ν₀ → IsProbabilityMeasure ν₁ →
    ∀ (C : ℝ≥0∞), C ≠ ∞ → ν₀ ≤ C • hausdorff n X → ν₁ ≤ C • hausdorff n X →
    ∀ (p : X) (R : ℝ), 0 ≤ R →
    (∀ᵐ x ∂ν₀, dist x p ≤ R) → (∀ᵐ x ∂ν₁, dist x p ≤ R) →
    ∀ (D : ℝ), 0 ≤ D → OptimalPlanDistanceBound ν₀ ν₁ D →
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      ∀ t ∈ dyadicGrid m,
        π.map (fun γ => γ t) ≤ compressionBudget K n D C • hausdorff n X ∧
        boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ t)) ≤
          entropyChord K (boltzmannEntropy (hausdorff n X) ν₀)
            (boltzmannEntropy (hausdorff n X) ν₁) (wassersteinSq ν₀ ν₁).toReal t := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  induction m with
  | zero =>
    intro ν₀ ν₁ hν₀ hν₁ C hC h0 h1 p R hR hs0 hs1 D hD0 hD
    let := hν₀
    let := hν₁
    have hm0 := finiteSecondMoment_of_bounded ν₀ p hs0
    have hm1 := finiteSecondMoment_of_bounded ν₁ p hs1
    obtain ⟨π, hπ, hg, hp, _⟩ := hX.cd ν₀ ν₁ hν₀ hν₁
      (Measure.absolutelyContinuous_of_le_smul h0)
      (Measure.absolutelyContinuous_of_le_smul h1) hm0 hm1
    have he := optimalPlan_endpoints ν₀ ν₁ π hp
    have hcap := le_compressionBudget K n D C hn0 hD0
    have h0' : ν₀ ≤ compressionBudget K n D C • hausdorff n X :=
      h0.trans (by intro S; exact mul_le_mul_left hcap _)
    have h1' : ν₁ ≤ compressionBudget K n D C • hausdorff n X :=
      h1.trans (by intro S; exact mul_le_mul_left hcap _)
    refine ⟨π, hπ, hg, hp, ?_⟩
    intro t ht
    rcases ht with rfl | ht
    · rw [he.1]
      exact ⟨h0', by simp⟩
    · have ht' : t = 1 := ht
      subst t
      rw [he.2]
      exact ⟨h1', by simp⟩
  | succ m ih =>
    intro ν₀ ν₁ hν₀ hν₁ C hC h0 h1 p R hR hs0 hs1 D hD0 hD
    let := hν₀
    let := hν₁
    let : Nonempty X := ⟨p⟩
    have hm0 := finiteSecondMoment_of_bounded ν₀ p hs0
    have hm1 := finiteSecondMoment_of_bounded ν₁ p hs1
    obtain ⟨π, hπ, hg, hp, hmidcap, hmident⟩ :=
      hX.exists_compressed_entropy_midpoint_short K n hn ν₀ ν₁ hC h0 h1 hm0 hm1 p hR hs0 hs1 D hD
    let := hπ
    let νm := π.map (fun γ => γ midpointTime)
    have hνm : IsProbabilityMeasure νm :=
      inferInstance
    let := hνm
    have he := optimalPlan_endpoints ν₀ ν₁ π hp
    have hp' : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
        (π.map (fun γ => (γ 0, γ 1))) := by rwa [he.1, he.2]
    have hfin := finite_second_moment_cost hm0 hm1 hp.1 hp.2.1
    have hD' : OptimalPlanDistanceBound (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1)) D := by
      rwa [he.1, he.2]
    obtain ⟨hDl, hDr⟩ := OptimalPlanDistanceBound.midpoint_halves π hg hp' hfin hD'
    rw [he.1] at hDl
    rw [he.2] at hDr
    obtain ⟨hWl, hWr⟩ := geodesic_midpoint_wasserstein_sq π hg hp' hfin
    rw [he.1, he.2] at hWl hWr
    let C' := compressionStep K n D C
    have hC' : C' ≠ ∞ := compressionStep_ne_top K n D hC
    have hincrease : C ≤ C' := le_compressionStep K n D C hn0 hD0
    have h0' : ν₀ ≤ C' • hausdorff n X :=
      h0.trans (by intro S; exact mul_le_mul_left hincrease _)
    have h1' : ν₁ ≤ C' • hausdorff n X :=
      h1.trans (by intro S; exact mul_le_mul_left hincrease _)
    have hm' : νm ≤ C' • hausdorff n X :=
      hmidcap.trans (by intro S; exact mul_le_mul_left (midpointCapacity_le_compressionStep K n D C hn0 hD0) _)
    have hsM : ∀ᵐ x ∂νm, dist x p ≤ 3 * R := by
      apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable
        (measurableSet_le (measurable_id.dist measurable_const) measurable_const)).mpr
      exact (optimal_geodesic_plan_bounded ν₀ ν₁ π hg hp p hR hs0 hs1).mono fun _ h => h.2 midpointTime
    have hs0' : ∀ᵐ x ∂ν₀, dist x p ≤ 3 * R := hs0.mono fun _ h => by linarith
    have hs1' : ∀ᵐ x ∂ν₁, dist x p ≤ 3 * R := hs1.mono fun _ h => by linarith
    obtain ⟨q₀, hq₀, hg₀, hp₀, hgrid₀⟩ := ih ν₀ νm hν₀ hνm C' hC' h0' hm'
      p (3 * R) (by positivity) hs0' hsM (D / 2) (by positivity) hDl
    obtain ⟨q₁, hq₁, hg₁, hp₁, hgrid₁⟩ := ih νm ν₁ hνm hν₁ C' hC' hm' h1'
      p (3 * R) (by positivity) hsM hs1' (D / 2) (by positivity) hDr
    let := hq₀
    let := hq₁
    have he₀ := optimalPlan_endpoints ν₀ νm q₀ hp₀
    have he₁ := optimalPlan_endpoints νm ν₁ q₁ hp₁
    obtain ⟨ρ, hρ, hρ₀, hρ₁⟩ := exists_matched_path_law q₀ q₁ (he₀.2.trans he₁.1.symm)
    let := hρ
    have hp₀' : IsOptimalCoupling (π.map (fun γ => γ 0)) νm
        (q₀.map (fun γ => (γ 0, γ 1))) := by rwa [he.1]
    have hp₁' : IsOptimalCoupling νm (π.map (fun γ => γ 1))
        (q₁.map (fun γ => (γ 0, γ 1))) := by rwa [he.2]
    obtain ⟨hpj, hgj, _⟩ := midpoint_matched_law_optimal π hg hp' hfin
      q₀ q₁ hg₀ hg₁ hp₀' hp₁' ρ hρ₀ hρ₁
    rw [he.1, he.2] at hpj
    refine ⟨ρ.map joinMatched,
      inferInstance, hgj, hpj, ?_⟩
    intro t ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · rw [joined_law_eval_lowerTime ρ q₀ hρ₀]
      obtain ⟨hcap, hent⟩ := hgrid₀ s hs
      rw [show compressionBudget K n (D / 2) C' = compressionBudget K n D C from
        compressionBudget_halve K n D C] at hcap
      refine ⟨hcap, ?_⟩
      rw [hWl] at hent
      rw [coe_lowerTime]
      exact hent.trans (entropyChord_lower _ _ _ _ _ _ s.property.1 hmident)
    · rw [joined_law_eval_upperTime ρ q₁ hρ₁]
      obtain ⟨hcap, hent⟩ := hgrid₁ s hs
      rw [show compressionBudget K n (D / 2) C' = compressionBudget K n D C from
        compressionBudget_halve K n D C] at hcap
      refine ⟨hcap, ?_⟩
      rw [hWr] at hent
      rw [coe_upperTime]
      exact hent.trans (entropyChord_upper _ _ _ _ _ _ s.property.2 hmident)


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal BoundedContinuousFunction

theorem compact_dyadic_selection {Y : Type*} [TopologicalSpace Y]
    {A : Set Y} (hA : IsCompact A) (P : Y → Time → Prop)
    (hclosed : ∀ t, IsClosed {y | P y t})
    (htime : ∀ y ∈ A, IsClosed {t | P y t})
    (hex : ∀ m, ∃ y ∈ A, ∀ t ∈ dyadicGrid m, P y t) :
    ∃ y ∈ A, ∀ t, P y t := by
  let Q : ℕ → Set Y := fun m => {y | ∀ t ∈ dyadicGrid m, P y t}
  have hQ : ∀ m, IsClosed (Q m) := by
    intro m
    simpa only [Q, ofPred_forall] using
      (isClosed_iInter fun t => isClosed_iInter fun (_ : t ∈ dyadicGrid m) => hclosed t)
  have hfin : ∀ u : Finset ℕ, (A ∩ ⋂ m ∈ u, Q m).Nonempty := by
    intro u
    obtain ⟨y, hy, hp⟩ := hex (u.sup id)
    refine ⟨y, hy, mem_iInter.mpr fun m => mem_iInter.mpr fun hm => ?_⟩
    intro t ht
    exact hp t (dyadicGrid_mono (Finset.le_sup hm) ht)
  obtain ⟨y, hy, hgrid⟩ := hA.inter_iInter_nonempty Q hQ hfin
  refine ⟨y, hy, ?_⟩
  have hs : (⋃ m, dyadicGrid m) ⊆ {t | P y t} := by
    intro t ht
    obtain ⟨m, hm⟩ := mem_iUnion.mp ht
    exact mem_iInter.mp hgrid m t hm
  have hc := closure_minimal hs (htime y hy)
  rw [dense_dyadicGrid.closure_eq] at hc
  exact fun t => hc (mem_univ t)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

theorem continuous_time_marginals (π : ProbabilityMeasure C(Time, X)) :
    Continuous (fun t : Time => π.map (fun γ => γ t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hc : Continuous (fun s : Time => ∫ γ, f (γ s) ∂(π : Measure C(Time, X))) := by
    apply continuous_of_dominated (bound := fun _ => ‖f‖)
    · intro s
      exact (f.continuous.comp (continuous_eval_const s)).aestronglyMeasurable
    · intro s
      exact ae_of_all _ (fun γ => f.norm_coe_le_norm (γ s))
    · exact integrable_const _
    · exact ae_of_all _ (fun γ => f.continuous.comp γ.continuous)
  simp only [ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_path_eval _).aemeasurable f.continuous.aestronglyMeasurable]
  exact hc.continuousAt


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace InformationTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

 

def compressedKLConstraint (μ : Measure X) (C : ℝ≥0∞)
    (ν : ProbabilityMeasure X) (a : ℝ) : Prop :=
  (ν : Measure X) ≤ C • μ ∧ 0 ≤ a ∧ klDiv ν μ ≤ ENNReal.ofReal a

theorem isClosed_compressedKLConstraint [ProperSpace X] [SeparableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {C : ℝ≥0∞} (hC : C ≠ ∞)
    {Y : Type*} [TopologicalSpace Y] (ν : Y → ProbabilityMeasure X) (a : Y → ℝ)
    (hν : Continuous ν) (ha : Continuous a) :
    IsClosed {y | compressedKLConstraint μ C (ν y) (a y)} := by
  have hc : IsClosed {ν : ProbabilityMeasure X | (ν : Measure X) ≤ C • μ} := by
    convert (lowerSemicontinuous_transportExcessMass μ hC).isClosed_preimage 0 using 1
    ext ν
    simp only [mem_ofPred_eq, mem_preimage, mem_Iic, nonpos_iff_eq_zero,
      transportExcessMass_zero_iff μ (ν : Measure X) hC]
  have hk := (lowerSemicontinuous_klDiv μ).isClosed_epigraph.preimage
    (hν.prodMk (ENNReal.continuous_ofReal.comp ha))
  exact (hc.preimage hν).inter ((isClosed_le continuous_const ha).inter hk)

omit [MetricSpace X] [BorelSpace X] in
theorem entropy_bound_localized_iff (μ : Measure X) [SigmaFinite μ]
    (ν : ProbabilityMeasure X) {B : Set X} (hB : MeasurableSet B)
    [IsFiniteMeasure (μ.restrict B)] {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hs : ∀ᵐ x ∂(ν : Measure X), x ∈ B)
    (hν : (ν : Measure X) ≤ C • μ) (a : ℝ) :
    boltzmannEntropy μ ν ≤ a ↔
      compressedKLConstraint (μ.restrict B) C ν (a + (μ.restrict B).real univ - 1) := by
  have hloc : (ν : Measure X) ≤ C • μ.restrict B :=
    (compression_iff_localized μ ν hs C).mp hν
  have hac := Measure.absolutelyContinuous_of_le_smul hloc
  have hfin := klDiv_ne_top_of_bounded_density (μ.restrict B) (ν : Measure X) hC hloc
  have he := toReal_klDiv_eq_boltzmannEntropy (μ.restrict B) (ν : Measure X) hfin
  rw [← boltzmannEntropy_localized μ ν hB hac] at he
  simp only [Measure.real, measure_univ, ENNReal.toReal_one] at he
  constructor
  · intro h
    have hv : (klDiv ν (μ.restrict B)).toReal ≤ a + (μ.restrict B).real univ - 1 := by
      rw [he]
      change boltzmannEntropy μ ν + ((μ.restrict B) univ).toReal - 1 ≤
        a + ((μ.restrict B) univ).toReal - 1
      linarith
    refine ⟨hloc, ENNReal.toReal_nonneg.trans hv, ?_⟩
    calc
      klDiv ν (μ.restrict B) = ENNReal.ofReal (klDiv ν (μ.restrict B)).toReal :=
        (ENNReal.ofReal_toReal hfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hv
  · rintro ⟨_, hn, hk⟩
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hk
    rw [ENNReal.toReal_ofReal hn, he] at hh
    change boltzmannEntropy μ ν + ((μ.restrict B) univ).toReal - 1 ≤
      a + ((μ.restrict B) univ).toReal - 1 at hh
    linarith


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace InformationTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.exists_compressed_entropy_plan
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : OptimalPlanDistanceBound ν₀ ν₁ D) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      ∀ t : Time,
        π.map (fun γ => γ t) ≤ compressionBudget K n D C • hausdorff n X ∧
        boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ t)) ≤
          entropyChord K (boltzmannEntropy (hausdorff n X) ν₀)
            (boltzmannEntropy (hausdorff n X) ν₁) (wassersteinSq ν₀ ν₁).toReal t := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let μ := hausdorff n X
  let B := closedBall p (3 * R)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ, B] using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  let v₀ : ProbabilityMeasure X := ⟨ν₀, inferInstance⟩
  let v₁ : ProbabilityMeasure X := ⟨ν₁, inferInstance⟩
  let cap := compressionBudget K n D C
  have hcap : cap ≠ ∞ := compressionBudget_ne_top K n D hC
  let Q : Time → ℝ := fun t =>
    entropyChord K (boltzmannEntropy μ ν₀) (boltzmannEntropy μ ν₁)
      (wassersteinSq ν₀ ν₁).toReal t + (μ.restrict B).real univ - 1
  have hQ : Continuous Q := by
    dsimp only [Q, entropyChord]
    fun_prop
  let A := OptimalGeodesicPlans v₀ v₁
  let P : ProbabilityMeasure C(Time, X) → Time → Prop := fun π t =>
    compressedKLConstraint (μ.restrict B) cap
      (π.map (fun γ => γ t)) (Q t)
  have hmem : ∀ π ∈ A, ∀ t : Time,
      ∀ᵐ x ∂((π : Measure C(Time, X)).map (fun γ => γ t)), x ∈ B := by
    intro π hπ t
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ π hπ.1 hπ.2 p hR hs0 hs1).mono
      fun γ hγ => hγ.2 t
  obtain ⟨π, hπ, hall⟩ := compact_dyadic_selection
    (isCompact_optimal_geodesic_plans v₀ v₁ p hR hs0 hs1) P
    (fun t => isClosed_compressedKLConstraint (μ.restrict B) hcap _ _
      (ProbabilityMeasure.continuous_map (continuous_eval_const t)) continuous_const)
    (fun π _ => isClosed_compressedKLConstraint (μ.restrict B) hcap _ _
      (continuous_time_marginals π) hQ) (by
      intro m
      obtain ⟨q, hq, hgq, hpq, hgrid⟩ := hX.exists_dyadic_compressed_entropy_plan K n hn m
        ν₀ ν₁ inferInstance inferInstance C hC h0 h1 p R hR hs0 hs1 D hD0 hD
      let vq : ProbabilityMeasure C(Time, X) := ⟨q, hq⟩
      have hvq : vq ∈ A := ⟨hgq, hpq⟩
      refine ⟨vq, hvq, ?_⟩
      intro t ht
      have hs := hmem vq hvq t
      exact (entropy_bound_localized_iff μ
        (vq.map (fun γ => γ t)) measurableSet_closedBall hcap
        hs (hgrid t ht).1 _).mp (hgrid t ht).2)
  refine ⟨π, inferInstance, hπ.1, hπ.2, ?_⟩
  intro t
  have hc : (π : Measure C(Time, X)).map (fun γ => γ t) ≤ cap • μ :=
    (compression_iff_localized μ _ (hmem π hπ t) cap).mpr (hall t).1
  refine ⟨hc, ?_⟩
  exact (entropy_bound_localized_iff μ
    (π.map (fun γ => γ t)) measurableSet_closedBall hcap
    (hmem π hπ t) hc _).mpr (hall t)


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem optimalPlanDistanceBound_of_bounded [SeparableSpace X]
    (ν₀ ν₁ : Measure X) (p : X) {R : ℝ}
    (h0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (h1 : ∀ᵐ x ∂ν₁, dist x p ≤ R) :
    OptimalPlanDistanceBound ν₀ ν₁ (2 * R) := by
  intro π _ _ hp
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have he0 : ∀ᵐ γ ∂π, dist (γ 0) p ≤ R := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 0).aemeasurable
      (p := fun x => dist x p ≤ R)
    simpa only [hend.1] using h0
  have he1 : ∀ᵐ γ ∂π, dist (γ 1) p ≤ R := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 1).aemeasurable
      (p := fun x => dist x p ≤ R)
    simpa only [hend.2] using h1
  filter_upwards [he0, he1] with γ hγ0 hγ1
  have hh := dist_triangle (γ 0) p (γ 1)
  rw [dist_comm p (γ 1)] at hh
  linarith

 

theorem NoncollapsedRCD.exists_bounded_entropy_plan
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      Integrable (fun γ : C(Time, X) => dist (γ 0) (γ 1)^2) π ∧
      ∀ t : Time,
        π.map (fun γ => γ t) ≤ compressionBudget K n (2 * R) C • hausdorff n X ∧
        Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv (hausdorff n X) x).toReal *
          Real.log ((π.map (fun γ => γ t)).rnDeriv (hausdorff n X) x).toReal)
          (hausdorff n X) ∧
        boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ t)) ≤
          (1 - (t : ℝ)) * boltzmannEntropy (hausdorff n X) ν₀ +
          (t : ℝ) * boltzmannEntropy (hausdorff n X) ν₁ +
          ((-K) * (t : ℝ) * (1 - (t : ℝ)) / 2) *
            (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let B := closedBall p (3 * R)
  let : IsFiniteMeasure ((hausdorff n X).restrict B) := ⟨by
    simpa [B] using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  have hD := optimalPlanDistanceBound_of_bounded ν₀ ν₁ p hs0 hs1
  obtain ⟨π, hπ, hg, hp, hall⟩ := hX.exists_compressed_entropy_plan K n hn
    ν₀ ν₁ hC h0 h1 p hR hs0 hs1 (2 * R) (by positivity) hD
  let := hπ
  have hb := hD π hπ hg hp
  have hi : Integrable (fun γ : C(Time, X) => dist (γ 0) (γ 1)^2) π := by
    apply Integrable.mono' (integrable_const ((2 * R)^2))
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).pow_const 2).aestronglyMeasurable
    exact hb.mono fun γ hγ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ dist_nonneg hγ _
  have he : (wassersteinSq ν₀ ν₁).toReal = ∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π := by
    rw [wassersteinSq_eq_cost hp, transportCost_plan_eq_integral π hi,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  refine ⟨π, hπ, hg, hp, hi, fun t => ⟨(hall t).1, ?_, ?_⟩⟩
  · apply entropy_integrable_of_bounded_support _ _
      (compressionBudget_ne_top K n (2 * R) hC) (hall t).1
      (B := B) measurableSet_closedBall
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ π hg hp p hR hs0 hs1).mono
      fun γ hγ => hγ.2 t
  · have hh := (hall t).2
    rw [entropyChord, he] at hh
    convert hh using 1 ; ring


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem entropy_plan_lp_signed_secant (μ : Measure X) [SigmaFinite μ]
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀]
    (hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal *
      Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (g : Lp ℝ 2 μ) (hrep : g =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hmap0 : π.map (fun γ => γ 0) = ν₀)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (K : ℝ) (t : Time) (ht : 0 < (t : ℝ))
    (het : Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
      Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ)
    (hc : boltzmannEntropy μ (π.map (fun γ => γ t)) ≤
      (1 - (t : ℝ)) * boltzmannEntropy μ ν₀ + (t : ℝ) * boltzmannEntropy μ ν₁ +
      ((-K) * (t : ℝ) * (1 - (t : ℝ)) / 2) *
        (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π)) :
    planInitialSecant π g t ≤ boltzmannEntropy μ ν₁ - boltzmannEntropy μ ν₀ -
      (K * (1 - (t : ℝ)) / 2) * (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π) := by
  have hac (s : Time) : π.map (fun γ => γ s) ≪ μ :=
    Measure.absolutelyContinuous_of_le_smul (hcomp s)
  have h0 : ν₀ ≪ μ := by rw [← hmap0]; exact hac 0
  have hi (s : Time) : Integrable g (π.map (fun γ => γ s)) :=
    ((Lp.memLp g).of_measure_le_smul hC (hcomp s)).integrable (by norm_num)
  have hip (s : Time) : Integrable (fun γ : C(Time, X) => g (γ s)) π :=
    (hi s).comp_measurable (measurable_path_eval s)
  let : IsProbabilityMeasure (π.map (fun γ => γ t)) :=
    inferInstance
  have hs := entropy_subgradient_rep μ ν₀ (π.map (fun γ => γ t)) h0 (hac t)
    hpos he0 het g hrep (hi t)
  have he (s : Time) : (∫ γ : C(Time, X), g (γ s) ∂π) =
      ∫ x, g x ∂(π.map (fun γ => γ s)) :=
    (integral_map (measurable_path_eval s).aemeasurable (hi s).aestronglyMeasurable).symm
  simp_rw [planInitialSecant, geodesicExtension_eq]
  rw [integral_sub (hip t) (hip 0), he t, he 0, hmap0]
  apply (div_le_iff₀ ht).mpr
  nlinarith only [hs, hc]

theorem entropy_plan_lp_signed_derivative_le (μ : Measure X) [SigmaFinite μ]
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀]
    (hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal *
      Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (g : Lp ℝ 2 μ) (hrep : g =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hmap0 : π.map (fun γ => γ 0) = ν₀)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (K : ℝ)
    (hconv : ∀ t : Time,
      Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
        Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ ∧
      boltzmannEntropy μ (π.map (fun γ => γ t)) ≤
        (1 - (t : ℝ)) * boltzmannEntropy μ ν₀ + (t : ℝ) * boltzmannEntropy μ ν₁ +
        ((-K) * (t : ℝ) * (1 - (t : ℝ)) / 2) *
          (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π))
    {d : ℝ} (hd : Tendsto (planInitialSecant π g) (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    d ≤ boltzmannEntropy μ ν₁ - boltzmannEntropy μ ν₀ -
      (K / 2) * (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π) := by
  have hlim : Tendsto (fun t : ℝ => boltzmannEntropy μ ν₁ - boltzmannEntropy μ ν₀ -
      (K * (1 - t) / 2) * (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π))
      (𝓝[>] (0 : ℝ)) (𝓝 (boltzmannEntropy μ ν₁ - boltzmannEntropy μ ν₀ -
        (K / 2) * (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π))) := by
    have hh : Continuous (fun t : ℝ => boltzmannEntropy μ ν₁ - boltzmannEntropy μ ν₀ -
        (K * (1 - t) / 2) * (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π)) := by fun_prop
    simpa using (hh.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hd hlim
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (gt_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht1 ht0
  exact entropy_plan_lp_signed_secant μ ν₀ ν₁ hpos he0 g hrep π hmap0 hC hcomp
    K ⟨t, le_of_lt ht0, ht1.le⟩ ht0 (hconv _).1 (hconv _).2

 

theorem compact_entropy_plan_sobolev_bound [CompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (hspace : IsGeodesicSpace X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal *
      Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (g : SobolevSpace μ hQ)
    (hlog : SobolevSpace.toLp μ hQ g =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (K : ℝ)
    (hconv : ∀ t : Time,
      Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
        Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ ∧
      boltzmannEntropy μ (π.map (fun γ => γ t)) ≤
        (1 - (t : ℝ)) * boltzmannEntropy μ ν₀ + (t : ℝ) * boltzmannEntropy μ ν₁ +
        ((-K) * (t : ℝ) * (1 - (t : ℝ)) / 2) *
          (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π)) :
    ∃ (u : SobolevSpace μ hQ) (φ ψ : X → ℝ) (M : ℝ≥0),
      LipschitzWith M φ ∧ LipschitzWith M ψ ∧
      (φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (∀ x y, φ x + ψ y ≤ dist x y^2 / 2) ∧
      (∀ᵐ γ ∂π, φ (γ 0) + ψ (γ 1) = dist (γ 0) (γ 1)^2 / 2) ∧
      -weightedGradientPair μ hQ ν₀ u g ≤
        boltzmannEntropy μ ν₁ - boltzmannEntropy μ ν₀ -
          (K / 2) * (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π) := by
  obtain ⟨u, φ, ψ, M, hφ, hψ, hu, had, hc, _, hvar⟩ :=
    compact_optimal_plan_signed_variation μ hQ hspace ν₀ ν₁ π hgeo hp hC hcomp
  exact ⟨u, φ, ψ, M, hφ, hψ, hu, had, hc,
    entropy_plan_lp_signed_derivative_le μ ν₀ ν₁ hpos he0 _ hlog π
      (optimalPlan_endpoints ν₀ ν₁ π hp).1 hC hcomp K hconv (hvar g)⟩


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace Bornology
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.compact_log_subgradient [CompactSpace X]
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (hpos : ∀ᵐ x ∂hausdorff n X, 0 < (ν₀.rnDeriv (hausdorff n X) x).toReal)
    (g : SobolevSpace (hausdorff n X) hX.quadratic)
    (hlog : SobolevSpace.toLp _ _ g =ᵐ[hausdorff n X]
      fun x => Real.log (ν₀.rnDeriv (hausdorff n X) x).toReal) :
    ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (φ ψ : X → ℝ) (M : ℝ≥0),
      LipschitzWith M φ ∧ LipschitzWith M ψ ∧
      (φ =ᵐ[hausdorff n X] SobolevSpace.toLp _ _ u) ∧
      (∀ x y, φ x + ψ y ≤ dist x y^2 / 2) ∧
      (∫ x, φ x ∂ν₀) + (∫ x, ψ x ∂ν₁) = (wassersteinSq ν₀ ν₁).toReal / 2 ∧
      -weightedGradientPair (hausdorff n X) hX.quadratic ν₀ u g ≤
        boltzmannEntropy (hausdorff n X) ν₁ - boltzmannEntropy (hausdorff n X) ν₀ -
          (K / 2) * (wassersteinSq ν₀ ν₁).toReal := by
  let : SeparableSpace X := hX.separable
  let : IsFiniteMeasure (hausdorff n X) := ⟨hX.finiteOnBounded univ (isBounded_univ.mpr inferInstance)⟩
  let μ := hausdorff n X
  have : Nonempty X := nonempty_of_isProbabilityMeasure ν₀
  obtain ⟨p⟩ := this
  obtain ⟨R, hR, hb⟩ := (isBounded_univ.mpr (inferInstance : BoundedSpace X)).subset_closedBall_lt (0 : ℝ) p
  have hs (ν : Measure X) : ∀ᵐ x ∂ν, dist x p ≤ R :=
    ae_of_all _ fun x => hb (mem_univ x)
  obtain ⟨π, hπ, hg, hp, hi, hall⟩ := hX.exists_bounded_entropy_plan K n hn
    ν₀ ν₁ hC h0 h1 p hR.le (hs ν₀) (hs ν₁)
  let := hπ
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ := by
    simpa only [hend.1] using (hall 0).2.1
  obtain ⟨u, φ, ψ, M, hφ, hψ, hu, had, hc, hbound⟩ :=
    compact_entropy_plan_sobolev_bound μ hX.quadratic hX.geodesic ν₀ ν₁ hpos he0
      g hlog π hg hp (compressionBudget_ne_top K n (2 * R) hC)
      (fun t => (hall t).1) K (fun t => (hall t).2)
  have he : (wassersteinSq ν₀ ν₁).toReal = ∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π := by
    rw [wassersteinSq_eq_cost hp, transportCost_plan_eq_integral π hi,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hiφ : Integrable φ ν₀ :=
    (hφ.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (p := 1)).integrable le_rfl
  have hiψ : Integrable ψ ν₁ :=
    (hψ.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (p := 1)).integrable le_rfl
  have hiφp : Integrable (fun γ : C(Time, X) => φ (γ 0)) π := by
    rw [← hend.1] at hiφ
    exact hiφ.comp_measurable (measurable_path_eval 0)
  have hiψp : Integrable (fun γ : C(Time, X) => ψ (γ 1)) π := by
    rw [← hend.2] at hiψ
    exact hiψ.comp_measurable (measurable_path_eval 1)
  have hdual := integral_congr_ae hc
  rw [integral_add hiφp hiψp, integral_div,
    ← integral_map (measurable_path_eval 0).aemeasurable hφ.continuous.aestronglyMeasurable,
    ← integral_map (measurable_path_eval 1).aemeasurable hψ.continuous.aestronglyMeasurable,
    hend.1, hend.2, ← he] at hdual
  exact ⟨u, φ, ψ, M, hφ, hψ, hu, had, hdual, he ▸ hbound⟩


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

theorem integral_sq_le_mass_mul_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ (μ univ).toReal * ∫ x, f x^2 ∂μ := by
  let u : Lp ℝ 2 μ := hf.toLp f
  let v : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp (fun _ => 1)
  have huv : inner ℝ u v = ∫ x, f x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, (memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp]
      with x hu hv
    simp only [u, v, Real.inner_apply, hu, hv, mul_one]
  have huu : inner ℝ u u = ∫ x, f x^2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [u, Real.inner_apply, hx, pow_two]
  have hvv : inner ℝ v v = (μ univ).toReal := by
    rw [L2.inner_def]
    have he : (fun x => inner ℝ (v x) (v x)) =ᵐ[μ] fun _ => (1 : ℝ) := by
      filter_upwards [(memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp] with x hx
      simp only [v, Real.inner_apply, hx, mul_one]
    rw [integral_congr_ae he]
    simp [Measure.real]
  have hh := real_inner_mul_inner_self_le u v
  rw [huv, huu, hvv] at hh
  simpa only [pow_two, mul_comm] using hh

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem testPlan_square_fubini (μ : Measure X) (π : Measure C(Time, X)) [IsFiniteMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) (G : Lp ℝ 2 μ) (t : Time) :
    Integrable (fun γ : C(Time, X) => ∫ r in Icc (0 : ℝ) (t : ℝ),
      G (geodesicExtension γ r)^2) π ∧
    (∫ γ : C(Time, X), (∫ r in Icc (0 : ℝ) (t : ℝ), G (geodesicExtension γ r)^2) ∂π) ≤
      (t : ℝ) * (C.toReal * ∫ x, G x^2 ∂μ) := by
  have hi := (testPlanMeasure_eval_memLp μ π hC hcomp G).integrable_sq
  have hit : Integrable (fun z : ℝ × C(Time, X) => G (geodesicExtension z.2 z.1)^2)
      ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod π) := by
    apply hi.mono_measure
    exact Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl t.2.2) le_rfl) le_rfl
  refine ⟨hit.integral_prod_right, ?_⟩
  rw [← integral_prod_symm _ hit, integral_prod _ hit]
  have hb (r : ℝ) : (∫ γ : C(Time, X), G (geodesicExtension γ r)^2 ∂π) ≤
      C.toReal * ∫ x, G x^2 ∂μ := by
    let s := Set.projIcc 0 1 zero_le_one r
    have hm : AEMeasurable (fun γ : C(Time, X) => γ s) π := (measurable_path_eval s).aemeasurable
    change (∫ γ : C(Time, X), G (γ s)^2 ∂π) ≤ _
    have hsm : AEStronglyMeasurable (fun x : X => G x^2) (π.map (fun γ => γ s)) :=
      ((Lp.stronglyMeasurable G).pow 2).aestronglyMeasurable
    rw [← integral_map hm hsm]
    have hh := integral_mono_measure (hcomp s) (ae_of_all _ fun x => sq_nonneg (G x))
      ((Lp.memLp G).integrable_sq.smul_measure hC)
    simpa only [integral_smul_measure, smul_eq_mul] using hh
  calc
    _ ≤ ∫ _ in Icc (0 : ℝ) (t : ℝ), C.toReal * ∫ x, G x^2 ∂μ :=
      integral_mono hit.integral_prod_left (integrable_const _) hb
    _ = _ := by simp [t.2.1]

theorem IsRelaxedSlope.testPlan_integrated_square (μ : Measure X)
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) (t : Time) :
    (∫ γ : C(Time, X), (u (γ t) - u (γ 0))^2 ∂π) ≤
      D^2 * (t : ℝ)^2 * (C.toReal * ∫ x, G x^2 ∂μ) := by
  have hiu (s : Time) : MemLp (fun γ : C(Time, X) => u (γ s)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval s) hC (hcomp s) u
  have hleft := ((hiu t).sub (hiu 0)).integrable_sq
  have hprod := (testPlanMeasure_eval_memLp μ π hC hcomp G).integrable_sq
  obtain ⟨hri, hbound⟩ := testPlan_square_fubini μ π hC hcomp G t
  have hae : ∀ᵐ γ ∂π, (u (γ t)-u (γ 0))^2 ≤
      D^2 * (t : ℝ) * ∫ r in Icc (0 : ℝ) (t : ℝ), G (geodesicExtension γ r)^2 := by
    filter_upwards [hG.testPlan_ae_subinterval μ π hgeo hC hcomp hD 0 t t.2.1,
      hprod.prod_left_ae, hDb] with γ hγ hi hdb
    change |u (γ t)-u (γ 0)| ≤ dist (γ 0) (γ 1) *
      (∫ r in (0 : ℝ)..(t : ℝ), G (geodesicExtension γ r)) at hγ
    have hmt : MemLp (fun r => G (geodesicExtension γ r)) 2
        (volume.restrict (Icc (0 : ℝ) (t : ℝ))) := by
      apply (memLp_two_iff_integrable_sq _).mpr
      · exact hi.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl t.2.2) le_rfl)
      · exact ((Lp.stronglyMeasurable G).comp_measurable
          (γ.continuous.comp (LipschitzWith.projIcc zero_le_one).continuous).measurable).aestronglyMeasurable
    have hcs := integral_sq_le_mass_mul_sq _ hmt
    simp only [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal t.2.1] at hcs
    have hsq : (u (γ t) - u (γ 0))^2 ≤
        dist (γ 0) (γ 1)^2 * (∫ r in Icc (0 : ℝ) (t : ℝ), G (geodesicExtension γ r))^2 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le t.2.1]
      have hh := mul_self_le_mul_self (abs_nonneg _) hγ
      simpa only [sq_abs, ← pow_two, mul_pow] using hh
    have hnon : 0 ≤ (t : ℝ) * ∫ r in Icc (0 : ℝ) (t : ℝ), G (geodesicExtension γ r)^2 :=
      mul_nonneg t.2.1 (integral_nonneg fun _ => sq_nonneg _)
    calc
      _ ≤ _ := hsq
      _ ≤ dist (γ 0) (γ 1)^2 * ((t : ℝ) *
          ∫ r in Icc (0 : ℝ) (t : ℝ), G (geodesicExtension γ r)^2) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ ≤ D^2 * ((t : ℝ) * ∫ r in Icc (0 : ℝ) (t : ℝ), G (geodesicExtension γ r)^2) :=
        mul_le_mul_of_nonneg_right (sq_le_sq₀ dist_nonneg (dist_nonneg.trans hdb) |>.mpr hdb) hnon
      _ = _ := by ring
  calc
    _ ≤ ∫ γ : C(Time, X), D^2 * (t : ℝ) *
        (∫ r in Icc (0 : ℝ) (t : ℝ), G (geodesicExtension γ r)^2) ∂π :=
      integral_mono_ae hleft (hri.const_mul _) hae
    _ = D^2 * (t : ℝ) * (∫ γ : C(Time, X),
        (∫ r in Icc (0 : ℝ) (t : ℝ), G (geodesicExtension γ r)^2) ∂π) := integral_const_mul _ _
    _ ≤ D^2 * (t : ℝ) * ((t : ℝ) * (C.toReal * ∫ x, G x^2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg (sq_nonneg _) t.2.1)
    _ = _ := by ring


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MetricSpace X] [BorelSpace X] in
 theorem uniformOn_le_scaled (μ : Measure X) (A : Set X) {C : ℝ≥0∞}
    (hC : (μ A)⁻¹ ≤ C) : uniformOn μ A ≤ C • μ := by
  apply Measure.le_iff.mpr
  intro s hs
  simp only [uniformOn,Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul hC (Measure.restrict_le_self s) bot_le bot_le

 theorem NoncollapsedRCD.dirichlet_integral_coercivity
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : hausdorff n X A ≠ 0) (hB0 : hausdorff n X B ≠ 0)
    (hsA : A ⊆ closedBall p R) (hsB : B ⊆ closedBall p R)
    {u G : Lp ℝ 2 (hausdorff n X)} (hG : IsRelaxedSlope (hausdorff n X) u G)
    (huB : u =ᵐ[(hausdorff n X).restrict B] 0) :
    (∫ x in A, (u x)^2 ∂hausdorff n X) ≤
      (hausdorff n X A).toReal * (2*R)^2 *
        (compressionBudget K n (2*R) (max (hausdorff n X A)⁻¹ (hausdorff n X B)⁻¹)).toReal *
          (∫ x, (G x)^2 ∂hausdorff n X) := by
  let μ := hausdorff n X
  let C : ℝ≥0∞ := max (μ A)⁻¹ (μ B)⁻¹
  have hAt : μ A ≠ ∞ := ne_of_lt (hX.finiteOnBounded A (isBounded_closedBall.subset hsA))
  have hBt : μ B ≠ ∞ := ne_of_lt (hX.finiteOnBounded B (isBounded_closedBall.subset hsB))
  have hC : C ≠ ∞ := max_ne_top (ENNReal.inv_ne_top.mpr hA0) (ENNReal.inv_ne_top.mpr hB0)
  let := uniformOn_probability μ A hA0 hAt
  let := uniformOn_probability μ B hB0 hBt
  have hbA : ∀ᵐ x ∂uniformOn μ A, dist x p ≤ R :=
    (uniformOn_ae_mem μ A hA).mono fun x hx => hsA hx
  have hbB : ∀ᵐ x ∂uniformOn μ B, dist x p ≤ R :=
    (uniformOn_ae_mem μ B hB).mono fun x hx => hsB hx
  obtain ⟨π,hπ,hgeo,hopt,hi,hall⟩ := hX.exists_bounded_entropy_plan K n hn
    (uniformOn μ A) (uniformOn μ B) hC (uniformOn_le_scaled μ A (le_max_left _ _))
    (uniformOn_le_scaled μ B (le_max_right _ _)) p hR hbA hbB
  let := hπ
  let := hX.separable
  have hend := optimalPlan_endpoints (uniformOn μ A) (uniformOn μ B) π hopt
  have hcap := compressionBudget_ne_top K n (2*R) hC
  have hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ compressionBudget K n (2*R) C • μ :=
    fun t => (hall t).1
  have hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π :=
    (memLp_two_iff_integrable_sq (((measurable_path_eval 0).dist
      (measurable_path_eval 1)).aestronglyMeasurable)).mpr hi
  have hDb := optimalPlanDistanceBound_of_bounded (uniformOn μ A) (uniformOn μ B) p hbA hbB π hπ hgeo hopt
  have hsq := hG.testPlan_integrated_square μ π hgeo hcap hcomp hD hDb (1:Time)
  have hzB : u =ᵐ[uniformOn μ B] 0 :=
    ((Measure.AbsolutelyContinuous.rfl : μ.restrict B ≪ μ.restrict B).smul_left ((μ B)⁻¹)).ae_le huB
  have hz : ∀ᵐ γ ∂π, u (γ 1)=0 := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 1).aemeasurable (p := fun x => u x=0)
    rw [hend.2]
    exact hzB
  have he : (∫ γ : C(Time,X), (u (γ 1)-u (γ 0))^2 ∂π) =
      (μ A).toReal⁻¹ * ∫ x in A, (u x)^2 ∂μ := by
    calc
      _ = ∫ γ : C(Time,X), (u (γ 0))^2 ∂π := integral_congr_ae (hz.mono fun γ hz => by simp [hz])
      _ = ∫ x, (u x)^2 ∂uniformOn μ A := by
        rw [←hend.1]
        exact (integral_map (measurable_path_eval 0).aemeasurable
          ((Lp.stronglyMeasurable u).pow 2).aestronglyMeasurable).symm
      _ = _ := by rw [uniformOn,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  rw [he] at hsq
  simp only [show ((1:Time):ℝ)=1 from rfl,one_pow,mul_one] at hsq
  have hpos : 0 < (μ A).toReal := ENNReal.toReal_pos hA0 hAt
  have hh := mul_le_mul_of_nonneg_left hsq hpos.le
  rw [←mul_assoc, mul_inv_cancel₀ hpos.ne',one_mul] at hh
  dsimp only [C,μ] at hh
  simpa only [mul_assoc] using hh


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

noncomputable def SobolevSpace.restrictLp (s : Set X) :
    SobolevSpace μ hQ →L[ℝ] Lp ℝ 2 (μ.restrict s) :=
  (Lp.LpToLpOfMeasureLeSMul (c := 1) (by norm_num)
    (by simpa using Measure.restrict_le_self (μ := μ) (s := s))).comp
      (SobolevSpace.toLpCLM μ hQ)

 theorem SobolevSpace.restrictLp_coe (s : Set X) (u : SobolevSpace μ hQ) :
    SobolevSpace.restrictLp μ hQ s u =ᵐ[μ.restrict s] SobolevSpace.toLp μ hQ u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by norm_num)
    (by simpa using Measure.restrict_le_self (μ := μ) (s := s)) _

 theorem SobolevSpace.restrictLp_eq_zero_iff (s : Set X) (u : SobolevSpace μ hQ) :
    SobolevSpace.restrictLp μ hQ s u = 0 ↔
      SobolevSpace.toLp μ hQ u =ᵐ[μ.restrict s] 0 := by
  constructor
  · intro h
    exact (SobolevSpace.restrictLp_coe μ hQ s u).symm.trans (h ▸ Lp.coeFn_zero _ _ _)
  · intro h
    apply Lp.ext
    exact (SobolevSpace.restrictLp_coe μ hQ s u).trans (h.trans (Lp.coeFn_zero _ _ _).symm)

noncomputable def SobolevSpace.dirichletCore (Ω : Set X) : Submodule ℝ (SobolevSpace μ hQ) where
  carrier := {u | ∃ (f : X → ℝ) (C : ℝ≥0), LipschitzWith C f ∧ HasCompactSupport f ∧
    tsupport f ⊆ Ω ∧ SobolevSpace.toLp μ hQ u =ᵐ[μ] f}
  zero_mem' := by
    refine ⟨0,0,?_,?_,?_,?_⟩
    · exact LipschitzWith.const 0
    · exact HasCompactSupport.zero
    · simp
    · simpa only [map_zero] using (Lp.coeFn_zero ℝ 2 μ)
  add_mem' := by
    rintro u v ⟨f,C,hf,hfc,hfs,hfu⟩ ⟨g,D,hg,hgc,hgs,hgv⟩
    refine ⟨f+g,C+D,hf.add hg,hfc.add hgc,?_,?_⟩
    · exact (tsupport_add f g).trans (union_subset hfs hgs)
    · exact (Lp.coeFn_add _ _).trans (hfu.add hgv)
  smul_mem' := by
    rintro c u ⟨f,C,hf,hfc,hfs,hfu⟩
    refine ⟨c • f,‖c‖₊*C,?_,hfc.smul_left,?_,?_⟩
    · exact (lipschitzWith_smul c).comp hf
    · exact (tsupport_smul_subset_right (fun _ => c) f).trans hfs
    · exact (Lp.coeFn_smul c _).trans (hfu.const_smul c)

 
noncomputable def SobolevSpace.dirichlet (Ω : Set X) : Submodule ℝ (SobolevSpace μ hQ) :=
  (SobolevSpace.dirichletCore μ hQ Ω).topologicalClosure

instance SobolevSpace.dirichlet_completeSpace (Ω : Set X) :
    CompleteSpace (SobolevSpace.dirichlet μ hQ Ω) := by
  unfold SobolevSpace.dirichlet
  infer_instance

 theorem SobolevSpace.dirichlet_zero_off (Ω : Set X) (hΩ : MeasurableSet Ω)
    (u : SobolevSpace.dirichlet μ hQ Ω) :
    SobolevSpace.toLp μ hQ u.val =ᵐ[μ.restrict Ωᶜ] 0 := by
  apply (SobolevSpace.restrictLp_eq_zero_iff μ hQ Ωᶜ u.val).mp
  have hsub : SobolevSpace.dirichlet μ hQ Ω ≤ (SobolevSpace.restrictLp μ hQ Ωᶜ).ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro v ⟨f,C,hf,hfc,hfs,hfv⟩
      apply (SobolevSpace.restrictLp_eq_zero_iff μ hQ Ωᶜ v).mpr
      have hh := ae_restrict_of_ae (s := Ωᶜ) hfv
      filter_upwards [hh,ae_restrict_mem hΩ.compl] with x hx hxc
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport (fun h => hxc (hfs h))
    · exact (SobolevSpace.restrictLp μ hQ Ωᶜ).isClosed_ker
  exact hsub u.property


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem energyForm_multiplier_lower (f g : SobolevSpace μ hQ)
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (c : ℝ) (hs : HasCompactSupport (fun x => v x-c))
    (hb : ∀ x, |v x| ≤ B)
    (V : Lp ℝ ∞ μ) (hV : ⇑V =ᵐ[μ] v)
    (hfg : SobolevSpace.toLp μ hQ g = lpMultiplier μ V (SobolevSpace.toLp μ hQ f)) :
    inner ℝ (SobolevSpace.minimalSlope μ hQ f)
      (lpMultiplier μ V (SobolevSpace.minimalSlope μ hQ f) -
        (C:ℝ) • lpAbs μ (SobolevSpace.toLp μ hQ f)) ≤ energyForm μ hQ f g := by
  let F := SobolevSpace.toLp μ hQ f
  let G := SobolevSpace.minimalSlope μ hQ f
  let H := lpMultiplier μ V G-(C:ℝ) • lpAbs μ F
  apply energyForm_lower_of_slope_variations μ hQ f g H
    (r := 1/((B:ℝ)+1)) (by positivity)
  intro δ hδ
  have hdB : δ*(B:ℝ) < 1 := by
    have hh := (lt_div_iff₀ (show 0 < (B:ℝ)+1 by positivity)).mp hδ.2
    nlinarith only [hh,hδ.1]
  let θ : X → ℝ := fun x => 1-δ*v x
  have ht (x : X) : 0 ≤ θ x ∧ θ x ≤ 2 := by
    have hx := (abs_le.mp (hb x))
    have hup := mul_le_mul_of_nonneg_left hx.2 hδ.1.le
    have hlo := mul_le_mul_of_nonneg_left hx.1 hδ.1.le
    dsimp [θ]
    constructor <;> nlinarith only [hup,hlo,hdB]
  have htLip : LipschitzWith (‖δ‖₊*C) θ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := (lipschitzWith_const_mul_real hv δ).dist_le_mul x y
    simpa only [θ,Real.dist_eq,sub_sub_sub_cancel_left,abs_sub_comm] using hh
  have htC : HasCompactSupport (fun x => θ x-(1-δ*c)) := by
    convert! (hs.mul_left (f := fun _ : X => -δ)) using 1
    funext x
    dsimp [θ]
    ring
  have htB (x : X) : |θ x| ≤ (2:ℝ≥0) := by
    rw [abs_of_nonneg (ht x).1]
    exact (ht x).2
  have htS (x : X) : localSlope θ x ≤ ENNReal.ofReal (δ*(C:ℝ)) := by
    have he : θ = fun x => (-δ)*v x-(-1) := by funext x; dsimp [θ]; ring
    rw [he,localSlope_sub_const,localSlope_const_mul,abs_neg,abs_of_pos hδ.1]
    calc
      _ ≤ ENNReal.ofReal δ * (C:ℝ≥0∞) := mul_le_mul' le_rfl (localSlope_le_of_lipschitz hv x)
      _ = _ := by rw [←ENNReal.ofReal_coe_nnreal,←ENNReal.ofReal_mul hδ.1.le]
  let T := boundedMultiplier μ θ htLip.continuous.measurable 2 htB
  have hT : ⇑T =ᵐ[μ] θ := boundedMultiplier_coe μ _ _ _ _
  let W := boundedMultiplier μ (fun _ : X => δ*(C:ℝ)) measurable_const ‖δ*(C:ℝ)‖₊
    (fun _ => by simp only [Real.norm_eq_abs,coe_nnnorm]; exact le_rfl)
  have hW : ⇑W =ᵐ[μ] (fun _ : X => δ*(C:ℝ)) := boundedMultiplier_coe μ _ _ _ _
  have hr := (SobolevSpace.minimalSlope_isRelaxed μ hQ f).mul_lipschitz μ
    htLip (1-δ*c) htC htB (fun x => (ht x).1)
    (fun _ => mul_nonneg hδ.1.le C.coe_nonneg) htS T W hT hW
  have hTF : lpMultiplier μ T F = SobolevSpace.toLp μ hQ (f-δ • g) := by
    rw [map_sub,map_smul,hfg]
    apply Lp.ext
    filter_upwards [lpMultiplier_coe μ T F,lpMultiplier_coe μ V F,
      Lp.coeFn_sub F (δ • lpMultiplier μ V F),Lp.coeFn_smul δ (lpMultiplier μ V F),hT,hV]
      with x htF hvF hsub hsm ht0 hv0
    rw [htF,hsub,Pi.sub_apply,hsm,Pi.smul_apply,smul_eq_mul,ht0,hvF,hv0]
    dsimp [θ]
    ring
  have hTH : lpMultiplier μ T G+lpMultiplier μ W (lpAbs μ F) = G-δ • H := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (lpMultiplier μ T G) (lpMultiplier μ W (lpAbs μ F)),
      Lp.coeFn_sub G (δ • H),Lp.coeFn_smul δ H,
      Lp.coeFn_sub (lpMultiplier μ V G) ((C:ℝ) • lpAbs μ F),Lp.coeFn_smul (C:ℝ) (lpAbs μ F),
      lpMultiplier_coe μ T G,lpMultiplier_coe μ W (lpAbs μ F),lpMultiplier_coe μ V G,hT,hV,hW]
      with x hadd hsub hsm hH hC htG hwF hvG ht0 hv0 hw0
    dsimp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at *
    rw [hadd,hsub,hsm,htG,hwF,ht0,hw0]
    change H x = _ at hH
    rw [hH,hC,hvG,hv0]
    dsimp only [θ]
    ring
  rwa [hTF,hTH] at hr


end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] in
 theorem lpMultiplier_neg_weight (V : Lp ℝ ∞ μ) (F : Lp ℝ 2 μ) :
    lpMultiplier μ (-V) F = -lpMultiplier μ V F := by
  apply Lp.ext
  filter_upwards [lpMultiplier_coe μ (-V) F,lpMultiplier_coe μ V F,
    Lp.coeFn_neg V,Lp.coeFn_neg (lpMultiplier μ V F)] with x h1 h2 h3 h4
  simp only [h1,h2,h3,h4,Pi.neg_apply,neg_mul]

omit [MetricSpace X] [BorelSpace X] in
 theorem lpAbs_norm (F : Lp ℝ 2 μ) : ‖lpAbs μ F‖ = ‖F‖ := by
  simp only [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable (lpAbs μ F))
    (Lp.aestronglyMeasurable F)
  filter_upwards [lpAbs_coe μ F] with x hx
  simp only [hx,Real.norm_eq_abs,abs_abs]

 theorem energyForm_multiplier_error (f g : SobolevSpace μ hQ)
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (c : ℝ) (hs : HasCompactSupport (fun x => v x-c))
    (hb : ∀ x, |v x| ≤ B)
    (V : Lp ℝ ∞ μ) (hV : ⇑V =ᵐ[μ] v)
    (hfg : SobolevSpace.toLp μ hQ g = lpMultiplier μ V (SobolevSpace.toLp μ hQ f)) :
    |energyForm μ hQ f g - inner ℝ (SobolevSpace.minimalSlope μ hQ f)
      (lpMultiplier μ V (SobolevSpace.minimalSlope μ hQ f))| ≤
      (C:ℝ)*‖SobolevSpace.minimalSlope μ hQ f‖*‖SobolevSpace.toLp μ hQ f‖ := by
  have hs' : HasCompactSupport (fun x => -v x-(-c)) := by
    have he : (fun x => -v x-(-c)) = -(fun x => v x-c) := by
      funext x
      simp only [Pi.neg_apply]
      ring
    rw [he]
    exact hs.neg
  have hV' : ⇑(-V) =ᵐ[μ] (fun x => -v x) := by
    filter_upwards [Lp.coeFn_neg V,hV] with x hn hv
    simp only [hn,Pi.neg_apply,hv]
  have hfg' : SobolevSpace.toLp μ hQ (-g) = lpMultiplier μ (-V) (SobolevSpace.toLp μ hQ f) := by
    rw [map_neg,lpMultiplier_neg_weight,hfg]
  have hlo := energyForm_multiplier_lower μ hQ f g hv c hs hb V hV hfg
  have hup := energyForm_multiplier_lower μ hQ f (-g) (v := fun x => -v x) (B := B) hv.neg (-c) hs'
    (fun x => by simpa only [abs_neg] using hb x) (-V) hV' hfg'
  rw [lpMultiplier_neg_weight,inner_sub_right,inner_neg_right,real_inner_smul_right] at hup
  have he : energyForm μ hQ f (-g) = -energyForm μ hQ f g := by
    simp only [energyForm,map_neg,inner_neg_right]; ring
  rw [he] at hup
  rw [inner_sub_right,real_inner_smul_right] at hlo
  have hh := real_inner_le_norm (SobolevSpace.minimalSlope μ hQ f)
    (lpAbs μ (SobolevSpace.toLp μ hQ f))
  rw [lpAbs_norm] at hh
  have hm := mul_le_mul_of_nonneg_left hh C.coe_nonneg
  apply abs_le.mpr
  constructor <;> nlinarith only [hlo,hup,hm]


end

 
section

 

open Set Filter Metric
open scoped Topology

noncomputable def integerFold (x : ℝ) : ℝ := infDist x (range ((↑) : ℤ → ℝ))

 theorem integerFold_lipschitz : LipschitzWith 1 integerFold := lipschitz_infDist_pt _

@[simp] theorem integerFold_zero : integerFold 0 = 0 := by
  apply infDist_zero_of_mem
  exact ⟨0, Int.cast_zero⟩

 theorem integerFold_nonneg (x : ℝ) : 0 ≤ integerFold x := infDist_nonneg

 theorem integerFold_le_one (x : ℝ) : integerFold x ≤ 1 := by
  have he := infDist_le_dist_of_mem (x := x) (show (⌊x⌋ : ℝ) ∈ range ((↑) : ℤ → ℝ) from ⟨⌊x⌋, rfl⟩)
  apply he.trans
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le x))]
  have hh := Int.lt_floor_add_one x
  linarith

 theorem integerFold_affine (x : ℝ) :
    ∃ k : ℤ, integerFold x = x-(k:ℝ) ∨ integerFold x = -(x-(k:ℝ)) := by
  obtain ⟨y, ⟨k,rfl⟩, hy⟩ := Real.isClosed_range_intCast.exists_infDist_eq_dist
    (show (range ((↑):ℤ → ℝ)).Nonempty from ⟨0,0,Int.cast_zero⟩) x
  refine ⟨k, ?_⟩
  change integerFold x = dist x (k:ℝ) at hy
  rw [hy, Real.dist_eq]
  by_cases h : 0 ≤ x-(k:ℝ)
  · exact Or.inl (abs_of_nonneg h)
  · exact Or.inr (abs_of_nonpos (le_of_not_ge h))

noncomputable def scalarFold (ε : ℝ) (x : ℝ) : ℝ := ε*integerFold (x/ε)

@[simp] theorem scalarFold_zero (ε : ℝ) : scalarFold ε 0 = 0 := by simp [scalarFold]

 theorem scalarFold_lipschitz {ε : ℝ} (hε : 0 < ε) : LipschitzWith 1 (scalarFold ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := integerFold_lipschitz.dist_le_mul (x/ε) (y/ε)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hh ⊢
  calc
    |scalarFold ε x-scalarFold ε y| = ε*|integerFold (x/ε)-integerFold (y/ε)| := by
      rw [scalarFold,scalarFold,←mul_sub,abs_mul,abs_of_pos hε]
    _ ≤ ε*|x/ε-y/ε| := mul_le_mul_of_nonneg_left hh hε.le
    _ = |x-y| := by rw [←sub_div,abs_div,abs_of_pos hε]; field_simp

 theorem scalarFold_bounds {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ scalarFold ε x ∧ scalarFold ε x ≤ ε := by
  refine ⟨mul_nonneg hε.le (integerFold_nonneg _), ?_⟩
  simpa only [scalarFold, mul_one] using mul_le_mul_of_nonneg_left (integerFold_le_one (x/ε)) hε.le

 theorem scalarFold_affine {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ∃ k : ℤ, scalarFold ε x = x-ε*(k:ℝ) ∨ scalarFold ε x = -(x-ε*(k:ℝ)) := by
  obtain ⟨k, hk|hk⟩ := integerFold_affine (x/ε)
  · refine ⟨k, Or.inl ?_⟩
    rw [scalarFold,hk,mul_sub,mul_div_cancel₀ _ hε.ne']
  · refine ⟨k, Or.inr ?_⟩
    rw [scalarFold,hk,mul_neg,mul_sub,mul_div_cancel₀ _ hε.ne']

 theorem scalarFold_tendsto {ε : ℕ → ℝ} (hε : ∀ i, 0 < ε i)
    (he : Tendsto ε atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun i => scalarFold (ε i) x) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (fun i => (scalarFold_bounds (hε i) x).1) (fun i => (scalarFold_bounds (hε i) x).2)


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.minimalSlope_eq_on_diff_level (f g : SobolevSpace μ hQ) (c : ℝ) :
    ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x-SobolevSpace.toLp μ hQ g x = c →
      SobolevSpace.minimalSlope μ hQ f x = SobolevSpace.minimalSlope μ hQ g x := by
  have hf := SobolevSpace.minimalSlope_add_le μ hQ (f-g) g
  rw [sub_add_cancel] at hf
  have hg := SobolevSpace.minimalSlope_add_le μ hQ (g-f) f
  rw [sub_add_cancel, ← neg_sub f g, SobolevSpace.minimalSlope_neg] at hg
  have hz := SobolevSpace.minimalSlope_zero_on_level μ hQ (f-g) c
  rw [map_sub] at hz
  filter_upwards [(Lp.coeFn_le _ _).mpr hf, (Lp.coeFn_le _ _).mpr hg, hz,
    Lp.coeFn_add (SobolevSpace.minimalSlope μ hQ (f-g)) (SobolevSpace.minimalSlope μ hQ g),
    Lp.coeFn_add (SobolevSpace.minimalSlope μ hQ (f-g)) (SobolevSpace.minimalSlope μ hQ f),
    Lp.coeFn_sub (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)]
    with x hf hg hz ha hb hs
  intro hfg
  have he : SobolevSpace.minimalSlope μ hQ (f-g) x = 0 := hz (by simpa only [hs,Pi.sub_apply] using hfg)
  simp only [ha,hb,Pi.add_apply,he,zero_add] at hf hg
  exact le_antisymm hf hg

noncomputable def SobolevSpace.fold (f : SobolevSpace μ hQ) (ε : ℝ) (hε : 0 < ε) :
    SobolevSpace μ hQ := SobolevSpace.comp μ hQ (scalarFold_lipschitz hε) (scalarFold_zero ε) f

omit [BorelSpace X] [ProperSpace X] in
 theorem SobolevSpace.fold_coe (f : SobolevSpace μ hQ) {ε : ℝ} (hε : 0 < ε) :
    SobolevSpace.toLp μ hQ (f.fold μ hQ ε hε) =ᵐ[μ]
      fun x => scalarFold ε (SobolevSpace.toLp μ hQ f x) :=
  SobolevSpace.comp_coe μ hQ (scalarFold_lipschitz hε) (scalarFold_zero ε) f

 theorem SobolevSpace.minimalSlope_fold (f : SobolevSpace μ hQ) {ε : ℝ} (hε : 0 < ε) :
    SobolevSpace.minimalSlope μ hQ (f.fold μ hQ ε hε) = SobolevSpace.minimalSlope μ hQ f := by
  let F := f.fold μ hQ ε hε
  have hp : ∀ᵐ x ∂μ, ∀ k : ℤ, SobolevSpace.toLp μ hQ F x-SobolevSpace.toLp μ hQ f x = -ε*(k:ℝ) →
      SobolevSpace.minimalSlope μ hQ F x = SobolevSpace.minimalSlope μ hQ f x :=
    ae_all_iff.mpr fun k => SobolevSpace.minimalSlope_eq_on_diff_level μ hQ F f (-ε*(k:ℝ))
  have hn : ∀ᵐ x ∂μ, ∀ k : ℤ, SobolevSpace.toLp μ hQ F x-SobolevSpace.toLp μ hQ (-f) x = ε*(k:ℝ) →
      SobolevSpace.minimalSlope μ hQ F x = SobolevSpace.minimalSlope μ hQ (-f) x :=
    ae_all_iff.mpr fun k => SobolevSpace.minimalSlope_eq_on_diff_level μ hQ F (-f) (ε*(k:ℝ))
  rw [SobolevSpace.minimalSlope_neg, map_neg] at hn
  apply Lp.ext
  filter_upwards [hp,hn,SobolevSpace.fold_coe μ hQ f hε,Lp.coeFn_neg (SobolevSpace.toLp μ hQ f)]
    with x hp hn hF hneg
  obtain ⟨k,hk|hk⟩ := scalarFold_affine hε (SobolevSpace.toLp μ hQ f x)
  · apply hp k
    change SobolevSpace.toLp μ hQ (f.fold μ hQ ε hε) x-_ = _
    rw [hF,hk]
    ring
  · apply hn k
    change SobolevSpace.toLp μ hQ (f.fold μ hQ ε hε) x-_ = _
    rw [hF,hk,hneg]
    simp only [Pi.neg_apply]
    ring

omit [BorelSpace X] [ProperSpace X] in
 theorem SobolevSpace.fold_tendsto_zero (f : SobolevSpace μ hQ) {ε : ℕ → ℝ}
    (hε : ∀ i, 0 < ε i) (he : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun i => SobolevSpace.toLp μ hQ (f.fold μ hQ (ε i) (hε i))) atTop (𝓝 0) := by
  have hz : LipschitzWith (1:ℝ≥0) (fun _ : ℝ => (0:ℝ)) := (LipschitzWith.const (0 : ℝ)).weaken (by norm_num)
  have hh := compLp_tendsto_of_pointwise μ (fun i => scalarFold_lipschitz (hε i))
    hz (fun i => scalarFold_zero (ε i)) rfl (scalarFold_tendsto hε he) (SobolevSpace.toLp μ hQ f)
  have hzlp : hz.compLp rfl (SobolevSpace.toLp μ hQ f) = 0 := by
    apply Lp.ext
    filter_upwards [hz.coeFn_compLp rfl (SobolevSpace.toLp μ hQ f),Lp.coeFn_zero ℝ 2 μ] with x hx hzero
    simpa only [Function.comp_apply,hzero,Pi.zero_apply] using hx
  rw [hzlp] at hh
  exact hh


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

noncomputable def SobolevSpace.signed (b : Bool) (f : SobolevSpace μ hQ) : SobolevSpace μ hQ :=
  if b then f else -f

noncomputable def slopePair (f g : SobolevSpace μ hQ) (x : X) : ℝ :=
  SobolevSpace.minimalSlope μ hQ (f+g) x^2+SobolevSpace.minimalSlope μ hQ (f-g) x^2

omit [ProperSpace X] in
 theorem slopePair_signed (f g : SobolevSpace μ hQ) (b c : Bool) (x : X) :
    slopePair μ hQ (SobolevSpace.signed μ hQ b f) (SobolevSpace.signed μ hQ c g) x =
      slopePair μ hQ f g x := by
  cases b <;> cases c <;> simp only [SobolevSpace.signed, Bool.false_eq_true,↓reduceIte,slopePair]
  · have h1 : -f + -g = -(f+g) := by abel
    have h2 : -f - -g = -(f-g) := by abel
    rw [h1,h2,SobolevSpace.minimalSlope_neg,SobolevSpace.minimalSlope_neg]
  · have h1 : -f+g = -(f-g) := by abel
    have h2 : -f-g = -(f+g) := by abel
    rw [h1,h2,SobolevSpace.minimalSlope_neg,SobolevSpace.minimalSlope_neg,add_comm]
  · simp only [←sub_eq_add_neg,sub_neg_eq_add,add_comm]

 theorem slopePair_on_affine (f g F G : SobolevSpace μ hQ) (a b : ℝ) :
    ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ F x = SobolevSpace.toLp μ hQ f x+a →
      SobolevSpace.toLp μ hQ G x = SobolevSpace.toLp μ hQ g x+b →
      slopePair μ hQ F G x = slopePair μ hQ f g x := by
  have hp := SobolevSpace.minimalSlope_eq_on_diff_level μ hQ (F+G) (f+g) (a+b)
  have hn := SobolevSpace.minimalSlope_eq_on_diff_level μ hQ (F-G) (f-g) (a-b)
  filter_upwards [hp,hn,
    Lp.coeFn_add (SobolevSpace.toLp μ hQ F) (SobolevSpace.toLp μ hQ G),
    Lp.coeFn_add (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g),
    Lp.coeFn_sub (SobolevSpace.toLp μ hQ F) (SobolevSpace.toLp μ hQ G),
    Lp.coeFn_sub (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)]
    with x hp hn hFG hfg hFG' hfg'
  intro hF hG
  have he : SobolevSpace.minimalSlope μ hQ (F+G) x = SobolevSpace.minimalSlope μ hQ (f+g) x := by
    apply hp
    simp only [map_add,hFG,hfg,Pi.add_apply,hF,hG]
    ring
  have he' : SobolevSpace.minimalSlope μ hQ (F-G) x = SobolevSpace.minimalSlope μ hQ (f-g) x := by
    apply hn
    simp only [map_sub,hFG',hfg',Pi.sub_apply,hF,hG]
    ring
  simp only [slopePair,he,he']

noncomputable def foldShift (ε : ℝ) (k : ℤ) (b : Bool) : ℝ :=
  if b then -ε*(k:ℝ) else ε*(k:ℝ)

omit [BorelSpace X] [ProperSpace X] in
 theorem SobolevSpace.fold_affine_coe (f : SobolevSpace μ hQ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂μ, ∃ k : ℤ, ∃ b : Bool, SobolevSpace.toLp μ hQ (f.fold μ hQ ε hε) x =
      SobolevSpace.toLp μ hQ (SobolevSpace.signed μ hQ b f) x+foldShift ε k b := by
  filter_upwards [SobolevSpace.fold_coe μ hQ f hε,Lp.coeFn_neg (SobolevSpace.toLp μ hQ f)] with x hF hn
  obtain ⟨k,hk|hk⟩ := scalarFold_affine hε (SobolevSpace.toLp μ hQ f x)
  · refine ⟨k,true,?_⟩
    simp only [hF,hk,SobolevSpace.signed,foldShift,↓reduceIte]
    ring
  · refine ⟨k,false,?_⟩
    simp only [hF,hk,SobolevSpace.signed,foldShift,Bool.false_eq_true,↓reduceIte,map_neg,hn,Pi.neg_apply]
    ring

 theorem slopePair_fold (f g : SobolevSpace μ hQ) {ε : ℝ} (hε : 0 < ε) :
    slopePair μ hQ (f.fold μ hQ ε hε) (g.fold μ hQ ε hε) =ᵐ[μ] slopePair μ hQ f g := by
  have hp : ∀ᵐ x ∂μ, ∀ k l : ℤ, ∀ b c : Bool,
      SobolevSpace.toLp μ hQ (f.fold μ hQ ε hε) x =
        SobolevSpace.toLp μ hQ (SobolevSpace.signed μ hQ b f) x+foldShift ε k b →
      SobolevSpace.toLp μ hQ (g.fold μ hQ ε hε) x =
        SobolevSpace.toLp μ hQ (SobolevSpace.signed μ hQ c g) x+foldShift ε l c →
      slopePair μ hQ (f.fold μ hQ ε hε) (g.fold μ hQ ε hε) x = slopePair μ hQ f g x := by
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro l
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro c
    filter_upwards [slopePair_on_affine μ hQ (SobolevSpace.signed μ hQ b f)
      (SobolevSpace.signed μ hQ c g) (f.fold μ hQ ε hε) (g.fold μ hQ ε hε)
      (foldShift ε k b) (foldShift ε l c)] with x hx
    intro hF hG
    exact (hx hF hG).trans (slopePair_signed μ hQ f g b c x)
  filter_upwards [hp,SobolevSpace.fold_affine_coe μ hQ f hε,SobolevSpace.fold_affine_coe μ hQ g hε]
    with x hx ⟨k,b,hF⟩ ⟨l,c,hG⟩
  exact hx k l b c hF hG


end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

noncomputable def SobolevSpace.mulLipschitzLinear
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (c : ℝ) (hs : HasCompactSupport (fun x => v x-c))
    (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (V : Lp ℝ ∞ μ) (hV : ⇑V =ᵐ[μ] v) : SobolevSpace μ hQ →ₗ[ℝ] SobolevSpace μ hQ where
  toFun f := f.mulLipschitz μ hQ hv c hs hb hn V hV
  map_add' f g := by apply Subtype.ext; exact map_add (lpMultiplier μ V) _ _
  map_smul' a f := by apply Subtype.ext; exact map_smul (lpMultiplier μ V) a _

noncomputable def multiplierGradientSquare (V : Lp ℝ ∞ μ) (f : SobolevSpace μ hQ) : ℝ :=
  inner ℝ (SobolevSpace.minimalSlope μ hQ f)
    (lpMultiplier μ V (SobolevSpace.minimalSlope μ hQ f))

 theorem multiplierGradientSquare_integrable (V : Lp ℝ ∞ μ) (f : SobolevSpace μ hQ) :
    Integrable (fun x => V x*SobolevSpace.minimalSlope μ hQ f x^2) μ := by
  apply (L2.integrable_inner (SobolevSpace.minimalSlope μ hQ f)
    (lpMultiplier μ V (SobolevSpace.minimalSlope μ hQ f))).congr
  filter_upwards [lpMultiplier_coe μ V (SobolevSpace.minimalSlope μ hQ f)] with x hx
  simp only [hx,Real.inner_apply]
  ring

 theorem multiplierGradientSquare_integral (V : Lp ℝ ∞ μ) (f : SobolevSpace μ hQ) :
    multiplierGradientSquare μ hQ V f = ∫x, V x*SobolevSpace.minimalSlope μ hQ f x^2 ∂μ := by
  rw [multiplierGradientSquare,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lpMultiplier_coe μ V (SobolevSpace.minimalSlope μ hQ f)] with x hx
  simp only [hx,Real.inner_apply]
  ring

omit [BorelSpace X] in
 theorem energyForm_linear_parallelogram (M : SobolevSpace μ hQ →ₗ[ℝ] SobolevSpace μ hQ)
    (f g : SobolevSpace μ hQ) :
    energyForm μ hQ (f+g) (M (f+g)) + energyForm μ hQ (f-g) (M (f-g)) =
      2*energyForm μ hQ f (M f)+2*energyForm μ hQ g (M g) := by
  simp only [map_add,map_sub,energyForm,inner_add_left,inner_sub_left,inner_add_right,
    inner_sub_right]
  ring

 theorem multiplierGradientSquare_error_tendsto
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (c : ℝ) (hs : HasCompactSupport (fun x => v x-c))
    (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (V : Lp ℝ ∞ μ) (hV : ⇑V =ᵐ[μ] v)
    (fs : ℕ → SobolevSpace μ hQ) {D : ℝ} (hD : ∀ i, ‖SobolevSpace.minimalSlope μ hQ (fs i)‖ ≤ D)
    (hf : Tendsto (fun i => SobolevSpace.toLp μ hQ (fs i)) atTop (𝓝 0)) :
    Tendsto (fun i => energyForm μ hQ (fs i)
      (SobolevSpace.mulLipschitzLinear μ hQ hv c hs hb hn V hV (fs i)) -
      multiplierGradientSquare μ hQ V (fs i)) atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun i => (C:ℝ)*D*‖SobolevSpace.toLp μ hQ (fs i)‖) ?_ ?_
  · intro i
    rw [Real.norm_eq_abs]
    exact (energyForm_multiplier_error μ hQ (fs i) _ hv c hs hb V hV rfl).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hD i) C.coe_nonneg) (norm_nonneg _))
  · simpa using hf.norm.const_mul ((C:ℝ)*D)

variable [ProperSpace X]

 theorem minimalSlope_norm_add_le (f g : SobolevSpace μ hQ) :
    ‖SobolevSpace.minimalSlope μ hQ (f+g)‖ ≤
      ‖SobolevSpace.minimalSlope μ hQ f‖+‖SobolevSpace.minimalSlope μ hQ g‖ := by
  apply le_trans (b := ‖SobolevSpace.minimalSlope μ hQ f+SobolevSpace.minimalSlope μ hQ g‖)
  · apply norm_le_norm_of_abs_le_abs
    rw [abs_of_nonneg (SobolevSpace.minimalSlope_nonneg μ hQ (f+g)),
      abs_of_nonneg (add_nonneg (SobolevSpace.minimalSlope_nonneg μ hQ f)
        (SobolevSpace.minimalSlope_nonneg μ hQ g))]
    exact SobolevSpace.minimalSlope_add_le μ hQ f g
  · exact norm_add_le _ _

 theorem multiplierGradientSquare_fold (V : Lp ℝ ∞ μ) (f : SobolevSpace μ hQ)
    {ε : ℝ} (hε : 0 < ε) : multiplierGradientSquare μ hQ V (f.fold μ hQ ε hε) =
      multiplierGradientSquare μ hQ V f := by
  simp only [multiplierGradientSquare,SobolevSpace.minimalSlope_fold]

 theorem multiplierGradientSquare_fold_pair (V : Lp ℝ ∞ μ) (f g : SobolevSpace μ hQ)
    {ε : ℝ} (hε : 0 < ε) :
    multiplierGradientSquare μ hQ V (f.fold μ hQ ε hε+g.fold μ hQ ε hε) +
      multiplierGradientSquare μ hQ V (f.fold μ hQ ε hε-g.fold μ hQ ε hε) =
    multiplierGradientSquare μ hQ V (f+g)+multiplierGradientSquare μ hQ V (f-g) := by
  simp only [multiplierGradientSquare_integral]
  rw [←integral_add (multiplierGradientSquare_integrable μ hQ V _)
    (multiplierGradientSquare_integrable μ hQ V _),
    ←integral_add (multiplierGradientSquare_integrable μ hQ V _)
    (multiplierGradientSquare_integrable μ hQ V _)]
  apply integral_congr_ae
  filter_upwards [slopePair_fold μ hQ f g hε] with x hx
  simp only [slopePair] at hx
  simpa only [←mul_add] using congrArg (V x*·) hx


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem multiplierGradientSquare_parallelogram
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (c : ℝ) (hs : HasCompactSupport (fun x => v x-c))
    (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (V : Lp ℝ ∞ μ) (hV : ⇑V =ᵐ[μ] v) (f g : SobolevSpace μ hQ) :
    multiplierGradientSquare μ hQ V (f+g)+multiplierGradientSquare μ hQ V (f-g) =
      2*multiplierGradientSquare μ hQ V f+2*multiplierGradientSquare μ hQ V g := by
  let ε (i : ℕ) : ℝ := (1/2)^i
  have hε (i : ℕ) : 0 < ε i := pow_pos (by norm_num) _
  have ht : Tendsto ε atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let F (i : ℕ) := f.fold μ hQ (ε i) (hε i)
  let G (i : ℕ) := g.fold μ hQ (ε i) (hε i)
  let M := SobolevSpace.mulLipschitzLinear μ hQ hv c hs hb hn V hV
  let q := multiplierGradientSquare μ hQ V
  let d (u : SobolevSpace μ hQ) := energyForm μ hQ u (M u)-q u
  have hF := SobolevSpace.fold_tendsto_zero μ hQ f hε ht
  have hG := SobolevSpace.fold_tendsto_zero μ hQ g hε ht
  have hbF (i : ℕ) : ‖SobolevSpace.minimalSlope μ hQ (F i)‖ ≤
      ‖SobolevSpace.minimalSlope μ hQ f‖ := by
    simp only [F,SobolevSpace.minimalSlope_fold,le_refl]
  have hbG (i : ℕ) : ‖SobolevSpace.minimalSlope μ hQ (G i)‖ ≤
      ‖SobolevSpace.minimalSlope μ hQ g‖ := by
    simp only [G,SobolevSpace.minimalSlope_fold,le_refl]
  have hbp (i : ℕ) : ‖SobolevSpace.minimalSlope μ hQ (F i+G i)‖ ≤
      ‖SobolevSpace.minimalSlope μ hQ f‖+‖SobolevSpace.minimalSlope μ hQ g‖ :=
    (minimalSlope_norm_add_le μ hQ _ _).trans (add_le_add (hbF i) (hbG i))
  have hbm (i : ℕ) : ‖SobolevSpace.minimalSlope μ hQ (F i-G i)‖ ≤
      ‖SobolevSpace.minimalSlope μ hQ f‖+‖SobolevSpace.minimalSlope μ hQ g‖ := by
    have hh := minimalSlope_norm_add_le μ hQ (F i) (-G i)
    rw [SobolevSpace.minimalSlope_neg,←sub_eq_add_neg] at hh
    exact hh.trans (add_le_add (hbF i) (hbG i))
  have hf0 : Tendsto (fun i => d (F i)) atTop (𝓝 0) :=
    multiplierGradientSquare_error_tendsto μ hQ hv c hs hb hn V hV F hbF hF
  have hg0 : Tendsto (fun i => d (G i)) atTop (𝓝 0) :=
    multiplierGradientSquare_error_tendsto μ hQ hv c hs hb hn V hV G hbG hG
  have hp0 : Tendsto (fun i => d (F i+G i)) atTop (𝓝 0) := by
    apply multiplierGradientSquare_error_tendsto μ hQ hv c hs hb hn V hV _ hbp
    simpa only [map_add,add_zero] using hF.add hG
  have hm0 : Tendsto (fun i => d (F i-G i)) atTop (𝓝 0) := by
    apply multiplierGradientSquare_error_tendsto μ hQ hv c hs hb hn V hV _ hbm
    simpa only [map_sub,sub_self] using hF.sub hG
  have hd : Tendsto (fun i => d (F i+G i)+d (F i-G i)-2*d (F i)-2*d (G i)) atTop (𝓝 0) := by
    simpa using ((hp0.add hm0).sub (hf0.const_mul 2)).sub (hg0.const_mul 2)
  have he (i : ℕ) : d (F i+G i)+d (F i-G i)-2*d (F i)-2*d (G i) =
      -(q (f+g)+q (f-g)-2*q f-2*q g) := by
    have hp := energyForm_linear_parallelogram μ hQ M (F i) (G i)
    have hq := multiplierGradientSquare_fold_pair μ hQ V f g (hε i)
    have hqf := multiplierGradientSquare_fold μ hQ V f (hε i)
    have hqg := multiplierGradientSquare_fold μ hQ V g (hε i)
    change q (F i+G i)+q (F i-G i) = q (f+g)+q (f-g) at hq
    change q (F i) = q f at hqf
    change q (G i) = q g at hqg
    dsimp only [d]
    rw [hqf,hqg]
    linarith only [hp,hq]
  simp_rw [he] at hd
  have hz := tendsto_nhds_unique tendsto_const_nhds hd
  change -(q (f+g)+q (f-g)-2*q f-2*q g) = 0 at hz
  change q (f+g)+q (f-g) = 2*q f+2*q g
  linarith only [hz]


end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] in
 theorem lpMultiplier_add_weight (V W : Lp ℝ ∞ μ) (F : Lp ℝ 2 μ) :
    lpMultiplier μ (V+W) F = lpMultiplier μ V F+lpMultiplier μ W F := by
  apply Lp.ext
  filter_upwards [lpMultiplier_coe μ (V+W) F,lpMultiplier_coe μ V F,lpMultiplier_coe μ W F,
    Lp.coeFn_add V W,Lp.coeFn_add (lpMultiplier μ V F) (lpMultiplier μ W F)] with x ha hb hc hd he
  simp only [ha,hb,hc,hd,he,Pi.add_apply,add_mul]

omit [ProperSpace X] in
 theorem multiplierGradientSquare_add_weight (V W : Lp ℝ ∞ μ) (f : SobolevSpace μ hQ) :
    multiplierGradientSquare μ hQ (V+W) f =
      multiplierGradientSquare μ hQ V f+multiplierGradientSquare μ hQ W f := by
  simp only [multiplierGradientSquare,lpMultiplier_add_weight,inner_add_right]

 theorem multiplierGradientSquare_parallelogram_signed
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (c : ℝ) (hs : HasCompactSupport (fun x => v x-c))
    (hb : ∀ x, |v x| ≤ B)
    (V : Lp ℝ ∞ μ) (hV : ⇑V =ᵐ[μ] v) (f g : SobolevSpace μ hQ) :
    multiplierGradientSquare μ hQ V (f+g)+multiplierGradientSquare μ hQ V (f-g) =
      2*multiplierGradientSquare μ hQ V f+2*multiplierGradientSquare μ hQ V g := by
  let W := boundedMultiplier μ (fun _ : X => (B:ℝ)) measurable_const B
    (fun _ => by simp)
  have hW : ⇑W =ᵐ[μ] (fun _ : X => (B:ℝ)) := boundedMultiplier_coe μ _ _ _ _
  have hWV : ⇑(V+W) =ᵐ[μ] fun x => v x+B := by
    filter_upwards [Lp.coeFn_add V W,hV,hW] with x ha hv hw
    simp only [ha,Pi.add_apply,hv,hw]
  have hsb : HasCompactSupport (fun x => v x+B-(c+B)) := by
    simpa only [add_sub_add_right_eq_sub] using hs
  have hbound (x : X) : |v x+B| ≤ (2*B:ℝ≥0) := by
    have hh := abs_add_le (v x) (B:ℝ)
    simp only [NNReal.coe_mul,NNReal.coe_ofNat]
    rw [abs_of_nonneg B.coe_nonneg] at hh
    linarith [hb x]
  have hpos (x : X) : 0 ≤ v x+B := by linarith [(abs_le.mp (hb x)).1]
  have hadd := multiplierGradientSquare_parallelogram μ hQ (hv.add (LipschitzWith.const (B:ℝ)))
    (c+B) hsb hbound hpos (V+W) hWV f g
  have hconst := multiplierGradientSquare_parallelogram μ hQ (LipschitzWith.const (B:ℝ))
    (B:ℝ) (by simp [HasCompactSupport,tsupport]) (B := B) (fun _ => by simp) (fun _ => B.coe_nonneg) W hW f g
  simp only [multiplierGradientSquare_add_weight] at hadd
  linarith only [hadd,hconst]


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

 theorem finiteMeasure_eq_of_lipschitz_compact (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ v : X → ℝ, ∀ C : ℝ≥0, LipschitzWith C v → HasCompactSupport v →
      (∀ x, 0 ≤ v x) → (∀ x, v x ≤ 1) → (∫x, v x ∂μ) = ∫x, v x ∂ν) : μ = ν := by
  have hc (K : Set X) (hK : IsCompact K) : μ K = ν K := by
    let ε (i : ℕ) : ℝ := (1/2)^i
    have hε (i : ℕ) : 0 < ε i := pow_pos (by norm_num) _
    have ht : Tendsto ε atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have he (i : ℕ) : (∫x, (thickenedIndicator (hε i) K x : ℝ) ∂μ) =
        ∫x, (thickenedIndicator (hε i) K x : ℝ) ∂ν := by
      apply h _ ((ε i).toNNReal⁻¹)
      · simpa only [one_mul,Function.comp_def] using
          NNReal.isometry_coe.lipschitzWith.comp (lipschitzWith_thickenedIndicator (hε i) K)
      · apply HasCompactSupport.intro (hK.cthickening (r := ε i))
        intro x hx
        simp only [thickenedIndicator_zero (hε i) K
          (fun h => hx (thickening_subset_cthickening (ε i) K h)),NNReal.coe_zero]
      · intro x; exact NNReal.coe_nonneg _
      · intro x; exact_mod_cast thickenedIndicator_le_one (hε i) K x
    have hμ := tendsto_integral_thickenedIndicator_of_isClosed μ hK.isClosed hε ht
    have hν := tendsto_integral_thickenedIndicator_of_isClosed ν hK.isClosed hε ht
    simp_rw [he] at hμ
    have heq := tendsto_nhds_unique hμ hν
    exact ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ K) (measure_ne_top ν K) |>.mp heq
  apply Measure.ext
  intro A hA
  rw [hA.measure_eq_iSup_isCompact μ,hA.measure_eq_iSup_isCompact ν]
  congr! 4 with K _ hK
  exact hc K hK


end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X)

 theorem integrable_nonneg_eq_of_lipschitz_compact {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    (h : ∀ v : X → ℝ, ∀ C : ℝ≥0, LipschitzWith C v → HasCompactSupport v →
      (∀ x, 0 ≤ v x) → (∀ x, v x ≤ 1) → (∫x, v x*f x ∂μ) = ∫x, v x*g x ∂μ) :
    f =ᵐ[μ] g := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let ξ := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hf.2
  have : IsFiniteMeasure ξ := isFiniteMeasure_withDensity_ofReal hg.2
  have he : ν = ξ := by
    apply finiteMeasure_eq_of_lipschitz_compact
    intro v C hv hs hn hb
    have h1 := integral_withDensity_eq_integral_toReal_smul₀
      hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) v
    have h2 := integral_withDensity_eq_integral_toReal_smul₀
      hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) v
    simp only [ENNReal.toReal_ofReal (hfn _),ENNReal.toReal_ofReal (hgn _),smul_eq_mul] at h1 h2
    rw [h1,h2]
    simpa only [mul_comm] using h v C hv hs hn hb
  have hh := (withDensity_eq_iff hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal hf.lintegral_lt_top.ne).mp he
  filter_upwards [hh] with x hx
  have heq := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (hfn x),ENNReal.toReal_ofReal (hgn x)] using heq

variable (hQ : QuadraticCheegerEnergy μ)

 theorem minimalSlope_pointwise_parallelogram (f g : SobolevSpace μ hQ) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (f+g) x^2+
      SobolevSpace.minimalSlope μ hQ (f-g) x^2 =
      2*SobolevSpace.minimalSlope μ hQ f x^2+2*SobolevSpace.minimalSlope μ hQ g x^2 := by
  have hi (u : SobolevSpace μ hQ) : Integrable (fun x => SobolevSpace.minimalSlope μ hQ u x^2) μ :=
    (memLp_two_iff_integrable_sq (Lp.memLp _).aestronglyMeasurable).mp (Lp.memLp _)
  apply integrable_nonneg_eq_of_lipschitz_compact μ
    (f := fun x => SobolevSpace.minimalSlope μ hQ (f+g) x^2+SobolevSpace.minimalSlope μ hQ (f-g) x^2)
    (g := fun x => 2*SobolevSpace.minimalSlope μ hQ f x^2+2*SobolevSpace.minimalSlope μ hQ g x^2)
    ((hi (f+g)).add (hi (f-g)))
    (((hi f).const_mul 2).add ((hi g).const_mul 2)) (by intro x; positivity) (by intro x; positivity)
  intro v C hv hs hn hb
  have hb' (x : X) : |v x| ≤ (1:ℝ≥0) := by simpa only [abs_of_nonneg (hn x),NNReal.coe_one] using hb x
  let V := boundedMultiplier μ v hv.continuous.measurable 1 hb'
  have hV : ⇑V =ᵐ[μ] v := boundedMultiplier_coe μ _ _ _ _
  have he := multiplierGradientSquare_parallelogram μ hQ hv 0 (by simpa only [sub_zero] using hs)
    hb' hn V hV f g
  have hie (u : SobolevSpace μ hQ) : Integrable (fun x => v x*SobolevSpace.minimalSlope μ hQ u x^2) μ := by
    apply (multiplierGradientSquare_integrable μ hQ V u).congr
    filter_upwards [hV] with x hx
    rw [hx]
  have hqe (u : SobolevSpace μ hQ) : multiplierGradientSquare μ hQ V u =
      ∫x, v x*SobolevSpace.minimalSlope μ hQ u x^2 ∂μ := by
    rw [multiplierGradientSquare_integral]
    apply integral_congr_ae
    filter_upwards [hV] with x hx
    rw [hx]
  simp only [hqe] at he
  simp only [mul_add]
  rw [integral_add (hie _) (hie _)]
  have he2 (x : X) : v x*(2*SobolevSpace.minimalSlope μ hQ f x^2)+
      v x*(2*SobolevSpace.minimalSlope μ hQ g x^2) =
      2*(v x*SobolevSpace.minimalSlope μ hQ f x^2)+2*(v x*SobolevSpace.minimalSlope μ hQ g x^2) := by ring
  simp_rw [he2]
  rw [integral_add ((hie _).const_mul 2) ((hie _).const_mul 2),integral_const_mul,integral_const_mul]
  exact he


end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
 theorem weightedGradientSquare_nonneg (ν : Measure X) (f : SobolevSpace μ hQ) :
    0 ≤ weightedGradientSquare μ hQ ν f := integral_nonneg (fun _ => sq_nonneg _)

omit [ProperSpace X] in
 theorem weightedGradientSquare_smul {ν : Measure X} {C : ℝ≥0∞}
    (hν : ν ≤ C • μ) (c : ℝ) (f : SobolevSpace μ hQ) :
    weightedGradientSquare μ hQ ν (c • f) = c^2*weightedGradientSquare μ hQ ν f := by
  rw [weightedGradientSquare,weightedGradientSquare,SobolevSpace.minimalSlope_smul,
    ←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(Lp.coeFn_smul |c| (SobolevSpace.minimalSlope μ hQ f)).filter_mono
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le] with x hx
  simp only [hx,Pi.smul_apply,smul_eq_mul,mul_pow,sq_abs]

omit [ProperSpace X] in
 theorem weightedGradientSquare_zero {ν : Measure X} {C : ℝ≥0∞}
    (hν : ν ≤ C • μ) : weightedGradientSquare μ hQ ν 0 = 0 := by
  simpa using weightedGradientSquare_smul μ hQ hν 0 (0 : SobolevSpace μ hQ)

 theorem weightedGradientSquare_parallelogram {ν : Measure X} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g : SobolevSpace μ hQ) :
    weightedGradientSquare μ hQ ν (f+g)+weightedGradientSquare μ hQ ν (f-g) =
      2*(weightedGradientSquare μ hQ ν f+weightedGradientSquare μ hQ ν g) := by
  have hi := weightedGradientSquare_integrable μ hQ hC hν
  simp only [weightedGradientSquare]
  rw [←integral_add (hi (f+g)) (hi (f-g))]
  calc
    _ = ∫x, 2*SobolevSpace.minimalSlope μ hQ f x^2+
        2*SobolevSpace.minimalSlope μ hQ g x^2 ∂ν := integral_congr_ae
      ((minimalSlope_pointwise_parallelogram μ hQ f g).filter_mono
        (Measure.absolutelyContinuous_of_le_smul hν).ae_le)
    _ = _ := by rw [integral_add ((hi f).const_mul 2) ((hi g).const_mul 2),
      integral_const_mul,integral_const_mul]; ring

 theorem weightedGradientSquare_line {ν : Measure X} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g : SobolevSpace μ hQ) (t : ℝ) :
    weightedGradientSquare μ hQ ν (f+t • g) = weightedGradientSquare μ hQ ν f+
      2*t*EnergyPolarization.bracket (weightedGradientSquare μ hQ ν) f g+
      t^2*weightedGradientSquare μ hQ ν g := by
  let q := weightedGradientSquare μ hQ ν
  have h0 := weightedGradientSquare_zero μ hQ hν
  have hn := weightedGradientSquare_nonneg μ hQ ν
  have hs := weightedGradientSquare_smul μ hQ hν
  have hp := weightedGradientSquare_parallelogram μ hQ hC hν
  have ha : q (f+t • g) = q f+q (t • g)+2*EnergyPolarization.bracket q f (t • g) := by
    unfold EnergyPolarization.bracket
    linarith only [hp f (t • g)]
  rw [EnergyPolarization.bracket_symm q hs (t • g) f,
    EnergyPolarization.bracket_smul_left q hn hs hp,
    EnergyPolarization.bracket_symm q hs f g] at ha
  dsimp only [q] at ha
  rw [hs] at ha
  linear_combination ha

 theorem weightedGradientPair_eq_bracket {ν : Measure X} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g : SobolevSpace μ hQ) :
    weightedGradientPair μ hQ ν f g =
      EnergyPolarization.bracket (weightedGradientSquare μ hQ ν) f g := by
  have he := funext (weightedGradientSquare_line μ hQ hC hν f g)
  let b := EnergyPolarization.bracket (weightedGradientSquare μ hQ ν) f g
  have hd : HasDerivAt (fun t : ℝ => weightedGradientSquare μ hQ ν f+
      2*t*b+t^2*weightedGradientSquare μ hQ ν g) (2*b) 0 := by
    convert! ((hasDerivAt_const (0:ℝ) (weightedGradientSquare μ hQ ν f)).add
      (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const b)).add
      (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (weightedGradientSquare μ hQ ν g)) using 1 ; norm_num
  rw [weightedGradientPair,he,hd.deriv]
  dsimp only [b]
  ring


end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 

noncomputable def localGamma (f g : SobolevSpace μ hQ) (x : X) : ℝ :=
  (SobolevSpace.minimalSlope μ hQ (f+g) x^2-
    SobolevSpace.minimalSlope μ hQ (f-g) x^2)/4

omit [ProperSpace X] in
 theorem localGamma_integrable {ν : Measure X} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g : SobolevSpace μ hQ) :
    Integrable (localGamma μ hQ f g) ν :=
  ((weightedGradientSquare_integrable μ hQ hC hν (f+g)).sub
    (weightedGradientSquare_integrable μ hQ hC hν (f-g))).div_const 4

omit [ProperSpace X] in
 theorem integral_localGamma {ν : Measure X} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g : SobolevSpace μ hQ) :
    (∫x, localGamma μ hQ f g x ∂ν) =
      EnergyPolarization.bracket (weightedGradientSquare μ hQ ν) f g := by
  simp only [localGamma,integral_div,EnergyPolarization.bracket,weightedGradientSquare]
  rw [integral_sub (weightedGradientSquare_integrable μ hQ hC hν (f+g))
    (weightedGradientSquare_integrable μ hQ hC hν (f-g))]

omit [ProperSpace X] in
 theorem localGamma_memL1 (f g : SobolevSpace μ hQ) :
    Integrable (localGamma μ hQ f g) μ :=
  localGamma_integrable μ hQ (C := 1) (by norm_num) (by simp) f g

 theorem localGamma_add_left (f g h : SobolevSpace μ hQ) :
    localGamma μ hQ (f+g) h =ᵐ[μ] fun x => localGamma μ hQ f h x+localGamma μ hQ g h x := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (localGamma_memL1 μ hQ _ _)
    ((localGamma_memL1 μ hQ _ _).add (localGamma_memL1 μ hQ _ _))
  intro s hs hfin
  have hν : μ.restrict s ≤ (1:ℝ≥0∞) • μ := by simpa using Measure.restrict_le_self (μ := μ) (s := s)
  have h1 : (1:ℝ≥0∞) ≠ ∞ := by norm_num
  simp only [Pi.add_apply]
  rw [integral_add (localGamma_integrable μ hQ h1 hν _ _) (localGamma_integrable μ hQ h1 hν _ _)]
  simp only [integral_localGamma μ hQ h1 hν]
  exact EnergyPolarization.bracket_add_left _ (weightedGradientSquare_parallelogram μ hQ h1 hν) f g h

 theorem localGamma_smul_left (c : ℝ) (f g : SobolevSpace μ hQ) :
    localGamma μ hQ (c • f) g =ᵐ[μ] fun x => c*localGamma μ hQ f g x := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (localGamma_memL1 μ hQ _ _)
    ((localGamma_memL1 μ hQ _ _).const_mul c)
  intro s hs hfin
  have hν : μ.restrict s ≤ (1:ℝ≥0∞) • μ := by simpa using Measure.restrict_le_self (μ := μ) (s := s)
  have h1 : (1:ℝ≥0∞) ≠ ∞ := by norm_num
  rw [integral_const_mul]
  simp only [integral_localGamma μ hQ h1 hν]
  exact EnergyPolarization.bracket_smul_left _ (weightedGradientSquare_nonneg μ hQ _)
    (weightedGradientSquare_smul μ hQ hν) (weightedGradientSquare_parallelogram μ hQ h1 hν) c f g

omit [ProperSpace X] in
 theorem localGamma_comm (f g : SobolevSpace μ hQ) :
    localGamma μ hQ f g =ᵐ[μ] localGamma μ hQ g f := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (localGamma_memL1 μ hQ _ _) (localGamma_memL1 μ hQ _ _)
  intro s hs hfin
  have hν : μ.restrict s ≤ (1:ℝ≥0∞) • μ := by simpa using Measure.restrict_le_self (μ := μ) (s := s)
  have h1 : (1:ℝ≥0∞) ≠ ∞ := by norm_num
  simp only [integral_localGamma μ hQ h1 hν]
  exact EnergyPolarization.bracket_symm _ (weightedGradientSquare_smul μ hQ hν) g f

omit [ProperSpace X] in
 theorem localGamma_self (f : SobolevSpace μ hQ) :
    localGamma μ hQ f f =ᵐ[μ] fun x => SobolevSpace.minimalSlope μ hQ f x^2 := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (localGamma_memL1 μ hQ _ _)
    (weightedGradientSquare_integrable μ hQ (C := 1) (by norm_num) (by simp) f)
  intro s hs hfin
  have hν : μ.restrict s ≤ (1:ℝ≥0∞) • μ := by simpa using Measure.restrict_le_self (μ := μ) (s := s)
  have h1 : (1:ℝ≥0∞) ≠ ∞ := by norm_num
  rw [integral_localGamma μ hQ h1 hν]
  exact EnergyPolarization.bracket_self _ (weightedGradientSquare_zero μ hQ hν)
    (weightedGradientSquare_smul μ hQ hν) f

 theorem localGamma_add_right (f g h : SobolevSpace μ hQ) :
    localGamma μ hQ f (g+h) =ᵐ[μ] fun x => localGamma μ hQ f g x+localGamma μ hQ f h x := by
  filter_upwards [localGamma_comm μ hQ f (g+h),localGamma_add_left μ hQ g h f,
    localGamma_comm μ hQ g f,localGamma_comm μ hQ h f] with x h1 h2 h3 h4
  simp only [h1,h2,h3,h4]

 theorem localGamma_smul_right (c : ℝ) (f g : SobolevSpace μ hQ) :
    localGamma μ hQ f (c • g) =ᵐ[μ] fun x => c*localGamma μ hQ f g x := by
  filter_upwards [localGamma_comm μ hQ f (c • g),localGamma_smul_left μ hQ c g f,
    localGamma_comm μ hQ g f] with x h1 h2 h3
  simp only [h1,h2,h3]

omit [ProperSpace X] in
 theorem integral_localGamma_eq_energyForm (f g : SobolevSpace μ hQ) :
    (∫x, localGamma μ hQ f g x ∂μ) = energyForm μ hQ f g := by
  rw [integral_localGamma μ hQ (C := 1) (by norm_num) (by simp),EnergyPolarization.bracket,
    weightedGradientSquare_self,weightedGradientSquare_self]
  have h := form_sub_smul μ hQ f g 1
  have h' := form_sub_smul μ hQ f g (-1)
  simp only [one_smul,one_pow,neg_smul,one_smul,sub_neg_eq_add,neg_sq] at h h'
  linarith


end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem localGamma_abs_le (f g : SobolevSpace μ hQ) :
    ∀ᵐ x ∂μ, |localGamma μ hQ f g x| ≤
      SobolevSpace.minimalSlope μ hQ f x*SobolevSpace.minimalSlope μ hQ g x := by
  have hn (z : SobolevSpace μ hQ) : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.minimalSlope μ hQ z x :=
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ z)
  filter_upwards [minimalSlope_pointwise_parallelogram μ hQ f g,
    (Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_add_le μ hQ f g),
    (Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_sub_le μ hQ f g),
    Lp.coeFn_add (SobolevSpace.minimalSlope μ hQ f) (SobolevSpace.minimalSlope μ hQ g),
    hn f,hn g,hn (f+g),hn (f-g)] with x hp ha hs he hf hg hfg hfg'
  simp only [he,Pi.add_apply] at ha hs
  have ha2 := (sq_le_sq₀ hfg (add_nonneg hf hg)).mpr ha
  have hs2 := (sq_le_sq₀ hfg' (add_nonneg hf hg)).mpr hs
  change |(_-_)/4| ≤ _
  rw [abs_le]
  constructor <;> nlinarith

 theorem localGamma_sub_left (f g h : SobolevSpace μ hQ) :
    localGamma μ hQ (f-g) h =ᵐ[μ] fun x => localGamma μ hQ f h x-localGamma μ hQ g h x := by
  have he : f-g=f+(-1:ℝ) • g := by module
  rw [he]
  filter_upwards [localGamma_add_left μ hQ f ((-1:ℝ) • g) h,
    localGamma_smul_left μ hQ (-1) g h] with x h1 h2
  simp only [h1,h2,neg_one_mul,sub_eq_add_neg]

 theorem localGamma_eq_on_eq (f g h : SobolevSpace μ hQ) :
    ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x = SobolevSpace.toLp μ hQ g x →
      localGamma μ hQ f h x = localGamma μ hQ g h x := by
  have hz := SobolevSpace.minimalSlope_zero_on_zero μ hQ (f-g)
  simp only [map_sub] at hz
  filter_upwards [hz, Lp.coeFn_sub (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g),
    localGamma_abs_le μ hQ (f-g) h,localGamma_sub_left μ hQ f g h] with x hz he hb hd
  intro hx
  have hzero := hz (by simp only [he,Pi.sub_apply,hx,sub_self])
  rw [hzero,zero_mul,hd] at hb
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)

 theorem localGamma_zero_on_level (f g : SobolevSpace μ hQ) (c : ℝ) :
    ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x=c → localGamma μ hQ f g x=0 := by
  filter_upwards [SobolevSpace.minimalSlope_zero_on_level μ hQ f c,
    localGamma_abs_le μ hQ f g] with x hz hb
  intro hx
  rw [hz hx,zero_mul] at hb
  exact abs_nonpos_iff.mp hb


end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
 theorem SobolevSpace.comp_sub_linear (f : SobolevSpace μ hQ)
    {φ : ℝ → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (c : ℝ) :
    SobolevSpace.comp μ hQ (hφ.sub (lipschitzWith_const_mul_real LipschitzWith.id c))
      (by simp only [hφ0,id_eq,mul_zero,sub_zero]) f = SobolevSpace.comp μ hQ hφ hφ0 f-c • f := by
  apply Subtype.ext
  apply Lp.ext
  have hcoe := SobolevSpace.comp_coe μ hQ
    (hφ.sub (lipschitzWith_const_mul_real LipschitzWith.id c)) (by simp only [hφ0,id_eq,mul_zero,sub_zero]) f
  have hsub := Lp.coeFn_sub (SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f))
    (c • SobolevSpace.toLp μ hQ f)
  filter_upwards [hcoe,SobolevSpace.comp_coe μ hQ hφ hφ0 f,hsub,
    Lp.coeFn_smul c (SobolevSpace.toLp μ hQ f)] with x hh hp hs hc
  change SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ (hφ.sub (lipschitzWith_const_mul_real LipschitzWith.id c)) (by simp [hφ0]) f) x =
    (SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f)-c • SobolevSpace.toLp μ hQ f) x
  simp only [hh,Function.comp_apply,hs,Pi.sub_apply,hp,hc,Pi.smul_apply,smul_eq_mul,id_eq]

 theorem localGamma_comp_C1 (f g : SobolevSpace μ hQ)
    {φ ψ : ℝ → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) :
    localGamma μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) g =ᵐ[μ]
      fun x => ψ (SobolevSpace.toLp μ hQ f x)*localGamma μ hQ f g x := by
  let u := SobolevSpace.comp μ hQ hφ hφ0 f
  have hinc (c : ℝ) : ∀ᵐ x ∂μ,
      |localGamma μ hQ u g x-c*localGamma μ hQ f g x| ≤
      |ψ (SobolevSpace.toLp μ hQ f x)-c| *
        (SobolevSpace.minimalSlope μ hQ f x*SobolevSpace.minimalSlope μ hQ g x) := by
    have hlip := hφ.sub (lipschitzWith_const_mul_real LipschitzWith.id c)
    have hzero : (fun a => φ a-c*a) 0=0 := by simp [hφ0]
    have hder (a : ℝ) : HasDerivAt (fun a => φ a-c*a) (ψ a-c) a := by
      convert! (hd a).sub ((hasDerivAt_id a).const_mul c) using 1 ; simp
    have hbound (a : ℝ) : |ψ a-c| ≤ (B+‖c‖₊:ℝ≥0) := by
      simp only [NNReal.coe_add,coe_nnnorm,Real.norm_eq_abs]
      calc
        _ ≤ |ψ a|+|c| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (ψ a) (-c)
        _ ≤ _ := by linarith [hB a]
    have hs := SobolevSpace.minimalSlope_comp_C1 μ hQ f hlip hzero (hψ.sub continuous_const)
      hder (B+‖c‖₊) hbound
    rw [SobolevSpace.comp_sub_linear μ hQ f hφ hφ0 c] at hs
    filter_upwards [hs,localGamma_abs_le μ hQ (u-c • f) g,
      localGamma_sub_left μ hQ u (c • f) g,localGamma_smul_left μ hQ c f g] with x hs hb hg hc
    dsimp only [u] at hb hg ⊢
    rw [hg,hc,hs] at hb
    simpa only [mul_assoc,Pi.sub_apply] using hb
  have hrat : ∀ᵐ x ∂μ, ∀ c : ℚ,
      |localGamma μ hQ u g x-(c:ℝ)*localGamma μ hQ f g x| ≤
      |ψ (SobolevSpace.toLp μ hQ f x)-(c:ℝ)| *
        (SobolevSpace.minimalSlope μ hQ f x*SobolevSpace.minimalSlope μ hQ g x) :=
    ae_all_iff.mpr (fun c => hinc c)
  filter_upwards [hrat] with x hx
  have hh : |localGamma μ hQ u g x-ψ (SobolevSpace.toLp μ hQ f x)*localGamma μ hQ f g x| ≤
      |ψ (SobolevSpace.toLp μ hQ f x)-ψ (SobolevSpace.toLp μ hQ f x)| *
        (SobolevSpace.minimalSlope μ hQ f x*SobolevSpace.minimalSlope μ hQ g x) := by
    refine Rat.isDenseEmbedding_coe_real.dense.induction_on
      (p := fun c : ℝ => |localGamma μ hQ u g x-c*localGamma μ hQ f g x| ≤
        |ψ (SobolevSpace.toLp μ hQ f x)-c| *
          (SobolevSpace.minimalSlope μ hQ f x*SobolevSpace.minimalSlope μ hQ g x)) _ ?_ hx
    exact isClosed_le (by fun_prop) (by fun_prop)
  simp only [sub_self,abs_zero,zero_mul] at hh
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)


end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

 theorem nonneg_mul_regularizedReciprocal_le_one {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    0 ≤ r*regularizedReciprocal ε r ∧ r*regularizedReciprocal ε r ≤ 1 := by
  constructor
  · exact mul_nonneg hr (regularizedReciprocal_nonneg hε r)
  rw [regularizedReciprocal_eq hε,←div_eq_mul_inv]
  apply (div_le_one (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg r]))).mpr
  exact (Real.le_sqrt hr (by positivity)).mpr (by nlinarith)

 theorem regularizedReciprocal_tendsto_pos {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε => regularizedReciprocal ε r) (𝓝[>] (0:ℝ)) (𝓝 r⁻¹) := by
  have hs : Tendsto (fun ε : ℝ => Real.sqrt (ε^2+r^2)) (𝓝[>] 0) (𝓝 r) := by
    have h : ContinuousAt (fun ε : ℝ => Real.sqrt (ε^2+r^2)) 0 := by fun_prop
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,Real.sqrt_sq hr.le] using
      h.tendsto.mono_left nhdsWithin_le_nhds
  apply (hs.inv₀ hr.ne').congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (regularizedReciprocal_eq hε r).symm

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem localGamma_comp_C1_right (f g : SobolevSpace μ hQ)
    {φ ψ : ℝ → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) :
    localGamma μ hQ f (SobolevSpace.comp μ hQ hφ hφ0 g) =ᵐ[μ]
      fun x => ψ (SobolevSpace.toLp μ hQ g x)*localGamma μ hQ f g x := by
  filter_upwards [localGamma_comp_C1 μ hQ g f hφ hφ0 hψ hd B hB,
    localGamma_comm μ hQ f (SobolevSpace.comp μ hQ hφ hφ0 g),localGamma_comm μ hQ g f]
    with x h1 h2 h3
  simp only [h1,h2,h3]

 theorem weighted_log_pair_integral (f ρ : SobolevSpace μ hQ)
    (hρ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ ρ x) {ε : ℝ} (hε : 0 < ε)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hν : μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)) ≤ C • μ) :
    weightedGradientPair μ hQ
      (μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x))) f
      (SobolevSpace.comp μ hQ (regularizedLog_lipschitz hε) (regularizedLog_zero ε) ρ) =
    ∫x, SobolevSpace.toLp μ hQ ρ x*regularizedReciprocal ε (SobolevSpace.toLp μ hQ ρ x)*
      localGamma μ hQ f ρ x ∂μ := by
  rw [weightedGradientPair_eq_bracket μ hQ hC hν,←integral_localGamma μ hQ hC hν]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (Lp.stronglyMeasurable (SobolevSpace.toLp μ hQ ρ)).measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ,localGamma_comp_C1_right μ hQ f ρ
    (regularizedLog_lipschitz hε) (regularizedLog_zero ε)
    (regularizedReciprocal_continuous ε) (regularizedLog_hasDerivAt ε)
    ⟨ε⁻¹,inv_nonneg.mpr hε.le⟩ (regularizedReciprocal_bound hε)] with x hr hx
  simp only [ENNReal.toReal_ofReal hr,smul_eq_mul,hx]
  ring

 

 theorem weighted_log_pair_tendsto (f ρ : SobolevSpace μ hQ)
    (hρ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ ρ x)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hν : μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)) ≤ C • μ) :
    Tendsto (fun ε : ℝ => if hε : 0 < ε then weightedGradientPair μ hQ
      (μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x))) f
      (SobolevSpace.comp μ hQ (regularizedLog_lipschitz hε) (regularizedLog_zero ε) ρ) else 0)
      (𝓝[>] 0) (𝓝 (energyForm μ hQ f ρ)) := by
  have he : Tendsto (fun ε : ℝ => ∫x, SobolevSpace.toLp μ hQ ρ x*
      regularizedReciprocal ε (SobolevSpace.toLp μ hQ ρ x)*localGamma μ hQ f ρ x ∂μ)
      (𝓝[>] 0) (𝓝 (∫x, localGamma μ hQ f ρ x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun x => |localGamma μ hQ f ρ x|)
    · apply Eventually.of_forall
      intro ε
      exact (((Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ ρ)).mul
        ((regularizedReciprocal_continuous ε).comp_aestronglyMeasurable
          (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ ρ)))).mul
        (localGamma_memL1 μ hQ f ρ).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [hρ] with x hr
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (nonneg_mul_regularizedReciprocal_le_one hε hr).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (nonneg_mul_regularizedReciprocal_le_one hε hr).2
    · exact (localGamma_memL1 μ hQ f ρ).abs
    · filter_upwards [hρ,localGamma_zero_on_level μ hQ ρ f 0,localGamma_comm μ hQ f ρ] with x hr hz hc
      rcases eq_or_lt_of_le hr with hr0 | hrpos
      · have hg : localGamma μ hQ f ρ x=0 := hc.trans (hz hr0.symm)
        simp only [hg,mul_zero]
        exact tendsto_const_nhds
      · have hh := (regularizedReciprocal_tendsto_pos hrpos).const_mul (SobolevSpace.toLp μ hQ ρ x)
        simpa only [mul_inv_cancel₀ hrpos.ne',one_mul] using hh.mul_const (localGamma μ hQ f ρ x)
  rw [integral_localGamma_eq_energyForm] at he
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  simp only [dite_eq_left hε]
  exact (weighted_log_pair_integral μ hQ f ρ hρ hε hC hν).symm


end

 
section

 
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem localGamma_square (f g : SobolevSpace μ hQ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C) :
    localGamma μ hQ (SobolevSpace.square μ hQ f C) g =ᵐ[μ]
      fun x => 2*SobolevSpace.toLp μ hQ f x*localGamma μ hQ f g x := by
  have he : SobolevSpace.comp μ hQ (squareClip_lipschitz C.coe_nonneg)
      (squareClip_zero C) f = SobolevSpace.square μ hQ f C := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [SobolevSpace.comp_coe μ hQ (squareClip_lipschitz C.coe_nonneg)
      (squareClip_zero C) f,SobolevSpace.square_coe μ hQ f C hf,hf] with x hc hs hx
    change SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ (squareClip_lipschitz C.coe_nonneg)
      (squareClip_zero C) f) x = SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ f C) x
    rw [hc,hs]
    exact squareClip_eq hx
  have hh := localGamma_comp_C1 μ hQ f g (squareClip_lipschitz C.coe_nonneg)
    (squareClip_zero C) (squareClipDeriv_continuous C) (squareClip_hasDerivAt C)
    (2*C) (squareClipDeriv_bound C.coe_nonneg)
  rw [he] at hh
  filter_upwards [hh,hf] with x hh hf
  simpa only [squareClipDeriv_eq hf] using hh

 theorem localGamma_product_left (f g h : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ D) :
    localGamma μ hQ (SobolevSpace.product μ hQ f g C D) h =ᵐ[μ]
      fun x => SobolevSpace.toLp μ hQ f x*localGamma μ hQ g h x+
        SobolevSpace.toLp μ hQ g x*localGamma μ hQ f h x := by
  have hp : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (f+g) x| ≤ (C+D:ℝ≥0) := by
    simp only [map_add]
    filter_upwards [hf,hg,Lp.coeFn_add (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)]
      with x hf hg he
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add hf hg)
  have hm : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (f-g) x| ≤ (C+D:ℝ≥0) := by
    simp only [map_sub]
    filter_upwards [hf,hg,Lp.coeFn_sub (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)]
      with x hf hg he
    rw [he]
    exact (abs_sub _ _).trans (add_le_add hf hg)
  have hc := localGamma_smul_left μ hQ (1/4) (SobolevSpace.square μ hQ (f+g) (C+D)-
    SobolevSpace.square μ hQ (f-g) (C+D)) h
  have hp' := Lp.coeFn_add (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)
  have hm' := Lp.coeFn_sub (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)
  change localGamma μ hQ ((1/4:ℝ) • _) h =ᵐ[μ] _
  filter_upwards [hc,localGamma_sub_left μ hQ (SobolevSpace.square μ hQ (f+g) (C+D))
    (SobolevSpace.square μ hQ (f-g) (C+D)) h,localGamma_square μ hQ (f+g) h (C+D) hp,
    localGamma_square μ hQ (f-g) h (C+D) hm,localGamma_add_left μ hQ f g h,
    localGamma_sub_left μ hQ f g h,hp',hm'] with x hc hs hps hms hpa hma hp hm
  simp only [map_add,map_sub] at hps hms
  rw [hc,hs,hps,hms,hpa,hma,hp,hm]
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

 theorem localGamma_product_right (f g h : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ C)
    (hh : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ h x| ≤ D) :
    localGamma μ hQ f (SobolevSpace.product μ hQ g h C D) =ᵐ[μ]
      fun x => SobolevSpace.toLp μ hQ g x*localGamma μ hQ f h x+
        SobolevSpace.toLp μ hQ h x*localGamma μ hQ f g x := by
  filter_upwards [localGamma_comm μ hQ f (SobolevSpace.product μ hQ g h C D),
    localGamma_product_left μ hQ g h f C D hg hh,localGamma_comm μ hQ h f,
    localGamma_comm μ hQ g f] with x hc hp hh hg
  simp only [hc,hp,hh,hg]



 
noncomputable def SobolevSpace.cutoffLinear
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x) :
    SobolevSpace μ hQ →ₗ[ℝ] SobolevSpace μ hQ where
  toFun f := SobolevSpace.mulLipschitz μ hQ f hv 0 (by simpa using hs) hb hn
    (boundedMultiplier μ v hv.continuous.measurable B hb)
    (boundedMultiplier_coe μ v hv.continuous.measurable B hb)
  map_add' f g := by apply Subtype.ext; exact (lpMultiplier μ _).map_add _ _
  map_smul' c f := by apply Subtype.ext; exact (lpMultiplier μ _).map_smul c _

omit [ProperSpace X] in
 theorem SobolevSpace.cutoffLinear_toLp
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (f : SobolevSpace μ hQ) :
    SobolevSpace.toLp μ hQ (SobolevSpace.cutoffLinear μ hQ hv hs hb hn f) =
      lpMultiplier μ (boundedMultiplier μ v hv.continuous.measurable B hb)
        (SobolevSpace.toLp μ hQ f) := rfl

noncomputable def SobolevSpace.cutoffCLM
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x) :
    SobolevSpace μ hQ →L[ℝ] SobolevSpace μ hQ where
  toLinearMap := SobolevSpace.cutoffLinear μ hQ hv hs hb hn
  cont := by
    apply LinearMap.continuous_of_seq_closed_graph
    intro fs f g hf hg
    apply Subtype.ext
    have h1 := (SobolevSpace.toLpCLM μ hQ).continuous.tendsto g |>.comp hg
    have h2 := ((lpMultiplier μ (boundedMultiplier μ v hv.continuous.measurable B hb)).comp
      (SobolevSpace.toLpCLM μ hQ)).continuous.tendsto f |>.comp hf
    exact tendsto_nhds_unique h1 h2

omit [ProperSpace X] in
 theorem SobolevSpace.cutoffCLM_coe
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (f : SobolevSpace μ hQ) :
    SobolevSpace.toLp μ hQ (SobolevSpace.cutoffCLM μ hQ hv hs hb hn f) =ᵐ[μ]
      fun x => v x*SobolevSpace.toLp μ hQ f x := by
  filter_upwards [lpMultiplier_coe μ (boundedMultiplier μ v hv.continuous.measurable B hb)
    (SobolevSpace.toLp μ hQ f),boundedMultiplier_coe μ v hv.continuous.measurable B hb]
    with x hx hvx
  exact hx.trans (by rw [hvx])

omit [ProperSpace X] in
 theorem SobolevSpace.cutoffCLM_mem_dirichlet
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    {Ω : Set X} (hΩ : tsupport v ⊆ Ω) (f : SobolevSpace μ hQ) :
    SobolevSpace.cutoffCLM μ hQ hv hs hb hn f ∈ SobolevSpace.dirichlet μ hQ Ω := by
  obtain ⟨fs,gs,hfs,hgs⟩ := SobolevSpace.exists_strong_lipschitz_recovery μ hQ f
  apply (SobolevSpace.dirichletCore μ hQ Ω).isClosed_topologicalClosure.mem_of_tendsto
    ((SobolevSpace.cutoffCLM μ hQ hv hs hb hn).continuous.tendsto f |>.comp hfs)
  apply Eventually.of_forall
  intro i
  apply subset_closure
  obtain ⟨D,hD⟩ := (hgs i).1
  obtain ⟨L,hL⟩ := lipschitz_mul_constant_outside_compact hv hD 0 (by simpa using hs) hb
  refine ⟨fun x => v x*gs i x,L,hL,hs.mul_right,?_,?_⟩
  · exact (tsupport_mul_subset_left : tsupport (fun x => v x*gs i x) ⊆ tsupport v).trans hΩ
  · filter_upwards [SobolevSpace.cutoffCLM_coe μ hQ hv hs hb hn (fs i),(hgs i).2.1]
      with x hx hfx
    simpa only [Function.comp_apply,hfx] using hx


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

 theorem caccioppoli_scalar {a b f g c : ℝ} (_ : 0 ≤ a) (_ : 0 ≤ b)
    (hc : |c| ≤ a*b) :
    f^2*a^2 ≤ 2*(f^2*a^2+2*f*g*c)+4*g^2*b^2 := by
  have hh : |f*g*c| ≤ |f| *a*(|g| *b) := by
    calc
      _ = (|f| *|g|) * |c| := by rw [abs_mul,abs_mul]
      _ ≤ (|f| *|g|)*(a*b) := mul_le_mul_of_nonneg_left hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by ring
  have hx := (abs_le.mp hh).1
  have hs := sq_nonneg (|f| *a-2*(|g| *b))
  simp only [sub_sq,mul_pow,sq_abs] at hs
  nlinarith only [hx,hs]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] in
 theorem bounded_square_weight_integrable (f g : Lp ℝ 2 μ) {C : ℝ≥0}
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) : Integrable (fun x => (f x)^2*(g x)^2) μ := by
  apply (Lp.memLp g).integrable_sq.bdd_mul (c := (C:ℝ)^2) (Lp.aestronglyMeasurable f |>.pow 2)
  filter_upwards [hf] with x hx
  simpa only [Real.norm_eq_abs, Pi.pow_apply,abs_pow,sq_abs] using
    (sq_le_sq₀ (abs_nonneg (f x)) C.coe_nonneg).mpr hx

 theorem caccioppoli_weighted (u η : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C)
    (hη : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ D)
    (hzero : energyForm μ hQ u (SobolevSpace.product μ hQ
      (SobolevSpace.square μ hQ η D) u (D*D) C) = 0) :
    (∫x, (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ u x)^2 ∂μ) ≤
      4*∫x, (SobolevSpace.toLp μ hQ u x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ := by
  let test := SobolevSpace.product μ hQ (SobolevSpace.square μ hQ η D) u (D*D) C
  have hs : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ η D) x| ≤ (D*D:ℝ≥0) := by
    filter_upwards [SobolevSpace.square_coe μ hQ η D hη,hη] with x hx hh
    rw [hx,abs_pow,sq_abs]
    simpa only [NNReal.coe_mul, ←pow_two, sq_abs, NNReal.coe_pow] using (sq_le_sq₀ (abs_nonneg _) D.coe_nonneg).mpr hh
  have hform : localGamma μ hQ u test =ᵐ[μ] fun x =>
      (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ u x)^2+
      2*SobolevSpace.toLp μ hQ η x*SobolevSpace.toLp μ hQ u x*localGamma μ hQ u η x := by
    filter_upwards [localGamma_product_right μ hQ u (SobolevSpace.square μ hQ η D) u (D*D) C hs hu,
      SobolevSpace.square_coe μ hQ η D hη,localGamma_self μ hQ u,
      localGamma_comm μ hQ u (SobolevSpace.square μ hQ η D),localGamma_square μ hQ η u D hη,
      localGamma_comm μ hQ η u] with x hp hs hself hc hsq hc'
    change localGamma μ hQ u (SobolevSpace.product μ hQ _ _ _ _) x = _
    rw [hp,hs,hself,hc,hsq,hc']
    ring
  have hi1 := bounded_square_weight_integrable μ (SobolevSpace.toLp μ hQ η)
    (SobolevSpace.minimalSlope μ hQ u) hη
  have hi2 := bounded_square_weight_integrable μ (SobolevSpace.toLp μ hQ u)
    (SobolevSpace.minimalSlope μ hQ η) hu
  have hx : (∫x, (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ u x)^2 ∂μ) ≤
      ∫x, 2*localGamma μ hQ u test x+
        4*((SobolevSpace.toLp μ hQ u x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2) ∂μ := by
    apply integral_mono_ae hi1 ((localGamma_memL1 μ hQ u test).const_mul 2 |>.add (hi2.const_mul 4))
    filter_upwards [hform,localGamma_abs_le μ hQ u η,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ u),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ η)] with x hf hb hu hη
    change _ ≤ 2 * localGamma μ hQ u test x + _
    rw [hf]
    simpa only [mul_assoc] using caccioppoli_scalar hu hη hb
  rw [integral_add ((localGamma_memL1 μ hQ u test).const_mul 2) (hi2.const_mul 4),
    integral_const_mul,integral_const_mul,integral_localGamma_eq_energyForm] at hx
  simpa only [test,hzero,mul_zero,zero_add] using hx


end

 
section
 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
 theorem caccioppoli_forced (u η : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C)
    (hη : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ D)
    :
    (∫x, (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ u x)^2 ∂μ) ≤
      2*energyForm μ hQ u (SobolevSpace.product μ hQ
        (SobolevSpace.square μ hQ η D) u (D*D) C) + 4*∫x, (SobolevSpace.toLp μ hQ u x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ := by
  let test := SobolevSpace.product μ hQ (SobolevSpace.square μ hQ η D) u (D*D) C
  have hs : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ η D) x| ≤ (D*D:ℝ≥0) := by
    filter_upwards [SobolevSpace.square_coe μ hQ η D hη,hη] with x hx hh
    rw [hx,abs_pow,sq_abs]
    simpa only [NNReal.coe_mul, ←pow_two, sq_abs, NNReal.coe_pow] using (sq_le_sq₀ (abs_nonneg _) D.coe_nonneg).mpr hh
  have hform : localGamma μ hQ u test =ᵐ[μ] fun x =>
      (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ u x)^2+
      2*SobolevSpace.toLp μ hQ η x*SobolevSpace.toLp μ hQ u x*localGamma μ hQ u η x := by
    filter_upwards [localGamma_product_right μ hQ u (SobolevSpace.square μ hQ η D) u (D*D) C hs hu,
      SobolevSpace.square_coe μ hQ η D hη,localGamma_self μ hQ u,
      localGamma_comm μ hQ u (SobolevSpace.square μ hQ η D),localGamma_square μ hQ η u D hη,
      localGamma_comm μ hQ η u] with x hp hs hself hc hsq hc'
    change localGamma μ hQ u (SobolevSpace.product μ hQ _ _ _ _) x = _
    rw [hp,hs,hself,hc,hsq,hc']
    ring
  have hi1 := bounded_square_weight_integrable μ (SobolevSpace.toLp μ hQ η)
    (SobolevSpace.minimalSlope μ hQ u) hη
  have hi2 := bounded_square_weight_integrable μ (SobolevSpace.toLp μ hQ u)
    (SobolevSpace.minimalSlope μ hQ η) hu
  have hx : (∫x, (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ u x)^2 ∂μ) ≤
      ∫x, 2*localGamma μ hQ u test x+
        4*((SobolevSpace.toLp μ hQ u x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2) ∂μ := by
    apply integral_mono_ae hi1 ((localGamma_memL1 μ hQ u test).const_mul 2 |>.add (hi2.const_mul 4))
    filter_upwards [hform,localGamma_abs_le μ hQ u η,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ u),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ η)] with x hf hb hu hη
    change _ ≤ 2 * localGamma μ hQ u test x + _
    rw [hf]
    simpa only [mul_assoc] using caccioppoli_scalar hu hη hb
  rw [integral_add ((localGamma_memL1 μ hQ u test).const_mul 2) (hi2.const_mul 4),
    integral_const_mul,integral_const_mul,integral_localGamma_eq_energyForm] at hx
  exact hx


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] in
theorem bounded_square_tail_integral (g f : Lp ℝ 2 μ) {C : ℝ≥0}
    (hg : ∀ᵐ x ∂μ, |g x| ≤ C) {S : Set X} (hS : MeasurableSet S)
    (hs : ∀ᵐ x ∂μ, x ∉ S → g x = 0) :
    (∫x, g x^2*f x^2 ∂μ) ≤ (C:ℝ)^2*(∫x in S, f x^2 ∂μ) := by
  rw [←integral_const_mul,←integral_indicator hS]
  apply integral_mono_ae (bounded_square_weight_integrable μ g f hg)
    (((Lp.memLp f).integrable_sq.const_mul _).indicator hS)
  filter_upwards [hg,hs] with x hx hsx
  by_cases hxS : x ∈ S
  · rw [Set.indicator_of_mem hxS]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) C.coe_nonneg).mpr hx
  · rw [Set.indicator_of_notMem hxS,hsx hxS]
    simp

theorem caccioppoli_tail (u η : SobolevSpace μ hQ) (g : Lp ℝ 2 μ)
    (hg : IsWeakLaplacian μ hQ u g) (C D L : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C)
    (hη : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ D)
    (hL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ η x ≤ L)
    {S : Set X} (hS : MeasurableSet S)
    (hs : ∀ᵐ x ∂μ, x ∉ S → SobolevSpace.toLp μ hQ η x = 0) :
    (∫x, SobolevSpace.toLp μ hQ η x^2*SobolevSpace.minimalSlope μ hQ u x^2 ∂μ) ≤
      2*‖g‖*(D:ℝ)^2*Real.sqrt (∫x in S, SobolevSpace.toLp μ hQ u x^2 ∂μ) +
        4*(L:ℝ)^2*(∫x in S, SobolevSpace.toLp μ hQ u x^2 ∂μ) := by
  let η2 := SobolevSpace.square μ hQ η D
  let test := SobolevSpace.product μ hQ η2 u (D*D) C
  have hη2r := SobolevSpace.square_coe μ hQ η D hη
  have hη2b : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η2 x| ≤ (D*D:ℝ≥0) := by
    filter_upwards [hη2r,hη] with x hx hb
    rw [hx,abs_pow,sq_abs]
    rw [NNReal.coe_mul]
    have hsq := (sq_le_sq₀ (abs_nonneg _) D.coe_nonneg).mpr hb
    rw [sq_abs] at hsq
    nlinarith
  have hη2s : ∀ᵐ x ∂μ, x ∉ S → SobolevSpace.toLp μ hQ η2 x = 0 := by
    filter_upwards [hη2r,hs] with x hx hsx hn
    rw [hx,hsx hn]
    norm_num
  have htr := SobolevSpace.product_coe μ hQ η2 u (D*D) C hη2b hu
  let T := ∫x in S, SobolevSpace.toLp μ hQ u x^2 ∂μ
  have hT : 0 ≤ T := integral_nonneg fun _ => sq_nonneg _
  have hnb : ‖SobolevSpace.toLp μ hQ test‖ ≤ (D:ℝ)^2*Real.sqrt T := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hT,←integral_sq_Lp]
    have he : (fun x => SobolevSpace.toLp μ hQ test x^2) =ᵐ[μ]
        fun x => SobolevSpace.toLp μ hQ η2 x^2*SobolevSpace.toLp μ hQ u x^2 := by
      filter_upwards [htr] with x hx
      rw [hx,mul_pow]
    rw [integral_congr_ae he]
    simpa only [T,NNReal.coe_mul,pow_two] using
      bounded_square_tail_integral μ (SobolevSpace.toLp μ hQ η2) (SobolevSpace.toLp μ hQ u) hη2b hS hη2s
  have hGs : ∀ᵐ x ∂μ, x ∉ S → SobolevSpace.minimalSlope μ hQ η x = 0 := by
    filter_upwards [hs,SobolevSpace.minimalSlope_zero_on_zero μ hQ η] with x hsx hz hx
    exact hz (hsx hx)
  have hGb : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ L := by
    filter_upwards [hL,(Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ η)] with x hl hn
    simpa only [abs_of_nonneg hn] using hl
  have hGB := bounded_square_tail_integral μ (SobolevSpace.minimalSlope μ hQ η)
    (SobolevSpace.toLp μ hQ u) hGb hS hGs
  have he : energyForm μ hQ u test ≤ ‖g‖*((D:ℝ)^2*Real.sqrt T) := by
    rw [hg test,←inner_neg_left]
    exact (real_inner_le_norm (-g) (SobolevSpace.toLp μ hQ test)).trans
      (by rw [norm_neg]; exact mul_le_mul_of_nonneg_left hnb (norm_nonneg _))
  have hc := caccioppoli_forced μ hQ u η C D hu hη
  have hI : (∫x, SobolevSpace.toLp μ hQ u x^2*SobolevSpace.minimalSlope μ hQ η x^2 ∂μ) ≤ (L:ℝ)^2*T := by
    simpa only [mul_comm] using hGB
  change _ ≤ 2*‖g‖*(D:ℝ)^2*Real.sqrt T+4*(L:ℝ)^2*T
  change _ ≤ 2*energyForm μ hQ u test+_ at hc
  linarith


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

theorem caccioppoli_exterior (u : SobolevSpace μ hQ) (g : Lp ℝ 2 μ)
    (hg : IsWeakLaplacian μ hQ u g) (C : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C)
    (p : X) {r : ℝ} (hr : 0 < r) :
    (∫x in {x | 2*r ≤ dist p x}, SobolevSpace.minimalSlope μ hQ u x^2 ∂μ) ≤
      2*‖g‖*Real.sqrt (∫x in {x | r ≤ dist p x}, SobolevSpace.toLp μ hQ u x^2 ∂μ) +
        16/r^2*(∫x in {x | r ≤ dist p x}, SobolevSpace.toLp μ hQ u x^2 ∂μ) := by
  let Du := SobolevSpace.minimalSlope μ hQ u
  let S : Set X := {x | r ≤ dist p x}
  have hS : MeasurableSet S := (isClosed_le continuous_const (continuous_const.dist continuous_id)).measurableSet
  let T := ∫x in S, SobolevSpace.toLp μ hQ u x^2 ∂μ
  let F : ℝ → X → ℝ := fun N x => (radialCutoff p N x-radialCutoff p r x)^2*Du x^2
  let Fl : X → ℝ := fun x => (1-radialCutoff p r x)^2*Du x^2
  have hb (N : ℝ) (x : X) : |radialCutoff p N x-radialCutoff p r x| ≤ 1 := by
    rcases radialCutoff_bounds p N x with ⟨hNa,hNb⟩
    rcases radialCutoff_bounds p r x with ⟨hra,hrb⟩
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hFb (N : ℝ) (x : X) : ‖F N x‖ ≤ Du x^2 := by
    dsimp only [F]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have hh := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (hb N x)
    rw [sq_abs,one_pow] at hh
    exact mul_le_of_le_one_left (sq_nonneg _) hh
  have hFi {N : ℝ} (hN : 0 < N) : Integrable (F N) μ := by
    apply (Lp.memLp Du).integrable_sq.mono' _ (Eventually.of_forall (hFb N))
    exact (((radialCutoff_lipschitz p hN).continuous.sub
      (radialCutoff_lipschitz p hr).continuous).pow 2).aestronglyMeasurable.mul
      ((Lp.memLp Du).integrable_sq.aestronglyMeasurable)
  have hFli : Integrable Fl μ := by
    refine (Lp.memLp Du).integrable_sq.mono' ?_ ?_
    · exact ((continuous_const.sub (radialCutoff_lipschitz p hr).continuous).pow 2).aestronglyMeasurable.mul
        ((Lp.memLp Du).integrable_sq.aestronglyMeasurable)
    · filter_upwards with x
      dsimp only [Fl]
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have h := radialCutoff_bounds p r x
      have hh : (1-radialCutoff p r x)^2 ≤ 1 := by nlinarith [sq_nonneg (radialCutoff p r x)]
      exact mul_le_of_le_one_left (sq_nonneg _) hh
  have hlim : Tendsto (fun N : ℝ => ∫x, F N x ∂μ) atTop (𝓝 (∫x, Fl x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => Du x^2)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with N hN
      exact (hFi hN).aestronglyMeasurable
    · exact Eventually.of_forall fun N => Eventually.of_forall (hFb N)
    · exact (Lp.memLp Du).integrable_sq
    · filter_upwards with x
      apply tendsto_const_nhds.congr'
      filter_upwards [radialCutoff_eventually_one p x] with N hN
      simp only [Fl,F,hN]
  have hFe : ∀ᶠ N : ℝ in atTop, (∫x, F N x ∂μ) ≤ 2*‖g‖*Real.sqrt T+16/r^2*T := by
    filter_upwards [eventually_ge_atTop r] with N hN
    have hNp : 0 < N := hr.trans_le hN
    let L : ℝ≥0 := ⟨2/r,by positivity⟩
    have hLip : LipschitzWith L (fun x => radialCutoff p N x-radialCutoff p r x) := by
      apply ((radialCutoff_lipschitz p hNp).sub (radialCutoff_lipschitz p hr)).weaken
      change N⁻¹+r⁻¹ ≤ 2/r
      have hh := one_div_le_one_div_of_le hr hN
      simp only [one_div] at hh
      calc
        N⁻¹+r⁻¹ ≤ r⁻¹+r⁻¹ := by linarith
        _ = 2/r := by ring
    have hsup := (radialCutoff_hasCompactSupport p hNp).sub (radialCutoff_hasCompactSupport p hr)
    let η := SobolevSpace.ofLipschitzCompact μ hQ hLip hsup
    have hηr := SobolevSpace.ofLipschitzCompact_coe μ hQ hLip hsup
    have hηb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ (1:ℝ≥0) := by
      filter_upwards [hηr] with x hx
      rw [hx]
      exact hb N x
    have hηs : ∀ᵐ x ∂μ, x ∉ S → SobolevSpace.toLp μ hQ η x = 0 := by
      filter_upwards [hηr] with x hx hsx
      have hd : dist p x < r := lt_of_not_ge hsx
      rw [hx,radialCutoff_eq_one p hNp (hd.le.trans hN),radialCutoff_eq_one p hr hd.le,sub_self]
    have hh := caccioppoli_tail μ hQ u η g hg C 1 L hu hηb
      (SobolevSpace.ofLipschitzCompact_minimalSlope_le_lip μ hQ hLip hsup) hS hηs
    have he : (fun x => SobolevSpace.toLp μ hQ η x^2*Du x^2) =ᵐ[μ] F N := by
      filter_upwards [hηr] with x hx
      rw [hx]
    rw [integral_congr_ae he] at hh
    change (∫x, F N x ∂μ) ≤ 2*‖g‖*(1:ℝ)^2*Real.sqrt T+4*(2/r)^2*T at hh
    convert hh using 1 ; ring
  have hbound := le_of_tendsto hlim hFe
  have hI : (∫x in {x | 2*r ≤ dist p x}, Du x^2 ∂μ) ≤ ∫x, Fl x ∂μ := by
    have hM : MeasurableSet {x | 2*r ≤ dist p x} :=
      (isClosed_le continuous_const (continuous_const.dist continuous_id)).measurableSet
    rw [←integral_indicator hM]
    apply integral_mono_ae ((Lp.memLp Du).integrable_sq.indicator hM) hFli
    filter_upwards with x
    by_cases hx : x ∈ {x | 2*r ≤ dist p x}
    · rw [indicator_of_mem hx]
      simp only [Fl,radialCutoff_eq_zero p hr hx,sub_zero,one_pow,one_mul,le_refl]
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  exact hI.trans hbound


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem SobolevSpace.cutoff_error_slope_sq (u η : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C)
    (hη : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ D) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (u-SobolevSpace.product μ hQ η u D C) x^2 ≤
      2*(1-SobolevSpace.toLp μ hQ η x)^2*SobolevSpace.minimalSlope μ hQ u x^2+
      2*SobolevSpace.toLp μ hQ u x^2*SobolevSpace.minimalSlope μ hQ η x^2 := by
  let q := SobolevSpace.product μ hQ η u D C
  let w := u-q
  have he : localGamma μ hQ w w =ᵐ[μ] fun x =>
      (1-SobolevSpace.toLp μ hQ η x)^2*SobolevSpace.minimalSlope μ hQ u x^2+
      SobolevSpace.toLp μ hQ u x^2*SobolevSpace.minimalSlope μ hQ η x^2-
      2*(1-SobolevSpace.toLp μ hQ η x)*SobolevSpace.toLp μ hQ u x*localGamma μ hQ u η x := by
    filter_upwards [localGamma_sub_left μ hQ u q w,localGamma_product_left μ hQ η u w D C hη hu,
      localGamma_comm μ hQ u w,localGamma_sub_left μ hQ u q u,
      localGamma_product_left μ hQ η u u D C hη hu,localGamma_self μ hQ u,
      localGamma_comm μ hQ η u,localGamma_comm μ hQ η w,localGamma_sub_left μ hQ u q η,
      localGamma_product_left μ hQ η u η D C hη hu,localGamma_self μ hQ η]
      with x hww hqw huw hwu hqu huu hηu hηw hwη hqη hηη
    rw [hww,hqw,huw,hwu,hqu,huu,hηu,hηw,hwη,hqη,hηη]
    ring
  filter_upwards [he,localGamma_self μ hQ w,localGamma_abs_le μ hQ u η,
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ u),
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ η)] with x he hs hc hu hη
  change SobolevSpace.minimalSlope μ hQ w x^2 ≤ _
  rw [←hs,he]
  let f := 1-SobolevSpace.toLp μ hQ η x
  let g := SobolevSpace.toLp μ hQ u x
  let a := SobolevSpace.minimalSlope μ hQ u x
  let b := SobolevSpace.minimalSlope μ hQ η x
  let c := localGamma μ hQ u η x
  have hh : |f*g*c| ≤ |f| * a*(|g| * b) := by
    calc
      _ = (|f| * |g|)*|c| := by rw [abs_mul,abs_mul]
      _ ≤ (|f| * |g|)*(a*b) := mul_le_mul_of_nonneg_left hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by ring
  have hn := (abs_le.mp hh).1
  have hsq := sq_nonneg (|f| * a-|g| * b)
  simp only [sub_sq,mul_pow,sq_abs] at hsq
  change f^2*a^2+g^2*b^2-2*f*g*c ≤ 2*f^2*a^2+2*g^2*b^2
  nlinarith only [hn,hsq]

variable [IsFiniteMeasureOnCompacts μ]

theorem SobolevSpace.radial_cutoff_error_norm_sq (u : SobolevSpace μ hQ) (C : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C)
    (p : X) {r : ℝ} (hr : 0 < r) :
    ‖u-SobolevSpace.product μ hQ (radialSobolevCutoff μ hQ p hr) u 1 C‖^2 ≤
      (1+2/r^2)*(∫x in {x | r ≤ dist p x}, SobolevSpace.toLp μ hQ u x^2 ∂μ)+
      2*(∫x in {x | r ≤ dist p x}, SobolevSpace.minimalSlope μ hQ u x^2 ∂μ) := by
  let η := radialSobolevCutoff μ hQ p hr
  let w := u-SobolevSpace.product μ hQ η u 1 C
  let S : Set X := {x | r ≤ dist p x}
  have hS : MeasurableSet S := (isClosed_le continuous_const (continuous_const.dist continuous_id)).measurableSet
  have hηr := radialSobolevCutoff_coe μ hQ p hr
  have hηb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ (1:ℝ≥0) := by
    filter_upwards [hηr] with x hx
    rw [hx,abs_of_nonneg (radialCutoff_bounds p r x).1]
    exact (radialCutoff_bounds p r x).2
  have hwr : SobolevSpace.toLp μ hQ w =ᵐ[μ] fun x => (1-radialCutoff p r x)*SobolevSpace.toLp μ hQ u x := by
    simp only [w,map_sub]
    filter_upwards [SobolevSpace.product_coe μ hQ η u 1 C hηb hu,hηr,
      Lp.coeFn_sub (SobolevSpace.toLp μ hQ u) (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ η u 1 C))]
      with x hp hηr hw
    rw [hw,Pi.sub_apply,hp,hηr]
    ring
  have hcb (x : X) : (1-radialCutoff p r x)^2 ≤ 1 := by
    have h := radialCutoff_bounds p r x
    nlinarith [sq_nonneg (radialCutoff p r x)]
  have hv : (∫x, SobolevSpace.toLp μ hQ w x^2 ∂μ) ≤
      ∫x in S, SobolevSpace.toLp μ hQ u x^2 ∂μ := by
    rw [←integral_indicator hS]
    apply integral_mono_ae (Lp.memLp _).integrable_sq ((Lp.memLp _).integrable_sq.indicator hS)
    filter_upwards [hwr] with x hx
    rw [hx,mul_pow]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
      exact mul_le_of_le_one_left (sq_nonneg _) (hcb x)
    · rw [indicator_of_notMem hxS,radialCutoff_eq_one p hr (lt_of_not_ge hxS).le]
      simp
  have hD : (∫x, SobolevSpace.minimalSlope μ hQ w x^2 ∂μ) ≤
      2*(∫x in S, SobolevSpace.minimalSlope μ hQ u x^2 ∂μ)+
      (2/r^2)*(∫x in S, SobolevSpace.toLp μ hQ u x^2 ∂μ) := by
    rw [←integral_const_mul,←integral_const_mul,←integral_add
      ((Lp.memLp _).integrable_sq.const_mul 2).integrableOn
      ((Lp.memLp _).integrable_sq.const_mul (2/r^2)).integrableOn,←integral_indicator hS]
    apply integral_mono_ae (Lp.memLp _).integrable_sq
      ((((Lp.memLp _).integrable_sq.const_mul 2).add ((Lp.memLp _).integrable_sq.const_mul _)).indicator hS)
    filter_upwards [SobolevSpace.cutoff_error_slope_sq μ hQ u η C 1 hu hηb,hηr,
      radialSobolevCutoff_slope_bound μ hQ p hr,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ η),
      SobolevSpace.minimalSlope_zero_on_zero μ hQ w,hwr] with x hb hηr hηD hηD0 hz hwr
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
      rw [hηr] at hb
      have hDs : SobolevSpace.minimalSlope μ hQ η x^2 ≤ r⁻¹^2 :=
        pow_le_pow_left₀ hηD0 hηD 2
      have h1 := mul_le_mul_of_nonneg_right (hcb x) (sq_nonneg (SobolevSpace.minimalSlope μ hQ u x))
      have h2 := mul_le_mul_of_nonneg_left hDs (sq_nonneg (SobolevSpace.toLp μ hQ u x))
      change SobolevSpace.minimalSlope μ hQ w x^2 ≤ _
      calc
        _ ≤ _ := hb
        _ ≤ 2*SobolevSpace.minimalSlope μ hQ u x^2+2*(SobolevSpace.toLp μ hQ u x^2*r⁻¹^2) := by nlinarith only [h1,h2]
        _ = _ := by simp only [Pi.add_apply]; ring
    · rw [indicator_of_notMem hxS,hz (by rw [hwr,radialCutoff_eq_one p hr (lt_of_not_ge hxS).le]; simp)]
      norm_num
  rw [SobolevSpace.norm_sq,SobolevSpace.normSq,←SobolevSpace.minimalSlope_norm_sq,
    ←integral_sq_Lp,←integral_sq_Lp]
  change (∫x, SobolevSpace.toLp μ hQ w x^2 ∂μ)+(∫x, SobolevSpace.minimalSlope μ hQ w x^2 ∂μ) ≤ _
  nlinarith only [hv,hD]


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

theorem radialCutoff_mul_integrable (p : X) {R : ℝ} (hR : 0 < R)
    {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => radialCutoff p R x*f x) μ := by
  apply hf.norm.mono' ((radialCutoff_lipschitz p hR).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with x
  change ‖radialCutoff p R x*f x‖ ≤ ‖f x‖
  rw [norm_mul,Real.norm_of_nonneg (radialCutoff_bounds p R x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (radialCutoff_bounds p R x).2

theorem radialCutoff_mass_defect (p : X) {R : ℝ} (hR : 0 < R)
    {f : X → ℝ} (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f) (hm : ∫x, f x ∂μ = 1) :
    let m := ∫x, radialCutoff p R x*f x ∂μ
    0 ≤ m ∧ m ≤ 1 ∧ 1-m ≤ ∫x in {x | R ≤ dist p x}, f x ∂μ := by
  dsimp only
  have hi := radialCutoff_mul_integrable μ p hR hf
  refine ⟨integral_nonneg_of_ae (hf0.mono fun x hx => mul_nonneg (radialCutoff_bounds p R x).1 hx),?_,?_⟩
  · rw [←hm]
    exact integral_mono_ae hi hf (hf0.mono fun x hx => mul_le_of_le_one_left hx (radialCutoff_bounds p R x).2)
  · rw [←hm,←integral_sub hf hi]
    have hS : MeasurableSet {x : X | R ≤ dist p x} :=
      (isClosed_le continuous_const (continuous_const.dist continuous_id)).measurableSet
    rw [←integral_indicator hS]
    apply integral_mono_ae (hf.sub hi) (hf.indicator hS)
    filter_upwards [hf0] with x hx
    by_cases hxS : R ≤ dist p x
    · rw [indicator_of_mem (show x ∈ {x : X | R ≤ dist p x} from hxS)]
      change f x-radialCutoff p R x*f x ≤ f x
      exact sub_le_self _ (mul_nonneg (radialCutoff_bounds p R x).1 hx)
    · rw [indicator_of_notMem (show x ∉ {x : X | R ≤ dist p x} from hxS)]
      change f x-radialCutoff p R x*f x ≤ 0
      rw [radialCutoff_eq_one p hR (lt_of_not_ge hxS).le]
      simp

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
 theorem norm_sub_normalized_cutoff_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u q : E) {m : ℝ} (hm0 : (1:ℝ)/2 ≤ m) (hm1 : m ≤ 1) :
    ‖u-m⁻¹ • q‖ ≤ (1+2*(1-m))*‖u-q‖+2*(1-m)*‖u‖ := by
  have hmp : 0 < m := by linarith
  have hi0 : 1 ≤ m⁻¹ := (one_le_inv₀ hmp).mpr hm1
  have hi1 : m⁻¹ ≤ 2 := by
    calc
      _ ≤ ((1:ℝ)/2)⁻¹ := (inv_le_inv₀ hmp (by norm_num)).mpr hm0
      _ = 2 := by norm_num
  have hi : |1-m⁻¹| ≤ 2*(1-m) := by
    rw [abs_of_nonpos (by linarith)]
    have h := mul_le_mul_of_nonneg_right hi1 (sub_nonneg.mpr hm1)
    have he := inv_mul_cancel₀ hmp.ne'
    nlinarith only [h,he]
  have he : u-m⁻¹ • q = (u-q)+(1-m⁻¹) • q := by module
  have hq : ‖q‖ ≤ ‖u‖+‖u-q‖ := by simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub u q
  calc
    _ ≤ ‖u-q‖+‖(1-m⁻¹) • q‖ := by rw [he]; exact norm_add_le _ _
    _ = ‖u-q‖+|1-m⁻¹| *‖q‖ := by rw [norm_smul,Real.norm_eq_abs]
    _ ≤ ‖u-q‖+2*(1-m)*(‖u‖+‖u-q‖) := by
      exact add_le_add le_rfl (mul_le_mul hi hq (norm_nonneg _) (by linarith))
    _ = _ := by ring

variable [ProperSpace X] [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

noncomputable def SobolevSpace.radialProbabilityCutoff (u : SobolevSpace μ hQ)
    (C : ℝ≥0) (p : X) {R : ℝ} (hR : 0 < R) : SobolevSpace μ hQ :=
  (∫x, radialCutoff p R x*SobolevSpace.toLp μ hQ u x ∂μ)⁻¹ •
    SobolevSpace.product μ hQ (radialSobolevCutoff μ hQ p hR) u 1 C

theorem SobolevSpace.radialProbabilityCutoff_coe (u : SobolevSpace μ hQ)
    (C : ℝ≥0) (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C)
    (p : X) {R : ℝ} (hR : 0 < R) :
    SobolevSpace.toLp μ hQ (u.radialProbabilityCutoff μ hQ C p hR) =ᵐ[μ] fun x =>
      (∫y, radialCutoff p R y*SobolevSpace.toLp μ hQ u y ∂μ)⁻¹*
        (radialCutoff p R x*SobolevSpace.toLp μ hQ u x) := by
  let η := radialSobolevCutoff μ hQ p hR
  let q := SobolevSpace.product μ hQ η u 1 C
  let m := ∫y, radialCutoff p R y*SobolevSpace.toLp μ hQ u y ∂μ
  have hη := radialSobolevCutoff_coe μ hQ p hR
  have hηb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ (1:ℝ≥0) := by
    filter_upwards [hη] with x hx
    rw [hx,abs_of_nonneg (radialCutoff_bounds p R x).1]
    exact (radialCutoff_bounds p R x).2
  change SobolevSpace.toLp μ hQ (m⁻¹ • q) =ᵐ[μ] _
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul m⁻¹ (SobolevSpace.toLp μ hQ q),
    SobolevSpace.product_coe μ hQ η u 1 C hηb hu,hη] with x hx hq hη
  change SobolevSpace.toLp μ hQ (m⁻¹ • q) x = _
  change SobolevSpace.toLp μ hQ q x = SobolevSpace.toLp μ hQ η x*SobolevSpace.toLp μ hQ u x at hq
  rw [map_smul, hx]
  change m⁻¹ * SobolevSpace.toLp μ hQ q x = _
  rw [hq,hη]

theorem SobolevSpace.radialProbabilityCutoff_data (u : SobolevSpace μ hQ)
    (C : ℝ≥0) (hu : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ u x ∧ SobolevSpace.toLp μ hQ u x ≤ C)
    (hui : Integrable (SobolevSpace.toLp μ hQ u) μ) (_ : ∫x, SobolevSpace.toLp μ hQ u x ∂μ = 1)
    (p : X) {R : ℝ} (hR : 0 < R)
    (hm : (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*SobolevSpace.toLp μ hQ u x ∂μ) :
    let v := u.radialProbabilityCutoff μ hQ C p hR
    (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ v x ∧ SobolevSpace.toLp μ hQ v x ≤ 2*C) ∧
    (∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ v x ≠ 0 → dist p x ≤ 2*R) ∧
    Integrable (SobolevSpace.toLp μ hQ v) μ ∧ (∫x, SobolevSpace.toLp μ hQ v x ∂μ) = 1 := by
  dsimp only
  let m := ∫x, radialCutoff p R x*SobolevSpace.toLp μ hQ u x ∂μ
  have hmp : 0 < m := by dsimp [m]; linarith
  have hi : m⁻¹ ≤ 2 := by
    calc
      _ ≤ ((1:ℝ)/2)⁻¹ := (inv_le_inv₀ hmp (by norm_num)).mpr hm
      _ = 2 := by norm_num
  have hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C := hu.mono fun x hx => by rw [abs_of_nonneg hx.1]; exact hx.2
  have hv := u.radialProbabilityCutoff_coe μ hQ C hb p hR
  refine ⟨?_,?_,?_,?_⟩
  · filter_upwards [hv,hu] with x hx hu
    rw [hx]
    refine ⟨mul_nonneg (inv_nonneg.mpr hmp.le) (mul_nonneg (radialCutoff_bounds p R x).1 hu.1),?_⟩
    exact mul_le_mul hi ((mul_le_of_le_one_left hu.1 (radialCutoff_bounds p R x).2).trans hu.2)
      (mul_nonneg (radialCutoff_bounds p R x).1 hu.1) (by norm_num)
  · filter_upwards [hv] with x hx hh
    by_contra hn
    apply hh
    rw [hx,radialCutoff_eq_zero p hR (le_of_not_ge hn),zero_mul,mul_zero]
  · exact ((radialCutoff_mul_integrable μ p hR hui).const_mul m⁻¹).congr hv.symm
  · rw [integral_congr_ae hv,integral_const_mul]
    exact inv_mul_cancel₀ hmp.ne'


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

noncomputable def inverseInitialDensityPlan (π : Measure C(Time, X)) (ρ : X → ℝ) :
    Measure C(Time, X) := π.withDensity (fun γ => ENNReal.ofReal ((ρ (γ 0))⁻¹))

omit [MeasurableSpace X] [BorelSpace X] in
theorem inverseInitialDensityPlan_ac (π : Measure C(Time, X)) (ρ : X → ℝ) :
    inverseInitialDensityPlan π ρ ≪ π := withDensity_absolutelyContinuous _ _

theorem inverseInitialDensityPlan_initial (μ : Measure X) (π : Measure C(Time, X))
    {ρ : X → ℝ} (hρ : Measurable ρ) (hp : ∀ᵐ x ∂μ, 0 < ρ x)
    (h0 : π.map (fun γ => γ 0) = μ.withDensity (fun x => ENNReal.ofReal (ρ x))) :
    (inverseInitialDensityPlan π ρ).map (fun γ => γ 0) = μ := by
  have hm : Measurable (fun x => ENNReal.ofReal ((ρ x)⁻¹)) := hρ.inv.ennreal_ofReal
  change (π.withDensity ((fun x => ENNReal.ofReal ((ρ x)⁻¹)) ∘ (fun γ => γ 0))).map _ = _
  rw [map_withDensity_pullback π (measurable_path_eval 0) hm, h0,
    ← withDensity_mul μ hρ.ennreal_ofReal hm]
  calc
    _ = μ.withDensity (fun _ => (1 : ℝ≥0∞)) := by
      apply withDensity_congr_ae
      filter_upwards [hp] with x hx
      simp only [Pi.mul_apply, ← ENNReal.ofReal_mul hx.le, mul_inv_cancel₀ hx.ne', ENNReal.ofReal_one]
    _ = μ := withDensity_one

theorem inverseInitialDensityPlan_le (μ : Measure X) (π : Measure C(Time, X))
    {ρ : X → ℝ} {ε : ℝ} (hε : 0 < ε) (hl : ∀ᵐ x ∂μ, ε ≤ ρ x)
    (h0 : π.map (fun γ => γ 0) ≪ μ) :
    inverseInitialDensityPlan π ρ ≤ ENNReal.ofReal ε⁻¹ • π := by
  rw [← withDensity_const]
  apply withDensity_mono
  have hh := ae_of_ae_map (measurable_path_eval 0).aemeasurable (h0.ae_le hl)
  filter_upwards [hh] with γ hγ
  exact ENNReal.ofReal_le_ofReal (inv_anti₀ hε hγ)

theorem inverseInitialDensityPlan_compression (μ : Measure X) (π : Measure C(Time, X))
    {ρ : X → ℝ} {ε : ℝ} (hε : 0 < ε) (hl : ∀ᵐ x ∂μ, ε ≤ ρ x)
    {C : ℝ≥0∞} (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) (t : Time) :
    (inverseInitialDensityPlan π ρ).map (fun γ => γ t) ≤ (ENNReal.ofReal ε⁻¹ * C) • μ := by
  have hh := Measure.map_mono (inverseInitialDensityPlan_le μ π hε hl
    (Measure.absolutelyContinuous_of_le_smul (hcomp 0))) (measurable_path_eval t)
  rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable] at hh
  apply hh.trans
  intro s
  simpa only [Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_left (hcomp t s) (ENNReal.ofReal ε⁻¹)

theorem inverseInitialDensityPlan_finite (μ : Measure X) (π : Measure C(Time, X))
    [IsFiniteMeasure π] {ρ : X → ℝ} {ε : ℝ} (hε : 0 < ε) (hl : ∀ᵐ x ∂μ, ε ≤ ρ x)
    (h0 : π.map (fun γ => γ 0) ≪ μ) : IsFiniteMeasure (inverseInitialDensityPlan π ρ) := by
  let : IsFiniteMeasure (ENNReal.ofReal ε⁻¹ • π) := Measure.smul_finite π ENNReal.ofReal_ne_top
  exact isFiniteMeasure_of_le (ENNReal.ofReal ε⁻¹ • π)
    (inverseInitialDensityPlan_le μ π hε hl h0)

theorem inverseInitialDensityPlan_integral (π : Measure C(Time, X))
    {ρ : X → ℝ} (hρ : Measurable ρ) (hp : ∀ᵐ γ ∂π, 0 ≤ ρ (γ 0))
    (f : C(Time, X) → ℝ) :
    (∫ γ, f γ ∂inverseInitialDensityPlan π ρ) = ∫ γ, f γ / ρ (γ 0) ∂π := by
  have hm : Measurable (fun γ : C(Time, X) => ENNReal.ofReal ((ρ (γ 0))⁻¹)) :=
    hρ.inv.ennreal_ofReal.comp (measurable_path_eval 0)
  rw [inverseInitialDensityPlan, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hp] with γ hγ
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hγ), smul_eq_mul]
  ring


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

theorem log_linear_remainder_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (b - a) / a - (Real.log b - Real.log a) := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hh
  have he : b / a - 1 = (b - a) / a := by field_simp
  rw [he] at hh
  linarith

theorem log_linear_remainder_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b - a) / a - (Real.log b - Real.log a) ≤ (b - a)^2 / (a * b) := by
  have hh := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at hh
  calc
    _ ≤ (b - a) / a + (a / b - 1) := by linarith
    _ = _ := by field_simp ; ring

theorem log_linear_remainder_abs_le {a b ε : ℝ} (hε : 0 < ε) (ha : ε ≤ a) (hb : ε ≤ b) :
    |(b - a) / a - (Real.log b - Real.log a)| ≤ (ε^2)⁻¹ * (b - a)^2 := by
  rw [abs_of_nonneg (log_linear_remainder_nonneg (hε.trans_le ha) (hε.trans_le hb))]
  apply (log_linear_remainder_le (hε.trans_le ha) (hε.trans_le hb)).trans
  have hden : ε^2 ≤ a * b := by
    nlinarith [mul_le_mul ha hb hε.le (hε.trans_le ha).le]
  simpa only [div_eq_mul_inv, mul_comm] using
    (div_le_div_of_nonneg_left (sq_nonneg (b - a)) (sq_pos_of_pos hε) hden)


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem planInitialSecant_log_reweight_error (μ : Measure X)
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    {ρ G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ ρ G)
    {ε : ℝ} (hε : 0 < ε) (hl : ∀ᵐ x ∂μ, ε ≤ ρ x)
    (hlog : MemLp (fun x => Real.log (ρ x)) 2 μ)
    (t : Time) (ht : 0 < (t : ℝ)) :
    |planInitialSecant (inverseInitialDensityPlan π ρ) ρ t -
        planInitialSecant π (fun x => Real.log (ρ x)) t| ≤
      (t : ℝ) * ((ε^2)⁻¹ * D^2 * (C.toReal * ∫ x, G x^2 ∂μ)) := by
  have hlp (s : Time) : ∀ᵐ γ ∂π, ε ≤ ρ (γ s) :=
    ae_of_ae_map (measurable_path_eval s).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hcomp s)).ae_le hl)
  have hir (s : Time) : Integrable (fun γ : C(Time, X) => ρ (γ s)) π :=
    (compressionPullback_memLp μ π _ (measurable_path_eval s) hC (hcomp s) ρ).integrable (by norm_num)
  have hil (s : Time) : Integrable (fun γ : C(Time, X) => Real.log (ρ (γ s))) π := by
    exact ((hlog.of_measure_le_smul hC (hcomp s)).comp_of_map
      (measurable_path_eval s).aemeasurable).integrable (by norm_num)
  have hiq : Integrable (fun γ : C(Time, X) => (ρ (γ t)-ρ (γ 0)) / ρ (γ 0)) π := by
    simp_rw [div_eq_mul_inv]
    apply ((hir t).sub (hir 0)).mul_bdd
    · exact ((Lp.stronglyMeasurable ρ).measurable.comp (measurable_path_eval 0)).inv.aestronglyMeasurable
    · filter_upwards [hlp 0] with γ hγ
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hε.le.trans hγ))]
      exact inv_anti₀ hε hγ
  have hils : Integrable (fun γ : C(Time, X) => Real.log (ρ (γ t)) - Real.log (ρ (γ 0))) π :=
    (hil t).sub (hil 0)
  have hirem := hiq.sub hils
  have hisq := ((compressionPullback_memLp μ π _ (measurable_path_eval t) hC (hcomp t) ρ).sub
    (compressionPullback_memLp μ π _ (measurable_path_eval 0) hC (hcomp 0) ρ)).integrable_sq
  have hrem : |∫ γ : C(Time, X), (ρ (γ t)-ρ (γ 0)) / ρ (γ 0) -
      (Real.log (ρ (γ t))-Real.log (ρ (γ 0))) ∂π| ≤
      (ε^2)⁻¹ * ∫ γ : C(Time, X), (ρ (γ t)-ρ (γ 0))^2 ∂π := by
    apply (abs_integral_le_integral_abs).trans
    rw [← integral_const_mul]
    apply integral_mono_ae hirem.abs (hisq.const_mul _)
    filter_upwards [hlp t, hlp 0] with γ ht h0
    exact log_linear_remainder_abs_le hε h0 ht
  have hsq := hG.testPlan_integrated_square μ π hgeo hC hcomp hD hDb t
  have htotal := hrem.trans (mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (sq_nonneg ε)))
  simp_rw [planInitialSecant, geodesicExtension_eq]
  rw [inverseInitialDensityPlan_integral π (Lp.stronglyMeasurable ρ).measurable
    ((hlp 0).mono fun γ hh => hε.le.trans hh), ← sub_div,
    ← integral_sub hiq hils, abs_div, abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  convert htotal using 1 ; ring

theorem planInitialSecant_log_reweight_tendsto (μ : Measure X)
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    {ρ G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ ρ G)
    {ε : ℝ} (hε : 0 < ε) (hl : ∀ᵐ x ∂μ, ε ≤ ρ x)
    (hlog : MemLp (fun x => Real.log (ρ x)) 2 μ) :
    Tendsto (fun t => planInitialSecant (inverseInitialDensityPlan π ρ) ρ t -
      planInitialSecant π (fun x => Real.log (ρ x)) t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t : ℝ => t * ((ε^2)⁻¹ * D^2 * (C.toReal * ∫ x, G x^2 ∂μ)))
  · have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      (gt_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall, self_mem_nhdsWithin] with t ht1 ht0
    exact planInitialSecant_log_reweight_error μ π hgeo hC hcomp hD hDb hG hε hl hlog
      ⟨t, ht0.le, ht1.le⟩ ht0
  · simpa using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const
      ((ε^2)⁻¹ * D^2 * (C.toReal * ∫ x, G x^2 ∂μ))


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MetricSpace X] [BorelSpace X] in
theorem memLp_log_of_lower (μ : Measure X) [IsFiniteMeasure μ]
    (ρ : Lp ℝ 2 μ) {ε : ℝ} (hε : 0 < ε) (hl : ∀ᵐ x ∂μ, ε ≤ ρ x) :
    MemLp (fun x => Real.log (ρ x)) 2 μ := by
  have hmajor : MemLp (fun x => ρ x + (|Real.log ε| + 1)) 2 μ :=
    (Lp.memLp ρ).add (memLp_const _)
  apply hmajor.mono' (Real.measurable_log.comp (Lp.stronglyMeasurable ρ).measurable).aestronglyMeasurable
  filter_upwards [hl] with x hx
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  have hh := Real.log_le_log hε hx
  have hu := Real.log_le_sub_one_of_pos (hε.trans_le hx)
  have ha := neg_abs_le (Real.log ε)
  have hb := abs_nonneg (Real.log ε)
  dsimp only [Function.comp_def]
  constructor <;> linarith

theorem reference_log_signed_variation [ProperSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (u ρ : SobolevSpace μ hQ)
    {ε : ℝ} (hε : 0 < ε) (hl : ∀ᵐ x ∂μ, ε ≤ SobolevSpace.toLp μ hQ ρ x)
    (h0 : π.map (fun γ => γ 0) = μ.withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x + ψ y ≤ dist x y^2 / 2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0) + ψ (γ 1) = dist (γ 0) (γ 1)^2 / 2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1)) :
    Tendsto (planInitialSecant π (fun x => Real.log (SobolevSpace.toLp μ hQ ρ x)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-energyForm μ hQ u ρ)) := by
  let r := SobolevSpace.toLp μ hQ ρ
  let π' := inverseInitialDensityPlan π r
  have hlen := inverseInitialDensityPlan_le μ π hε hl
    (Measure.absolutelyContinuous_of_le_smul (hcomp 0))
  let : IsFiniteMeasure π' := inverseInitialDensityPlan_finite μ π hε hl
    (Measure.absolutelyContinuous_of_le_smul (hcomp 0))
  have hac : π' ≪ π := inverseInitialDensityPlan_ac π r
  have hcomp' := inverseInitialDensityPlan_compression μ π hε hl hcomp
  have hC' : ENNReal.ofReal ε⁻¹ * C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  have hD' : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π' :=
    hD.of_measure_le_smul ENNReal.ofReal_ne_top hlen
  have hinit : π'.map (fun γ => γ 0) = μ :=
    inverseInitialDensityPlan_initial μ π (Lp.stronglyMeasurable r).measurable
      (hl.mono fun _ hx => hε.trans_le hx) h0
  have hd := kantorovich_signed_first_variation μ hQ π' (hac.ae_le hgeo) hC' hcomp' hD'
    u ρ hu had (hac.ae_le hc) (hac.ae_le hb)
  rw [hinit, weightedGradientPair_reference] at hd
  have he := planInitialSecant_log_reweight_tendsto μ π hgeo hC hcomp hD hDb
    (SobolevSpace.minimalSlope_isRelaxed μ hQ ρ) hε hl (memLp_log_of_lower μ r hε hl)
  simpa only [π', r, sub_sub_cancel, sub_zero] using hd.sub he


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem reference_entropy_plan_bound [ProperSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀]
    (ρ : SobolevSpace μ hQ)
    {ε : ℝ} (hε : 0 < ε) (hl : ∀ᵐ x ∂μ, ε ≤ SobolevSpace.toLp μ hQ ρ x)
    (hν : ν₀ = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hmap0 : π.map (fun γ => γ 0) = ν₀)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (u : SobolevSpace μ hQ)
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x + ψ y ≤ dist x y^2 / 2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0) + ψ (γ 1) = dist (γ 0) (γ 1)^2 / 2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1))
    (K : ℝ)
    (hconv : ∀ t : Time,
      Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
        Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ ∧
      boltzmannEntropy μ (π.map (fun γ => γ t)) ≤
        (1 - (t : ℝ)) * boltzmannEntropy μ ν₀ + (t : ℝ) * boltzmannEntropy μ ν₁ +
        ((-K) * (t : ℝ) * (1 - (t : ℝ)) / 2) *
          (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π)) :
    -energyForm μ hQ u ρ ≤ boltzmannEntropy μ ν₁ - boltzmannEntropy μ ν₀ -
      (K / 2) * (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π) := by
  let r := SobolevSpace.toLp μ hQ ρ
  have hrn : (fun x => (ν₀.rnDeriv μ x).toReal) =ᵐ[μ] r := by
    rw [hν]
    filter_upwards [Measure.rnDeriv_withDensity μ (Lp.stronglyMeasurable r).measurable.ennreal_ofReal,
      hl] with x hx hxpos
    rw [hx, ENNReal.toReal_ofReal (hε.le.trans hxpos)]
  have hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal := by
    filter_upwards [hrn, hl] with x hx hh
    rw [hx]
    exact hε.trans_le hh
  have hi := memLp_log_of_lower μ r hε hl
  let g := hi.toLp (fun x => Real.log (r x))
  have hrep : g =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal := by
    filter_upwards [hi.coeFn_toLp, hrn] with x hx hh
    exact hx.trans (congrArg Real.log hh.symm)
  have hd := reference_log_signed_variation μ hQ π hgeo hC hcomp hD hDb u ρ
    hε hl (hmap0.trans hν) hu had hc hb
  have hdg : Tendsto (planInitialSecant π g) (𝓝[>] (0 : ℝ)) (𝓝 (-energyForm μ hQ u ρ)) := by
    apply hd.congr'
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      (gt_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall, self_mem_nhdsWithin] with t ht1 ht0
    exact (planInitialSecant_congr_ae μ π
      (fun s => Measure.absolutelyContinuous_of_le_smul (hcomp s)) hi.coeFn_toLp ⟨ht0.le, ht1.le⟩).symm
  exact entropy_plan_lp_signed_derivative_le μ ν₀ ν₁ hpos he0 g hrep π hmap0 hC hcomp K hconv hdg


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [CompactSpace X]

noncomputable def compactPotentialLipschitz : ℝ≥0 :=
  2 * ⟨‖compactDistanceCost (X := X)‖, norm_nonneg _⟩

theorem hopfLax_sub_const {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 < t) (c : ℝ) (x : X) :
    hopfLax (fun y => f y - c) t x = hopfLax f t x - c := by
  have hg : LipschitzWith L (fun y => f y - c) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hf.dist_le_mul x y
  obtain ⟨y, hy, _⟩ := hopfLax_exists_minimizer hf ht x
  obtain ⟨z, hz, _⟩ := hopfLax_exists_minimizer hg ht x
  have hb := hopfLax_le_cost hg ht x y
  have hb' := hopfLax_le_cost hf ht x z
  linarith

theorem hopfLax_unit_uniform_lipschitz {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith (compactPotentialLipschitz (X := X)) (hopfLax f 1) := by
  have hbound (x y : X) : hopfLax f 1 x - hopfLax f 1 y ≤
      (compactPotentialLipschitz (X := X) : ℝ) * dist x y := by
    obtain ⟨z, hz, _⟩ := hopfLax_exists_minimizer hf (show (0 : ℝ) < 1 by norm_num) y
    have hb := hopfLax_le_cost hf (show (0 : ℝ) < 1 by norm_num) x z
    have hc := (compactSquaredCost_lipschitz (X := X)).dist_le_mul (x,z) (y,z)
    change |dist x z^2 / 2 - dist y z^2 / 2| ≤ _ at hc
    simp only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] at hc
    have hh := (le_abs_self (dist x z^2 / 2 - dist y z^2 / 2)).trans hc
    change hopfLax f 1 y = f z + dist y z^2 / (2*1) at hz
    change hopfLax f 1 x ≤ f z + dist x z^2 / (2*1) at hb
    change hopfLax f 1 x - hopfLax f 1 y ≤ (2*‖compactDistanceCost (X := X)‖) * dist x y
    norm_num only [mul_one] at hz hb
    change dist x z^2 / 2 - dist y z^2 / 2 ≤
      (2*‖compactDistanceCost (X := X)‖) * dist x y at hh
    exact by linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  constructor
  · have hh := hbound y x
    rw [dist_comm y x] at hh
    linarith
  · exact hbound x y

variable [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem IsOptimalCoupling.normalized_compact_sobolev_potential
    (μ : Measure X) [IsFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
    (hgeo : IsGeodesicSpace X) (p : X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] (hac : ν₀ ≪ μ)
    {π : Measure (X × X)} (hp : IsOptimalCoupling ν₀ ν₁ π) :
    ∃ (u : SobolevSpace μ hQ) (φ ψ : X → ℝ),
      LipschitzWith (compactPotentialLipschitz (X := X)) φ ∧ Continuous ψ ∧
      φ p = 0 ∧ (φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (∀ x y, φ x + ψ y ≤ dist x y^2 / 2) ∧
      (∀ᵐ xy ∂π, φ xy.1 + ψ xy.2 = dist xy.1 xy.2^2 / 2) ∧
      (∀ᵐ xy ∂π, SobolevSpace.minimalSlope μ hQ u xy.1 ≤ dist xy.1 xy.2) := by
  obtain ⟨φ₀, ψ₀, ⟨L, hφ₀, hψ₀⟩, had₀, hc₀⟩ := hp.compact_potentials ν₀ ν₁
  let c := hopfLax (-ψ₀) 1 p
  let ψ : X → ℝ := fun x => ψ₀ x + c
  have hψ : LipschitzWith L ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [ψ, dist_add_right] using hψ₀.dist_le_mul x y
  let f : X → ℝ := -ψ
  have hf : LipschitzWith L f := hψ.neg
  have hLip := hopfLax_lipschitz hf hgeo (show (0 : ℝ) < 1 by norm_num)
  let u := SobolevSpace.ofLipschitzCompact μ hQ hLip (HasCompactSupport.of_compactSpace _)
  have had (x y : X) : (φ₀ x - c) + ψ y ≤ dist x y^2 / 2 := by
    dsimp only [ψ]
    linarith [had₀ x y]
  have hc : ∀ᵐ xy ∂π, (φ₀ xy.1 - c) + ψ xy.2 = dist xy.1 xy.2^2 / 2 := by
    filter_upwards [hc₀] with xy hxy
    dsimp only [ψ]
    linarith
  refine ⟨u, hopfLax f 1, ψ, hopfLax_unit_uniform_lipschitz hf, hψ.continuous, ?_,
    (SobolevSpace.ofLipschitzCompact_coe μ hQ hLip (HasCompactSupport.of_compactSpace _)).symm,
    ?_, ?_, ?_⟩
  · have he : f = fun x => (-ψ₀) x - c := by
      funext x
      dsimp only [f, ψ, Pi.neg_apply, ContinuousMap.neg_apply]
      ring
    rw [he, hopfLax_sub_const (f := fun x => (-ψ₀) x) hψ₀.neg (show (0 : ℝ) < 1 by norm_num)]
    exact sub_self _
  · intro x y
    have hh := hopfLax_le_cost hf (show (0 : ℝ) < 1 by norm_num) x y
    change hopfLax f 1 x ≤ -ψ y + dist x y^2 / (2*1) at hh
    linarith
  · filter_upwards [hc] with xy hxy
    have he := (hopfLax_of_contact hψ had hxy).1
    change hopfLax (-ψ) 1 xy.1 + ψ xy.2 = _
    rw [he]
    exact hxy
  · have hbound := (hopfLeftRadius_minimalSlope_bound μ hQ hf hgeo).filter_mono hac.ae_le
    rw [← hp.1] at hbound
    have hb := ae_of_ae_map measurable_fst.aemeasurable hbound
    filter_upwards [hb, hc] with xy hh hxy
    exact hh.trans (hopfLeftRadius_le_minimizer hf (hopfLax_of_contact hψ had hxy).2)


end

 
section

 

open Set Filter MeasureTheory Metric Bornology TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.compact_energy_subgradient [CompactSpace X]
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (ρ : SobolevSpace (hausdorff n X) hX.quadratic)
    {ε : ℝ} (hε : 0 < ε) (hl : ∀ᵐ x ∂hausdorff n X, ε ≤ SobolevSpace.toLp _ _ ρ x)
    (hν : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ _ ρ x))) :
    ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (φ ψ : X → ℝ),
      LipschitzWith (compactPotentialLipschitz (X := X)) φ ∧ Continuous ψ ∧
      φ p = 0 ∧ (φ =ᵐ[hausdorff n X] SobolevSpace.toLp _ _ u) ∧
      (∀ x y, φ x + ψ y ≤ dist x y^2 / 2) ∧
      (∫ x, φ x ∂ν₀) + (∫ x, ψ x ∂ν₁) = (wassersteinSq ν₀ ν₁).toReal / 2 ∧
      -energyForm (hausdorff n X) hX.quadratic u ρ ≤
        boltzmannEntropy (hausdorff n X) ν₁ - boltzmannEntropy (hausdorff n X) ν₀ -
          (K / 2) * (wassersteinSq ν₀ ν₁).toReal := by
  let : SeparableSpace X := hX.separable
  let : IsFiniteMeasure (hausdorff n X) := ⟨hX.finiteOnBounded univ (isBounded_univ.mpr inferInstance)⟩
  let μ := hausdorff n X
  obtain ⟨R, hR, hRball⟩ := (isBounded_univ.mpr (inferInstance : BoundedSpace X)).subset_closedBall_lt (0 : ℝ) p
  have hs (ν : Measure X) : ∀ᵐ x ∂ν, dist x p ≤ R :=
    ae_of_all _ fun x => hRball (mem_univ x)
  obtain ⟨π, hπ, hg, hp, hi, hall⟩ := hX.exists_bounded_entropy_plan K n hn
    ν₀ ν₁ hC h0 h1 p hR.le (hs ν₀) (hs ν₁)
  let := hπ
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ := by
    simpa only [hend.1] using (hall 0).2.1
  obtain ⟨u, φ, ψ, hφ, hψ, hp0, hu, had, hc, hb⟩ :=
    hp.normalized_compact_sobolev_potential μ hX.quadratic hX.geodesic p ν₀ ν₁
      (Measure.absolutelyContinuous_of_le_smul h0)
  have hm : Measurable (fun γ : C(Time, X) => (γ 0, γ 1)) :=
    (measurable_path_eval 0).prodMk (measurable_path_eval 1)
  have hc' := ae_of_ae_map hm.aemeasurable hc
  have hb' := ae_of_ae_map hm.aemeasurable hb
  have hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π :=
    (memLp_two_iff_integrable_sq ((measurable_path_eval 0).dist
      (measurable_path_eval 1)).aestronglyMeasurable).mpr hi
  have hDb := optimalPlanDistanceBound_of_bounded ν₀ ν₁ p (hs ν₀) (hs ν₁) π hπ hg hp
  have hbnd := reference_entropy_plan_bound μ hX.quadratic ν₀ ν₁ ρ hε hl hν he0
    π hg hend.1 (compressionBudget_ne_top K n (2*R) hC) (fun t => (hall t).1)
    hD hDb u hu had hc' hb' K (fun t => (hall t).2)
  have he : (wassersteinSq ν₀ ν₁).toReal = ∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π := by
    rw [wassersteinSq_eq_cost hp, transportCost_plan_eq_integral π hi,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hiφ : Integrable φ ν₀ :=
    (hφ.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (p := 1)).integrable le_rfl
  have hiψ : Integrable ψ ν₁ :=
    (hψ.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (p := 1)).integrable le_rfl
  have hiφp : Integrable (fun γ : C(Time, X) => φ (γ 0)) π := by
    rw [← hend.1] at hiφ
    exact hiφ.comp_measurable (measurable_path_eval 0)
  have hiψp : Integrable (fun γ : C(Time, X) => ψ (γ 1)) π := by
    rw [← hend.2] at hiψ
    exact hiψ.comp_measurable (measurable_path_eval 1)
  have hdual := integral_congr_ae hc'
  rw [integral_add hiφp hiψp, integral_div,
    ← integral_map (measurable_path_eval 0).aemeasurable hφ.continuous.aestronglyMeasurable,
    ← integral_map (measurable_path_eval 1).aemeasurable hψ.aestronglyMeasurable,
    hend.1, hend.2, ← he] at hdual
  exact ⟨u, φ, ψ, hφ, hψ, hp0, hu, had, hdual, he ▸ hbnd⟩


end

 
section

 

open Set Filter MeasureTheory Metric Bornology TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def compactPotentialL2Bound (μ : Measure X) : ℝ :=
  (measureUnivNNReal μ : ℝ) ^ (2 : ℝ)⁻¹ *
    ((compactPotentialLipschitz (X := X) : ℝ) * ‖compactDistanceCost (X := X)‖)

omit [BorelSpace X] in
theorem compactPotentialL2Bound_nonneg (μ : Measure X) : 0 ≤ compactPotentialL2Bound μ := by
  unfold compactPotentialL2Bound
  positivity

omit [BorelSpace X] in
theorem normalized_potential_norm_le (μ : Measure X) [IsFiniteMeasure μ]
    (hQ : QuadraticCheegerEnergy μ) (p : X) (u : SobolevSpace μ hQ)
    {φ : X → ℝ} (hφ : LipschitzWith (compactPotentialLipschitz (X := X)) φ)
    (hp : φ p = 0) (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) :
    ‖SobolevSpace.toLp μ hQ u‖ ≤ compactPotentialL2Bound μ := by
  have hb (x : X) : ‖φ x‖ ≤
      (compactPotentialLipschitz (X := X) : ℝ) * ‖compactDistanceCost (X := X)‖ := by
    have hd : dist x p ≤ ‖compactDistanceCost (X := X)‖ := by
      simpa only [compactDistanceCost, ContinuousMap.coe_mk, Real.norm_eq_abs,
        abs_of_nonneg dist_nonneg] using (compactDistanceCost (X := X)).norm_coe_le_norm (x,p)
    have hh := hφ.dist_le_mul x p
    rw [hp, dist_zero_right] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg _))
  have hh := Lp.norm_le_of_ae_bound (f := SobolevSpace.toLp μ hQ u)
    (C := (compactPotentialLipschitz (X := X) : ℝ) * ‖compactDistanceCost (X := X)‖)
    (by positivity) (hu.mono fun x hx => hx ▸ hb x)
  simpa only [compactPotentialL2Bound, ENNReal.toReal_ofNat] using hh

theorem compact_dual_le_wasserstein (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {φ ψ : X → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (had : ∀ x y, φ x + ψ y ≤ dist x y^2 / 2) :
    (∫ x, φ x ∂ν₀) + (∫ x, ψ x ∂ν₁) ≤ (wassersteinSq ν₀ ν₁).toReal / 2 := by
  obtain ⟨π, φ₀, ψ₀, hprob, hf, hs, _, had₀, hc₀, _⟩ := compact_squared_cost_potentials ν₀ ν₁
  let := hprob
  have hp := compact_contact_isOptimal hf hs φ₀ ψ₀ had₀ hc₀
  have hi : Integrable (fun xy : X×X => dist xy.1 xy.2^2) π :=
    ((continuous_fst.dist continuous_snd).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let Φ : C(X, ℝ) := ⟨φ, hφ⟩
  let Ψ : C(X, ℝ) := ⟨ψ, hψ⟩
  have hh := integral_mono (compact_continuous_integrable π (separatedSum Φ Ψ))
    (hi.div_const 2) (fun xy : X×X => had xy.1 xy.2)
  rw [compact_coupling_separated_integral ν₀ ν₁ π hf hs, integral_div] at hh
  rw [wassersteinSq_eq_cost hp, compact_transportCost_integral,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  exact hh

theorem heat_dual_secant (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    (hQ : QuadraticCheegerEnergy μ) (f : Lp ℝ 2 μ) (hf : 0 ≤ f)
    (ν : Measure X) [IsProbabilityMeasure ν] (s t : ℝ)
    [IsProbabilityMeasure (heatMeasure μ hQ s f)] [IsProbabilityMeasure (heatMeasure μ hQ t f)]
    (u : SobolevSpace μ hQ) {φ ψ : X → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x + ψ y ≤ dist x y^2 / 2)
    (hdual : (∫ x, φ x ∂heatMeasure μ hQ s f) + (∫ x, ψ x ∂ν) =
      (wassersteinSq (heatMeasure μ hQ s f) ν).toReal / 2) :
    ((wassersteinSq (heatMeasure μ hQ s f) ν).toReal -
      (wassersteinSq (heatMeasure μ hQ t f) ν).toReal) / 2 ≤
        inner ℝ (heatAt μ hQ s f - heatAt μ hQ t f) (SobolevSpace.toLp μ hQ u) := by
  have hw := compact_dual_le_wasserstein (heatMeasure μ hQ t f) ν hφ hψ had
  rw [integral_heatMeasure μ hQ f hf s φ] at hdual
  rw [integral_heatMeasure μ hQ f hf t φ] at hw
  have he (r : ℝ) : (∫ x, φ x * heatAt μ hQ r f x ∂μ) =
      inner ℝ (heatAt μ hQ r f) (SobolevSpace.toLp μ hQ u) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    simp only [hx, Real.inner_apply, mul_comm]
  rw [he s] at hdual
  rw [he t] at hw
  rw [inner_sub_left]
  linarith


end

 
section

 

open Set Filter MeasureTheory Metric Bornology TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]

omit [SeparableSpace X] in
theorem NoncollapsedRCD.compact_heat_lower
    (K : ℝ) (n : ℕ) [IsFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ᵐ x ∂hausdorff n X, c ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂hausdorff n X, c ≤ heatAt (hausdorff n X) hX.quadratic t f x := by
  let : SeparableSpace X := hX.separable
  let : IsFiniteMeasure (hausdorff n X) := ⟨hX.finiteOnBounded univ (isBounded_univ.mpr inferInstance)⟩
  let μ := hausdorff n X
  let g : Lp ℝ 2 μ := Lp.const 2 μ c
  have hg : g =ᵐ[μ] fun _ => c := Lp.coeFn_const 2 μ c
  have hg0 : 0 ≤ g := (Lp.coeFn_nonneg g).mp (hg.mono fun _ hx => hx ▸ hc)
  have hgfi : Integrable g μ := (Lp.memLp g).integrable (by norm_num)
  have hi : Integrable (heatAt μ hX.quadratic t g) μ :=
    (Lp.memLp _).integrable (by norm_num)
  have hup := heatAt_le_const μ hX.quadratic t hc g (hg.mono fun _ hx => hx.le)
  have hmass := hX.conservative K n hn p g hg0 hgfi t ht
  have hfixed : (heatAt μ hX.quadratic t g) =ᵐ[μ] g :=
    (integral_eq_iff_of_ae_le hi hgfi (by
      filter_upwards [hup, hg] with x hx he
      rwa [he])).mp hmass
  have hgf : g ≤ f := (Lp.coeFn_le g f).mp (by
    filter_upwards [hg, hf] with x hx hh
    rwa [hx])
  have hm := (Lp.coeFn_le _ _).mpr (heatAt_mono μ hX.quadratic t hgf)
  filter_upwards [hm, hfixed, hg] with x hx he hh
  rwa [he, hh] at hx

omit [SeparableSpace X] in
theorem NoncollapsedRCD.compact_heat_probability
    (K : ℝ) (n : ℕ) [IsFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (hf : 0 ≤ f)
    (hm : ∫ x, f x ∂hausdorff n X = 1) {t : ℝ} (ht : 0 ≤ t) :
    IsProbabilityMeasure (heatMeasure (hausdorff n X) hX.quadratic t f) := by
  let : SeparableSpace X := hX.separable
  let : IsFiniteMeasure (hausdorff n X) := ⟨hX.finiteOnBounded univ (isBounded_univ.mpr inferInstance)⟩
  let μ := hausdorff n X
  have hi : Integrable f μ := (Lp.memLp f).integrable (by norm_num)
  constructor
  rw [heatMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (heatAt_integrable_of_nonneg μ hX.quadratic t f hf hi)
      ((Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hX.quadratic t f hf)),
    hX.conservative K n hn p f hf hi t ht, hm, ENNReal.ofReal_one]


end

 
section

 

open Set Filter MeasureTheory Metric Bornology TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def heatEviRemainder [ProperSpace X] (μ : Measure X) [μ.Regular]
    (hQ : QuadraticCheegerEnergy μ) (f : Lp ℝ 2 μ) (t h : ℝ) : ℝ :=
  ‖h⁻¹ • (heatAt μ hQ (t+h) f - heatAt μ hQ t f) + heatGeneratorAt μ hQ (t+h) f‖

theorem heatEviRemainder_tendsto [ProperSpace X] (μ : Measure X) [μ.Regular]
    (hQ : QuadraticCheegerEnergy μ) (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    Tendsto (heatEviRemainder μ hQ f t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hd := (heatAt_hasDerivAt μ hQ t ht f).tendsto_slope_zero_right
  have hc : Tendsto (fun h : ℝ => heatGeneratorAt μ hQ (t+h) f) (𝓝[>] 0)
      (𝓝 (heatGeneratorAt μ hQ t f)) := by
    exact (heatGeneratorAt_continuousAt μ hQ f t ht).tendsto.comp
      (by simpa using (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun h : ℝ => t+h) (𝓝[>] 0) (𝓝 (t+0))))
  unfold heatEviRemainder
  simpa only [neg_add_cancel, norm_zero] using (hd.add hc).norm

theorem heatMeasure_le_const [ProperSpace X] (μ : Measure X) [μ.Regular]
    (hQ : QuadraticCheegerEnergy μ) (f : Lp ℝ 2 μ) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ᵐ x ∂μ, f x ≤ c) (t : ℝ) :
    heatMeasure μ hQ t f ≤ ENNReal.ofReal c • μ := by
  rw [heatMeasure, ← withDensity_const]
  exact withDensity_mono ((heatAt_le_const μ hQ t hc f hf).mono fun _ hx => ENNReal.ofReal_le_ofReal hx)

variable [CompactSpace X] [SeparableSpace X]

omit [SeparableSpace X] in
theorem NoncollapsedRCD.compact_heat_EVI_secant
    (K : ℝ) (n : ℕ) [IsFiniteMeasure (hausdorff n X)]
    (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f)
    (hfm : ∫ x, f x ∂hausdorff n X = 1)
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hfl : ∀ᵐ x ∂hausdorff n X, ε ≤ f x)
    (hfu : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≤ ENNReal.ofReal C • hausdorff n X)
    {t h : ℝ} (ht : 0 < t) (hh : 0 < h) :
    ((wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic (t+h) f) ν).toReal -
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic t f) ν).toReal) / (2*h) ≤
        boltzmannEntropy (hausdorff n X) ν -
          boltzmannEntropy (hausdorff n X) (heatMeasure (hausdorff n X) hX.quadratic (t+h) f) -
        (K/2) * (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic (t+h) f) ν).toReal +
        compactPotentialL2Bound (hausdorff n X) * heatEviRemainder (hausdorff n X) hX.quadratic f t h := by
  let μ := hausdorff n X
  let : IsProbabilityMeasure (heatMeasure μ hX.quadratic t f) :=
    hX.compact_heat_probability K n hn p f hf0 hfm ht.le
  let : IsProbabilityMeasure (heatMeasure μ hX.quadratic (t+h) f) :=
    hX.compact_heat_probability K n hn p f hf0 hfm (add_pos ht hh).le
  let ρ := heatSobolev μ hX.quadratic (t+h) (add_pos ht hh) f
  have hl : ∀ᵐ x ∂μ, ε ≤ SobolevSpace.toLp μ hX.quadratic ρ x :=
    hX.compact_heat_lower K n hn p f hε.le hfl (add_pos ht hh).le
  obtain ⟨u, φ, ψ, hφ, hψ, hp, hu, had, hdual, hbound⟩ :=
    hX.compact_energy_subgradient K n hn p (heatMeasure μ hX.quadratic (t+h) f) ν
      ENNReal.ofReal_ne_top (heatMeasure_le_const μ hX.quadratic f hC hfu (t+h)) hν
      ρ hε hl rfl
  have hs := heat_dual_secant μ hX.quadratic f hf0 ν (t+h) t u hφ.continuous hψ hu had hdual
  have hsn := (div_le_div_of_nonneg_right hs hh.le)
  have hun := normalized_potential_norm_le μ hX.quadratic p u hφ hp hu
  let v := h⁻¹ • (heatAt μ hX.quadratic (t+h) f - heatAt μ hX.quadratic t f)
  let A := heatGeneratorAt μ hX.quadratic (t+h) f
  have hc := (real_inner_le_norm (v+A) (SobolevSpace.toLp μ hX.quadratic u)).trans
    (mul_le_mul_of_nonneg_left hun (norm_nonneg _))
  have he : energyForm μ hX.quadratic u ρ = inner ℝ A (SobolevSpace.toLp μ hX.quadratic u) := by
    rw [energyForm_comm, heatGenerator_form]
    simp only [A, heatGeneratorAt_of_pos μ hX.quadratic (t+h) (add_pos ht hh)]
  rw [he] at hbound
  have hsn' : ((wassersteinSq (heatMeasure μ hX.quadratic (t+h) f) ν).toReal -
      (wassersteinSq (heatMeasure μ hX.quadratic t f) ν).toReal) / (2*h) ≤
      inner ℝ v (SobolevSpace.toLp μ hX.quadratic u) := by
    simpa only [v, inner_smul_left, RCLike.conj_to_real, div_mul_eq_div_mul_one_div,
      div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hsn
  change _ ≤ _ + compactPotentialL2Bound μ * ‖v+A‖
  rw [inner_add_left] at hc
  nlinarith only [hsn', hbound, hc]


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heatGeneratorAt_hasDerivAt_split (f : Lp ℝ 2 μ) {a t : ℝ}
    (ha : 0 < a) (hat : a < t) :
    HasDerivAt (fun s => heatGeneratorAt μ hQ s f)
      (-heatGeneratorAt μ hQ (t-a) (heatGeneratorAt μ hQ a f)) t := by
  have hd := (heatAt_hasDerivAt μ hQ (t-a) (sub_pos.mpr hat)
    (heatGeneratorAt μ hQ a f)).scomp t ((hasDerivAt_id t).sub_const a)
  simp only [one_smul] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hat] with s hs
  rw [heatGeneratorAt_of_pos μ hQ s (ha.trans hs),heatGeneratorAt_of_pos μ hQ a ha]
  have he := heatGenerator_add μ hQ (s-a) a (sub_nonneg.mpr hs.le) ha
  simp only [sub_add_cancel] at he
  rw [he,mul_apply_eq_comp]
  rfl

theorem heatGeneratorAt_norm_sub_le (f : Lp ℝ 2 μ) {t s z : ℝ}
    (ht : 0 < t) (hs : t ≤ s) (hz : t ≤ z) :
    ‖heatGeneratorAt μ hQ s f-heatGeneratorAt μ hQ z f‖ ≤
      (2*(1+1/(t/2)))^2*‖f‖*|s-z| := by
  let A := 2*(1+1/(t/2))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb (x : ℝ) (hx : x ∈ Ici t) :
      ‖-heatGeneratorAt μ hQ (x-t/2) (heatGeneratorAt μ hQ (t/2) f)‖ ≤ A^2*‖f‖ := by
    rw [norm_neg]
    have h1 := (heatGeneratorAt μ hQ (x-t/2)).le_of_opNorm_le
      (heatGeneratorAt_norm_le_of_ge μ hQ (t/2) (half_pos ht) (x-t/2) (by have hx' : t ≤ x := hx; linarith))
      (heatGeneratorAt μ hQ (t/2) f)
    have h2 := (heatGeneratorAt μ hQ (t/2)).le_of_opNorm_le
      (heatGeneratorAt_norm_le_of_ge μ hQ (t/2) (half_pos ht) (t/2) le_rfl) f
    calc
      _ ≤ A*‖heatGeneratorAt μ hQ (t/2) f‖ := h1
      _ ≤ A*(A*‖f‖) := mul_le_mul_of_nonneg_left h2 hA
      _ = _ := by ring
  have hv := (convex_Ici t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (heatGeneratorAt_hasDerivAt_split μ hQ f (half_pos ht)
      (show t/2 < x by have hx' : t ≤ x := hx; linarith)).hasDerivWithinAt) hb hz hs
  simpa only [Real.norm_eq_abs] using hv

theorem heatEviRemainder_le (f : Lp ℝ 2 μ) {t h : ℝ} (ht : 0 < t) (hh : 0 < h) :
    heatEviRemainder μ hQ f t h ≤ (2*(1+1/(t/2)))^2*‖f‖*h := by
  let A := (2*(1+1/(t/2)))^2*‖f‖
  let G := heatGeneratorAt μ hQ (t+h) f
  let F : ℝ → Lp ℝ 2 μ := fun s => heatAt μ hQ s f+s • G
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd (s : ℝ) (hs : s ∈ Icc t (t+h)) :
      HasDerivAt F (-heatGeneratorAt μ hQ s f+G) s := by
    convert! (heatAt_hasDerivAt μ hQ s (ht.trans_le hs.1) f).add
      ((hasDerivAt_id s).smul_const G) using 1 ; simp
  have hb (s : ℝ) (hs : s ∈ Icc t (t+h)) : ‖-heatGeneratorAt μ hQ s f+G‖ ≤ A*h := by
    rw [neg_add_eq_sub, norm_sub_rev]
    have hv := heatGeneratorAt_norm_sub_le μ hQ f ht hs.1 (le_add_of_nonneg_right hh.le)
    rw [abs_of_nonpos (sub_nonpos.mpr hs.2)] at hv
    exact hv.trans (mul_le_mul_of_nonneg_left (by linarith [hs.1]) hA)
  have hr := (convex_Icc t (t+h)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt) hb
    (left_mem_Icc.mpr (le_add_of_nonneg_right hh.le))
    (right_mem_Icc.mpr (le_add_of_nonneg_right hh.le))
  rw [add_sub_cancel_left,Real.norm_eq_abs,abs_of_pos hh] at hr
  have he : h⁻¹ • (F (t+h)-F t) =
      h⁻¹ • (heatAt μ hQ (t+h) f-heatAt μ hQ t f)+G := by
    have he : F (t+h)-F t = heatAt μ hQ (t+h) f-heatAt μ hQ t f+h • G := by
      dsimp [F]
      module
    rw [he,smul_add,smul_smul,inv_mul_cancel₀ hh.ne',one_smul]
  change ‖h⁻¹ • (heatAt μ hQ (t+h) f-heatAt μ hQ t f)+G‖ ≤ A*h
  rw [←he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh)]
  calc
    _ ≤ h⁻¹*(A*h*h) := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hh.le)
    _ = A*h := by field_simp


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)

theorem heatSobolev_cutoff_norm_sq_le (f : Lp ℝ 2 μ) (C : ℝ≥0)
    (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂μ, f x ≤ C) (p : X) {t : ℝ} (ht : 0 < t)
    {R : ℝ} (hR : 1 ≤ R) :
    let u := heatSobolev μ hQ t ht f
    let T := ∫x in {x | R/2 ≤ dist p x}, heatAt μ hQ t f x^2 ∂μ
    ‖u-SobolevSpace.product μ hQ (radialSobolevCutoff μ hQ p (lt_of_lt_of_le zero_lt_one hR)) u 1 C‖^2 ≤
      131*T+4*‖heatGenerator μ hQ t ht f‖*Real.sqrt T := by
  dsimp only
  let u := heatSobolev μ hQ t ht f
  let T := ∫x in {x | R/2 ≤ dist p x}, heatAt μ hQ t f x^2 ∂μ
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf0),
      heatAt_le_const μ hQ t (NNReal.coe_nonneg C) f hfC] with x hx hy
    simpa only [u,heatSobolev_toLp,abs_of_nonneg hx] using hy
  have hb := SobolevSpace.radial_cutoff_error_norm_sq μ hQ u C hu p hRp
  have hG := caccioppoli_exterior μ hQ u (-heatGenerator μ hQ t ht f)
    (heatSobolev_weak_laplacian μ hQ t ht f) C hu p (half_pos hRp)
  simp only [u,heatSobolev_toLp,norm_neg] at hb hG
  have h2 : 2*(R/2) = R := by ring
  rw [h2] at hG
  have hTm : (∫x in {x | R ≤ dist p x}, heatAt μ hQ t f x^2 ∂μ) ≤ T := by
    exact setIntegral_mono_set ((Lp.memLp _).integrable_sq.integrableOn)
      (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall fun x hx => by
        change R/2 ≤ dist p x
        exact (by linarith : R/2 ≤ R).trans hx)
  have hT : 0 ≤ T := integral_nonneg fun x => sq_nonneg _
  have hR2 : 1 ≤ R^2 := by nlinarith
  have hdiv : 2/R^2 ≤ 2 := (div_le_iff₀ (sq_pos_of_pos hRp)).mpr (by linarith)
  have hdiv2 : 16/(R/2)^2 ≤ 64 := (div_le_iff₀ (sq_pos_of_pos (half_pos hRp))).mpr (by nlinarith)
  have hbt := mul_le_mul hTm (show 1+2/R^2 ≤ 3 by linarith) (by positivity) hT
  have hgt := mul_le_mul_of_nonneg_right hdiv2 hT
  change _ ≤ _
  nlinarith only [hb,hG,hbt,hgt]

theorem heatSobolev_cutoff_exponential_norm_sq_le (f : Lp ℝ 2 μ) (C : ℝ≥0)
    (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂μ, f x ≤ C) (p : X)
    {r : ℝ} (hfs : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {a t s T : ℝ} (ha : 0 ≤ a) (ht : 0 < t) (hs : t ≤ s) (hT : s ≤ T)
    {R : ℝ} (hR : 1 ≤ R) :
    let u := heatSobolev μ hQ s (ht.trans_le hs) f
    let E := Real.exp (a^2/2*T+a*r)*‖f‖^2
    let G := 2*(1+1/t)*‖f‖
    ‖u-SobolevSpace.product μ hQ (radialSobolevCutoff μ hQ p (lt_of_lt_of_le zero_lt_one hR)) u 1 C‖^2 ≤
      (131*E+4*G*Real.sqrt E)*Real.exp (-a*R/4) := by
  dsimp only
  let E := Real.exp (a^2/2*T+a*r)*‖f‖^2
  let Q := ∫x in {x | R/2 ≤ dist p x}, heatAt μ hQ s f x^2 ∂μ
  let e := Real.exp (-a*R/4)
  have hQ0 : 0 ≤ Q := integral_nonneg fun x => sq_nonneg _
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have he : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by have hRp := zero_lt_one.trans_le hR; exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hRp.le) (by norm_num))
  have hEb : Real.exp (a^2/2*s+a*r)*‖f‖^2 ≤ E := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg a])
  have hQb : Q ≤ e^2*E := by
    have hv := heatAt_tail_square_integral_le μ hQ f p hfs ha (ht.trans_le hs).le (R/2)
    calc
      Q ≤ Real.exp (-a*(R/2))*(Real.exp (a^2/2*s+a*r)*‖f‖^2) := hv
      _ ≤ Real.exp (-a*(R/2))*E := mul_le_mul_of_nonneg_left hEb (Real.exp_pos _).le
      _ = e^2*E := by dsimp only [e]; rw [←Real.exp_nat_mul]; congr 2; ring
  have hQs : Real.sqrt Q ≤ e*Real.sqrt E := by
    exact (Real.sqrt_le_iff).mpr ⟨mul_nonneg he.le (Real.sqrt_nonneg _),by
      rw [mul_pow,Real.sq_sqrt hE]; exact hQb⟩
  have hQe : Q ≤ e*E := hQb.trans (mul_le_mul_of_nonneg_right (by nlinarith only [he1,he] : e^2 ≤ e) hE)
  have hG : ‖heatGenerator μ hQ s (ht.trans_le hs) f‖ ≤ 2*(1+1/t)*‖f‖ := by
    have hb := (heatGeneratorAt μ hQ s).le_of_opNorm_le
      (heatGeneratorAt_norm_le_of_ge μ hQ t ht s hs) f
    simpa only [heatGeneratorAt_of_pos μ hQ s (ht.trans_le hs)] using hb
  have hb := heatSobolev_cutoff_norm_sq_le μ hQ f C hf0 hfC p (ht.trans_le hs) hR
  have hh : ‖heatGenerator μ hQ s (ht.trans_le hs) f‖*Real.sqrt Q ≤
      (2*(1+1/t)*‖f‖)*(e*Real.sqrt E) :=
    mul_le_mul hG hQs (Real.sqrt_nonneg _) (by positivity)
  change _ ≤ (131*E+4*(2*(1+1/t)*‖f‖)*Real.sqrt E)*e
  nlinarith only [hb,hQe,hh]


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
  [SigmaFinite μ] (hQ : QuadraticCheegerEnergy μ)

omit [SigmaFinite μ] in
theorem heatSobolev_norm_uniform (f : Lp ℝ 2 μ) {t s : ℝ} (ht : 0 < t) (hs : t ≤ s) :
    ‖heatSobolev μ hQ s (ht.trans_le hs) f‖ ≤ Real.sqrt (1+1/(2*t))*‖f‖ := by
  apply (heatSobolev_norm_bound μ hQ s (ht.trans_le hs) f).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.sqrt_le_sqrt
  have hi := one_div_le_one_div_of_le (by positivity : 0 < 2*t) (by linarith : 2*t ≤ 2*s)
  linarith

theorem heat_radial_mass_defect_uniform (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ)
    (hfm : ∫x, f x ∂μ = 1) {r : ℝ} (hfs : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {a T : ℝ} (ha : 0 ≤ a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, 0 ≤ s → s ≤ T → ∀ R, 0 < R →
      let m := ∫x, radialCutoff p R x*heatAt μ hQ s f x ∂μ
      0 ≤ m ∧ m ≤ 1 ∧ 1-m ≤ M*Real.exp (-a*R) := by
  let M := Real.exp ((2*a+(B+1))^2/2*T+(2*a+(B+1))*r)*‖f‖^2+
    (∫x, Real.exp (-(B+1)*dist p x) ∂μ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M,hM,?_⟩
  intro s hs hT R hR
  have hm := heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi hs
  rw [hfm] at hm
  have hd := radialCutoff_mass_defect μ p hR (heatAt_integrable μ hQ s f hfi)
    ((Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ s f hf0)) hm
  refine ⟨hd.1,hd.2.1,hd.2.2.trans ?_⟩
  have ht := heatAt_tail_moment_integral_le μ hQ p hA hB hvol f hf0 hfs 0 ha hs hT R
  simpa only [Nat.mul_zero,Nat.zero_mul,Nat.cast_zero,add_zero,pow_zero,one_mul,M,mul_comm] using ht

theorem heat_normalized_cutoff_exponential (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (C : ℝ≥0) (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂μ, f x ≤ C)
    (hfi : Integrable f μ) (hfm : ∫x, f x ∂μ = 1)
    {r : ℝ} (hfs : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {a t T : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    ∃ D R₀ : ℝ, 0 ≤ D ∧ 1 ≤ R₀ ∧ ∀ s (hs : t ≤ s), s ≤ T → ∀ R (hR : 0 < R), R₀ ≤ R →
      let u := heatSobolev μ hQ s (ht.trans_le hs) f
      (1:ℝ)/2 ≤ (∫x, radialCutoff p R x*heatAt μ hQ s f x ∂μ) ∧
      ‖u-u.radialProbabilityCutoff μ hQ C p hR‖ ≤ D*Real.exp (-a*R) := by
  obtain ⟨M,hM,hMass⟩ := heat_radial_mass_defect_uniform μ hQ p hA hB hvol f hf0 hfi hfm hfs
    (a := a+1) (T := T) (by linarith)
  let E := Real.exp ((8*a)^2/2*T+(8*a)*r)*‖f‖^2
  let G := 2*(1+1/t)*‖f‖
  let L := Real.sqrt (131*E+4*G*Real.sqrt E)
  let U := Real.sqrt (1+1/(2*t))*‖f‖
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hlim : Tendsto (fun R : ℝ => M*Real.exp (-(a+1)*R)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith : -(a+1) < 0))).const_mul M
  obtain ⟨R₁,hR₁⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2)))
  refine ⟨2*L+2*M*U,max R₁ 1,by positivity,le_max_right _ _,?_⟩
  intro s hs hT R hRp0 hR
  have hR1 : 1 ≤ R := (le_max_right R₁ 1).trans hR
  have hRp : 0 < R := zero_lt_one.trans_le hR1
  have hm := hMass s (ht.trans_le hs).le hT R hRp
  have hmm : (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt μ hQ s f x ∂μ := by
    have hh := hR₁ R ((le_max_left R₁ 1).trans hR)
    linarith [hm.2.2]
  refine ⟨hmm,?_⟩
  let u := heatSobolev μ hQ s (ht.trans_le hs) f
  let q := SobolevSpace.product μ hQ (radialSobolevCutoff μ hQ p hRp) u 1 C
  let m := ∫x, radialCutoff p R x*heatAt μ hQ s f x ∂μ
  have hraw : ‖u-q‖ ≤ L*Real.exp (-a*R) := by
    have hb := heatSobolev_cutoff_exponential_norm_sq_le μ hQ f C hf0 hfC p hfs
      (a := 8*a) (by linarith) ht hs hT hR1
    have he : Real.exp (-(8*a)*R/4) = (Real.exp (-a*R))^2 := by
      rw [←Real.exp_nat_mul]; congr 1; ring
    rw [he] at hb
    have hLsq : L^2 = 131*E+4*G*Real.sqrt E := Real.sq_sqrt (by positivity)
    change ‖u-q‖^2 ≤ (131*E+4*G*Real.sqrt E)*Real.exp (-a*R)^2 at hb
    have hn : 0 ≤ L*Real.exp (-a*R) := by positivity
    nlinarith [sq_nonneg (‖u-q‖-L*Real.exp (-a*R))]
  have hnorm := norm_sub_normalized_cutoff_le u q hmm hm.2.1
  have he : Real.exp (-(a+1)*R) ≤ Real.exp (-a*R) := Real.exp_le_exp.mpr (by nlinarith)
  have hmd : 1-m ≤ M*Real.exp (-a*R) := hm.2.2.trans (mul_le_mul_of_nonneg_left he hM)
  have hu : ‖u‖ ≤ U := heatSobolev_norm_uniform μ hQ f ht hs
  have h1 := mul_le_mul (show 1+2*(1-m) ≤ 2 by dsimp [m]; linarith) hraw
    (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  have h2 := mul_le_mul (mul_le_mul_of_nonneg_left hmd (by norm_num : (0:ℝ) ≤ 2)) hu
    (norm_nonneg _) (by positivity : 0 ≤ 2*(M*Real.exp (-a*R)))
  change ‖u-m⁻¹ • q‖ ≤ (2*L+2*M*U)*Real.exp (-a*R)
  nlinarith only [hnorm,h1,h2]


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

theorem radial_probability_entropy_error (p : X) {R : ℝ} (hR : 0 < R)
    {f : X → ℝ} (hf : Measurable f) (hf0 : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ)
    (hfm : ∫x, f x ∂μ = 1) (hfe : Integrable (fun x => f x*Real.log (f x)) μ)
    (hm : (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*f x ∂μ) :
    let m := ∫x, radialCutoff p R x*f x ∂μ
    let g := fun x => m⁻¹*(radialCutoff p R x*f x)
    |(∫x, g x*Real.log (g x) ∂μ)-(∫x, f x*Real.log (f x) ∂μ)| ≤
      2*(1-m)*(∫x, |f x*Real.log (f x)| ∂μ)+4*(1-m)+
      (∫x in {x | R ≤ dist p x}, |f x*Real.log (f x)| ∂μ)+
      5*(∫x in {x | R ≤ dist p x}, f x ∂μ) := by
  dsimp only
  let χ := radialCutoff p R
  let m := ∫x, χ x*f x ∂μ
  let w := fun x => m⁻¹*χ x
  let E := fun x => f x*Real.log (f x)
  let S := {x : X | R ≤ dist p x}
  have hS : MeasurableSet S := (isClosed_le continuous_const (continuous_const.dist continuous_id)).measurableSet
  have hm0 : 0 < m := by dsimp [m,χ]; linarith
  have hmd := radialCutoff_mass_defect μ p hR hfi hf0 hfm
  have hm1 : m ≤ 1 := hmd.2.1
  have ha : 1 ≤ m⁻¹ := (one_le_inv₀ hm0).mpr hm1
  have ha2 : m⁻¹ ≤ 2 := by
    calc
      _ ≤ ((1:ℝ)/2)⁻¹ := (inv_le_inv₀ hm0 (by norm_num)).mpr hm
      _ = 2 := by norm_num
  have had : m⁻¹-1 ≤ 2*(1-m) := by
    have he := inv_mul_cancel₀ hm0.ne'
    nlinarith [mul_le_mul_of_nonneg_right ha2 (sub_nonneg.mpr hm1)]
  have hχ : Measurable χ := (radialCutoff_lipschitz p hR).continuous.measurable
  have hw : Measurable w := measurable_const.mul hχ
  have hwb (x : X) : 0 ≤ w x ∧ w x ≤ 2 := by
    refine ⟨mul_nonneg (inv_nonneg.mpr hm0.le) (radialCutoff_bounds p R x).1,?_⟩
    exact (mul_le_of_le_one_right (inv_nonneg.mpr hm0.le) (radialCutoff_bounds p R x).2).trans ha2
  have hg := density_factor_entropy_integrable μ hf hf0 hfi hfe hw 2 (Eventually.of_forall hwb)
  let H : X → ℝ := fun x => 2*(1-m)*|E x|+4*(1-m)*f x+
    S.indicator (fun x => |E x|) x+5*S.indicator f x
  have hHi : Integrable H μ := (((hfe.abs.const_mul _).add (hfi.const_mul _)).add
    (hfe.abs.indicator hS)).add ((hfi.indicator hS).const_mul 5)
  have hpoint : ∀ᵐ x ∂μ, |(w x*f x)*Real.log (w x*f x)-E x| ≤ H x := by
    filter_upwards [hf0] with x hx
    have hwx := hwb x
    have he : (w x*f x)*Real.log (w x*f x)-E x =
        (w x-1)*E x+(w x*Real.log (w x))*f x := by rw [mul_log_mul]; dsimp [E]; ring
    have hbase : |(w x*f x)*Real.log (w x*f x)-E x| ≤
        |w x-1| * |E x|+|w x*Real.log (w x)| *f x := by
      rw [he]
      refine (abs_add_le _ _).trans_eq ?_
      simp only [abs_mul,abs_of_nonneg hx]
    by_cases hxS : x ∈ S
    · have h1 : |w x-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
      have h2 : |w x*Real.log (w x)| ≤ 5 := by
        have hb := entropy_radial_abs_bound hwx.1 (b := 0) le_rfl
        simp only [zero_mul,neg_zero,Real.exp_zero] at hb
        nlinarith [sq_nonneg (w x-2)]
      have hh := add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg (E x)))
        (mul_le_mul_of_nonneg_right h2 hx)
      dsimp only [H]
      rw [indicator_of_mem hxS,indicator_of_mem hxS]
      have he0 := mul_nonneg (show 0 ≤ 2*(1-m) by linarith) (abs_nonneg (E x))
      have hf0 := mul_nonneg (show 0 ≤ 4*(1-m) by linarith) hx
      nlinarith only [hbase,hh,he0,hf0]
    · have hc : χ x = 1 := radialCutoff_eq_one p hR (le_of_lt (lt_of_not_ge hxS))
      have hwc : w x = m⁻¹ := by dsimp [w]; rw [hc,mul_one]
      have h1 : |w x-1| ≤ 2*(1-m) := by rw [hwc,abs_of_nonneg (by linarith)]; exact had
      have h2 : |w x*Real.log (w x)| ≤ 4*(1-m) := by
        rw [hwc,abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hm0.le) (Real.log_nonneg ha))]
        have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hm0)
        have hmul := mul_le_mul ha2 hl (Real.log_nonneg ha) (by norm_num : (0:ℝ) ≤ 2)
        linarith
      have hh := add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg (E x)))
        (mul_le_mul_of_nonneg_right h2 hx)
      dsimp only [H]
      rw [indicator_of_notMem hxS,indicator_of_notMem hxS]
      simp only [mul_zero,add_zero]
      exact hbase.trans hh
  have hbound := (abs_integral_le_integral_abs (f := fun x => (w x*f x)*Real.log (w x*f x)-E x) (μ := μ)).trans
    (integral_mono_ae (hg.sub hfe).abs hHi hpoint)
  rw [integral_sub hg hfe] at hbound
  have hH : (∫x, H x ∂μ) = 2*(1-m)*(∫x, |E x| ∂μ)+4*(1-m)+
      (∫x in S, |E x| ∂μ)+5*(∫x in S, f x ∂μ) := by
    dsimp only [H]
    have i1 : Integrable (fun x => 2*(1-m)*|E x|) μ := hfe.abs.const_mul _
    have i2 : Integrable (fun x => 4*(1-m)*f x) μ := hfi.const_mul _
    have i3 : Integrable (S.indicator (fun x => |E x|)) μ := hfe.abs.indicator hS
    have i4 : Integrable (fun x => 5*S.indicator f x) μ := (hfi.indicator hS).const_mul _
    rw [integral_add (f := fun x => 2*(1-m)*|E x|+4*(1-m)*f x+S.indicator (fun x => |E x|) x) (i1.add i2 |>.add i3) i4,
      integral_add (f := fun x => 2*(1-m)*|E x|+4*(1-m)*f x) (i1.add i2) i3,
      integral_add i1 i2,integral_const_mul,integral_const_mul,
      integral_const_mul,integral_indicator hS,integral_indicator hS,hfm,mul_one]
  rw [hH] at hbound
  simpa only [w,E,S,χ,mul_assoc] using hbound


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heat_entropy_tail_uniform (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) {r : ℝ} (hfs : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {a T : ℝ} (ha : 0 ≤ a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, 0 ≤ s → s ≤ T → ∀ R : ℝ,
      (∫x in {x | R ≤ dist p x}, |heatAt μ hQ s f x*Real.log (heatAt μ hQ s f x)| ∂μ) ≤
        M*Real.exp (-a*R) := by
  let c := a+B+1
  have hc : 0 ≤ c := by dsimp [c]; linarith
  let E := Real.exp (a^2/2*T+a*r)*‖f‖^2
  let P := Real.exp ((2*a+(B+3))^2/2*T+(2*a+(B+3))*r)*‖f‖^2+
    (∫x, dist p x^2*Real.exp (-(B+3)*dist p x) ∂μ)
  let I := ∫x, Real.exp (-(B+1)*dist p x) ∂μ
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hI : 0 ≤ I := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨E+c*P+I,by positivity,?_⟩
  intro s hs hT R
  let u := heatAt μ hQ s f
  let w := fun x => Real.exp (a*dist p x)*|u x*Real.log (u x)|
  let V := fun x => Real.exp (a*dist p x)*u x^2+
    c*(Real.exp (a*dist p x)*dist p x*u x)+Real.exp (-(B+1)*dist p x)
  have hi1 := heatAt_exponential_square_integrable μ hQ f p hfs ha hs
  have hi2 : Integrable (fun x => Real.exp (a*dist p x)*dist p x*u x) μ := by
    simpa only [pow_one] using heatAt_weighted_moment_integrable μ hQ p hA hB hvol f hfs 1 ha hs
  have hi3 := integrable_exp_neg_dist_of_volume μ p hA hB (by linarith : B < B+1) hvol
  have hVi : Integrable V μ := (hi1.add (hi2.const_mul c)).add hi3
  have hu0 := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ s f hf0)
  have hpoint : ∀ᵐ x ∂μ, w x ≤ V x := by
    filter_upwards [hu0] with x hx
    have hb := mul_le_mul_of_nonneg_left (entropy_radial_abs_bound hx (mul_nonneg hc (dist_nonneg (x := p) (y := x)))) (Real.exp_pos (a*dist p x)).le
    have he : Real.exp (a*dist p x)*Real.exp (-(c*dist p x)) = Real.exp (-(B+1)*dist p x) := by
      rw [←Real.exp_add]; congr 1; dsimp [c]; ring
    dsimp only [w,V,u]
    nlinarith only [hb,he]
  have hwi : Integrable w μ := hVi.mono' (by
    exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.dist continuous_id))).aestronglyMeasurable).mul
      (Real.continuous_mul_log.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).norm)
    (hpoint.mono fun x hx => by simpa only [w,Real.norm_eq_abs,abs_mul,abs_abs,abs_of_pos (Real.exp_pos _)] using hx)
  have hi1b : (∫x, Real.exp (a*dist p x)*u x^2 ∂μ) ≤ E := by
    apply (heatAt_exponential_square_integral_le μ hQ f p hfs ha hs).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg a]
  have hi2b : (∫x, Real.exp (a*dist p x)*dist p x*u x ∂μ) ≤ P := by
    have hh := heatAt_weighted_moment_integral_le μ hQ p hA hB hvol f hfs 1 ha hs
    simp only [Nat.mul_one,Nat.cast_ofNat,pow_one] at hh
    rw [show B+2+1 = B+3 by ring] at hh
    apply hh.trans
    dsimp only [P]
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (2*a+(B+3))]
  have hVb : (∫x, V x ∂μ) ≤ E+c*P+I := by
    dsimp only [V]
    rw [integral_add (f := fun x => Real.exp (a*dist p x)*u x^2+c*(Real.exp (a*dist p x)*dist p x*u x))
      (hi1.add (hi2.const_mul c)) hi3,
      integral_add hi1 (hi2.const_mul c),integral_const_mul]
    exact add_le_add (add_le_add hi1b (mul_le_mul_of_nonneg_left hi2b hc)) le_rfl
  have hwb : (∫x, w x ∂μ) ≤ E+c*P+I := (integral_mono_ae hwi hVi hpoint).trans hVb
  let S := {x : X | R ≤ dist p x}
  have hS : MeasurableSet S := (isClosed_le continuous_const (continuous_const.dist continuous_id)).measurableSet
  have hloc : (∫x in S, |u x*Real.log (u x)| ∂μ) ≤ Real.exp (-a*R)*(∫x in S, w x ∂μ) := by
    rw [←integral_const_mul]
    apply integral_mono_ae (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hfs hs).abs.integrableOn (hwi.integrableOn.const_mul _)
    filter_upwards [ae_restrict_mem hS] with x hx
    have he : 1 ≤ Real.exp (-a*R)*Real.exp (a*dist p x) := by
      rw [←Real.exp_add,Real.one_le_exp_iff]
      have hx' : R ≤ dist p x := hx
      nlinarith
    dsimp only [w]
    nlinarith only [mul_le_mul_of_nonneg_right he (abs_nonneg (u x*Real.log (u x)))]
  have hnon : ∀ x, 0 ≤ w x := fun _ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hsub := integral_mono_measure (Measure.restrict_le_self : μ.restrict S ≤ μ)
    (Eventually.of_forall hnon) hwi
  calc
    _ ≤ Real.exp (-a*R)*(∫x in S, w x ∂μ) := hloc
    _ ≤ Real.exp (-a*R)*(E+c*P+I) := mul_le_mul_of_nonneg_left (hsub.trans hwb) (Real.exp_pos _).le
    _ = _ := mul_comm _ _


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X]

theorem normalized_submeasure_wassersteinSq_le (ν σ : Measure X)
    [IsProbabilityMeasure ν] (hσ : σ ≤ ν) {a : ℝ≥0∞} (ha : 1 ≤ a)
    [IsProbabilityMeasure (a • σ)] (p : X) :
    wassersteinSq (a • σ) ν ≤
      2*(a-1)*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂σ)+
      2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂(ν-σ)) := by
  let η := a • σ
  let π := ν.map (fun x => (x,x))
  let τ := σ.map (fun x => (x,x))
  let : IsFiniteMeasure σ := isFiniteMeasure_of_le ν hσ
  have hd : Measurable (fun x : X => (x,x)) := measurable_id.prodMk measurable_id
  have hπ₁ : π.map Prod.snd = ν := by rw [Measure.map_map measurable_snd hd]; simp [Function.comp_def]
  have hτ₀ : τ.map Prod.fst = σ := by rw [Measure.map_map measurable_fst hd]; simp [Function.comp_def]
  have hτ₁ : τ.map Prod.snd = σ := by rw [Measure.map_map measurable_snd hd]; simp [Function.comp_def]
  have hη : σ ≤ η := by
    calc
      σ = (1:ℝ≥0∞) • σ := by simp
      _ ≤ a • σ := by gcongr
  have hτ : τ ≤ π := Measure.map_mono hσ hd
  obtain ⟨κ,hκ₀,hκ₁,hκ⟩ := coupling_repair hπ₁ hτ (hτ₀ ▸ hη)
  have hsub : η-σ = (a-1) • σ := by
    have he : η = (a-1) • σ+σ := by
      calc
        η = ((a-1)+1) • σ := by rw [tsub_add_cancel_of_le ha]
        _ = _ := by rw [add_smul,one_smul]
    rw [he,Measure.add_sub_cancel]
  have hm : (ν-σ) univ = (η-σ) univ := by
    rw [Measure.sub_apply MeasurableSet.univ hσ,Measure.sub_apply MeasurableSet.univ hη]
    simp only [measure_univ]
  have hc := equalMass_product_cost_le (η-σ) (ν-σ) hm p
  have hκ' : κ = ((η-σ) univ)⁻¹ • (η-σ).prod (ν-σ) := by simpa only [hτ₀,hτ₁] using hκ
  have hτc : transportCost τ = 0 := by
    unfold transportCost
    rw [lintegral_map (by fun_prop) hd]
    simp only [dist_self,ENNReal.ofReal_zero,zero_pow (by omega : (2:ℕ) ≠ 0),lintegral_zero]
  calc
    _ ≤ transportCost (τ+κ) := wassersteinSq_le_cost hκ₀ hκ₁
    _ = transportCost κ := by rw [transportCost_add,hτc,zero_add]
    _ ≤ 2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂(η-σ))+
        2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂(ν-σ)) := by rw [hκ']; exact hc
    _ = _ := by rw [hsub,lintegral_smul_measure]; simp only [smul_eq_mul]; ring


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
theorem integral_realDensity {f g : X → ℝ} (hf : Measurable f)
    (hfn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) = ∫x, f x*g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hfn] with x hx
  simp only [ENNReal.toReal_ofReal hx,smul_eq_mul]

theorem bounded_density_potential_integral_tendsto (p : X) (R M A : ℝ)
    {fs : ℕ → X → ℝ} {f : X → ℝ} {gs : ℕ → X → ℝ} {g : X → ℝ}
    (hfm : ∀ i, Measurable (fs i)) (hfn : ∀ i x, 0 ≤ fs i x ∧ fs i x ≤ M)
    (hfs : ∀ i x, fs i x ≠ 0 → x ∈ closedBall p R)
    (hgm : ∀ i, Measurable (gs i)) (hgb : ∀ i x, |gs i x| ≤ A)
    (hfl : ∀ᵐ x ∂μ, Tendsto (fun i => fs i x) atTop (𝓝 (f x)))
    (hgl : ∀ᵐ x ∂μ, Tendsto (fun i => gs i x) atTop (𝓝 (g x))) :
    Tendsto (fun i => ∫x, fs i x*gs i x ∂μ) atTop (𝓝 (∫x, f x*g x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence ((closedBall p R).indicator (fun _ => M*A))
  · intro i
    exact ((hfm i).mul (hgm i)).aestronglyMeasurable
  · exact (integrableOn_const (isCompact_closedBall p R).measure_lt_top.ne).integrable_indicator measurableSet_closedBall
  · intro i
    filter_upwards with x
    by_cases hx : x ∈ closedBall p R
    · rw [indicator_of_mem hx,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hfn i x).1]
      exact mul_le_mul (hfn i x).2 (hgb i x) (abs_nonneg _) ((hfn i x).1.trans (hfn i x).2)
    · have hz : fs i x = 0 := by
        by_contra h
        exact hx (hfs i x h)
      simp only [indicator_of_notMem hx,hz,zero_mul,norm_zero,le_refl]
  · filter_upwards [hfl,hgl] with x hx hy
    exact hx.mul hy


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X]

theorem normalized_submeasure_wassersteinSq_real_le (ν σ : Measure X)
    [IsProbabilityMeasure ν] (hσ : σ ≤ ν) {a : ℝ} (ha : 1 ≤ a)
    [IsProbabilityMeasure (ENNReal.ofReal a • σ)] (p : X)
    (hi : Integrable (fun x => dist p x^2) ν) :
    (wassersteinSq (ENNReal.ofReal a • σ) ν).toReal ≤
      2*(a-1)*(∫x, dist p x^2 ∂σ)+2*(∫x, dist p x^2 ∂(ν-σ)) := by
  have hiσ := hi.mono_measure hσ
  have hiτ := hi.mono_measure (Measure.sub_le : ν-σ ≤ ν)
  have hreal (η : Measure X) (hη : Integrable (fun x => dist p x^2) η) :
      (∫⁻x, ENNReal.ofReal (dist p x)^2 ∂η) = ENNReal.ofReal (∫x, dist p x^2 ∂η) := by
    simp_rw [←ENNReal.ofReal_pow dist_nonneg]
    exact (ofReal_integral_eq_lintegral_ofReal hη (Eventually.of_forall fun _ => sq_nonneg _)).symm
  have hw := normalized_submeasure_wassersteinSq_le ν σ hσ
    (a := ENNReal.ofReal a) (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ha) p
  rw [hreal σ hiσ,hreal (ν-σ) hiτ,←ENNReal.ofReal_one,←ENNReal.ofReal_sub a (by norm_num : (0:ℝ) ≤ 1)] at hw
  have hnon1 : 0 ≤ ∫x, dist p x^2 ∂σ := integral_nonneg fun _ => sq_nonneg _
  have hnon2 : 0 ≤ ∫x, dist p x^2 ∂(ν-σ) := integral_nonneg fun _ => sq_nonneg _
  have he : (2:ℝ≥0∞)*ENNReal.ofReal (a-1)*ENNReal.ofReal (∫x, dist p x^2 ∂σ)+
      2*ENNReal.ofReal (∫x, dist p x^2 ∂(ν-σ)) =
      ENNReal.ofReal (2*(a-1)*(∫x, dist p x^2 ∂σ)+2*(∫x, dist p x^2 ∂(ν-σ))) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat]
    rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2*(a-1)),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat]
  rw [he] at hw
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hw).trans_eq (ENNReal.toReal_ofReal (by positivity))

variable [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

omit [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
theorem radial_probability_measure_transport_le (p : X) {R : ℝ} (hR : 0 < R)
    {f : X → ℝ} (hf : Measurable f) (hf0 : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ)
    (hfm : ∫x, f x ∂μ = 1) (h2 : Integrable (fun x => dist p x^2*f x) μ)
    (hm : (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*f x ∂μ) :
    let m := ∫x, radialCutoff p R x*f x ∂μ
    let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
    let η := μ.withDensity (fun x => ENNReal.ofReal (m⁻¹*(radialCutoff p R x*f x)))
    (wassersteinSq η ν).toReal ≤
      4*(1-m)*(∫x, dist p x^2*f x ∂μ)+2*(∫x in {x | R ≤ dist p x}, dist p x^2*f x ∂μ) := by
  dsimp only
  let χ := radialCutoff p R
  let m := ∫x, χ x*f x ∂μ
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let σ := μ.withDensity (fun x => ENNReal.ofReal (χ x*f x))
  let τ := μ.withDensity (fun x => ENNReal.ofReal ((1-χ x)*f x))
  have hχ : Measurable χ := (radialCutoff_lipschitz p hR).continuous.measurable
  have hm0 : 0 < m := by dsimp [m,χ]; linarith
  have hmd := radialCutoff_mass_defect μ p hR hfi hf0 hfm
  have hmi : m ≤ 1 := hmd.2.1
  have hai : 1 ≤ m⁻¹ := (one_le_inv₀ hm0).mpr hmi
  have hai2 : m⁻¹ ≤ 2 := by
    calc
      _ ≤ ((1:ℝ)/2)⁻¹ := (inv_le_inv₀ hm0 (by norm_num)).mpr hm
      _ = 2 := by norm_num
  have hσi := radialCutoff_mul_integrable μ p hR hfi
  have hσn : 0 ≤ᵐ[μ] (fun x => χ x*f x) := hf0.mono fun x hx => mul_nonneg (radialCutoff_bounds p R x).1 hx
  have hτn : 0 ≤ᵐ[μ] (fun x => (1-χ x)*f x) := hf0.mono fun x hx => mul_nonneg (sub_nonneg.mpr (radialCutoff_bounds p R x).2) hx
  let : IsProbabilityMeasure ν := by
    constructor
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ←ofReal_integral_eq_lintegral_ofReal hfi hf0,hfm,ENNReal.ofReal_one]
  have hσ : σ ≤ ν := withDensity_mono (hf0.mono fun x hx =>
    ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left hx (radialCutoff_bounds p R x).2))
  let : IsFiniteMeasure σ := isFiniteMeasure_of_le ν hσ
  have hadd : σ+τ = ν := by
    dsimp only [σ,τ,ν]
    rw [←withDensity_add_left (f := fun x => ENNReal.ofReal (χ x*f x)) (hχ.mul hf).ennreal_ofReal]
    apply withDensity_congr_ae
    filter_upwards [hσn,hτn] with x hx hy
    simp only [Pi.add_apply]
    rw [←ENNReal.ofReal_add hx hy]
    congr 1
    ring
  have hsub : ν-σ = τ := by rw [←hadd,add_comm,Measure.add_sub_cancel]
  have heta : μ.withDensity (fun x => ENNReal.ofReal (m⁻¹*(χ x*f x))) = ENNReal.ofReal m⁻¹ • σ := by
    dsimp only [σ]
    rw [←withDensity_smul _ (f := fun x => ENNReal.ofReal (χ x*f x)) (hχ.mul hf).ennreal_ofReal]
    congr 1
    funext x
    exact ENNReal.ofReal_mul (inv_nonneg.mpr hm0.le)
  let : IsProbabilityMeasure (ENNReal.ofReal m⁻¹ • σ) := by
    rw [←heta]
    constructor
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ←ofReal_integral_eq_lintegral_ofReal (hσi.const_mul m⁻¹) (hσn.mono fun x hx => mul_nonneg (inv_nonneg.mpr hm0.le) hx),
      integral_const_mul,inv_mul_cancel₀ hm0.ne',ENNReal.ofReal_one]
  have hν2 : Integrable (fun x => dist p x^2) ν := by
    change Integrable (fun x => dist p x^2) (μ.withDensity (fun x => ((f x).toNNReal : ℝ≥0∞)))
    apply (integrable_withDensity_iff_integrable_smul₀ (hf.real_toNNReal.aemeasurable)).mpr
    apply h2.congr
    filter_upwards [hf0] with x hx
    simp only [NNReal.smul_def,Real.coe_toNNReal _ hx,smul_eq_mul,mul_comm]
  have hw := normalized_submeasure_wassersteinSq_real_le ν σ hσ hai p hν2
  have hσ2 : (∫x, dist p x^2 ∂σ) ≤ ∫x, dist p x^2*f x ∂μ := by
    have hi := integral_mono_measure hσ (Eventually.of_forall fun x => sq_nonneg (dist p x)) hν2
    dsimp only [ν] at hi
    rw [integral_realDensity μ hf hf0] at hi
    simpa only [mul_comm] using hi
  have hτ2 : (∫x, dist p x^2 ∂τ) ≤ ∫x in {x | R ≤ dist p x}, dist p x^2*f x ∂μ := by
    dsimp only [τ]
    rw [integral_realDensity μ (f := fun x => (1-χ x)*f x) ((measurable_const.sub hχ).mul hf) hτn]
    have hi : Integrable (fun x => (1-χ x)*f x*dist p x^2) μ := by
      apply ((h2.sub (radialCutoff_mul_integrable μ p hR h2))).congr
      filter_upwards with x
      dsimp only [Pi.sub_apply,χ]
      ring
    have hS : MeasurableSet {x : X | R ≤ dist p x} := (isClosed_le continuous_const (continuous_const.dist continuous_id)).measurableSet
    rw [←integral_indicator hS]
    apply integral_mono_ae hi (h2.indicator hS)
    filter_upwards [hf0] with x hx
    by_cases hh : x ∈ {x : X | R ≤ dist p x}
    · rw [indicator_of_mem hh]
      have h0 := mul_nonneg (sq_nonneg (dist p x)) hx
      have hc := mul_le_of_le_one_left h0 (show 1-χ x ≤ 1 by have := (radialCutoff_bounds p R x).1; dsimp [χ]; linarith)
      nlinarith only [hc]
    · rw [indicator_of_notMem hh]
      have hc : χ x = 1 := radialCutoff_eq_one p hR (le_of_lt (lt_of_not_ge hh))
      simp only [hc,sub_self,zero_mul,le_refl]
  rw [hsub] at hw
  have had : m⁻¹-1 ≤ 2*(1-m) := by
    have he := inv_mul_cancel₀ hm0.ne'
    nlinarith [mul_le_mul_of_nonneg_right hai2 (sub_nonneg.mpr hmi)]
  have hσpos : 0 ≤ ∫x, dist p x^2 ∂σ := integral_nonneg fun _ => sq_nonneg _
  have hstep := mul_le_mul (mul_le_mul_of_nonneg_left had (by norm_num : (0:ℝ) ≤ 2)) hσ2 hσpos (by linarith : 0 ≤ 2*(2*(1-m)))
  change (wassersteinSq (μ.withDensity (fun x => ENNReal.ofReal (m⁻¹*(χ x*f x)))) ν).toReal ≤ _
  rw [heta]
  nlinarith only [hw,hstep,hτ2]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

noncomputable def radialHeatMeasure (p : X) (R s : ℝ) (f : Lp ℝ 2 μ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal
    ((∫y, radialCutoff p R y*heatAt μ hQ s f y ∂μ)⁻¹*(radialCutoff p R x*heatAt μ hQ s f x)))

theorem heat_moment_tail_uniform (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) {r : ℝ} (hfs : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (k : ℕ) {a T : ℝ} (ha : 0 ≤ a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, 0 ≤ s → s ≤ T → ∀ R,
      (∫x in {x | R ≤ dist p x}, dist p x^k*heatAt μ hQ s f x ∂μ) ≤ M*Real.exp (-a*R) := by
  let M := Real.exp ((2*a+(B+(2*k:ℕ)+1))^2/2*T+(2*a+(B+(2*k:ℕ)+1))*r)*‖f‖^2+
    (∫x, dist p x^(2*k)*Real.exp (-(B+(2*k:ℕ)+1)*dist p x) ∂μ)
  refine ⟨M,?_,?_⟩
  · dsimp only [M]
    positivity
  · intro s hs hT R
    simpa only [M,mul_comm] using heatAt_tail_moment_integral_le μ hQ p hA hB hvol f hf0 hfs k ha hs hT R

variable [SigmaFinite μ]

theorem radialHeatMeasure_entropy_exponential (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) (hfm : ∫x, f x ∂μ = 1)
    {r : ℝ} (hfs : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a T : ℝ} (ha : 0 ≤ a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s, 0 ≤ s → s ≤ T → ∀ R, 0 < R →
      (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt μ hQ s f x ∂μ →
      |boltzmannEntropy μ (radialHeatMeasure μ hQ p R s f)-boltzmannEntropy μ (heatMeasure μ hQ s f)| ≤ D*Real.exp (-a*R) := by
  obtain ⟨M,hM,hMass⟩ := heat_radial_mass_defect_uniform μ hQ p hA hB hvol f hf0 hfi hfm hfs (T := T) ha
  obtain ⟨E,hE,hEnt⟩ := heat_entropy_tail_uniform μ hQ p hA hB hvol f hf0 hfs (T := T) ha
  obtain ⟨P,hP,hTail⟩ := heat_moment_tail_uniform μ hQ p hA hB hvol f hf0 hfs 0 (T := T) ha
  refine ⟨2*M*E+4*M+E+5*P,by positivity,?_⟩
  intro s hs hT R hR hm
  let u := heatAt μ hQ s f
  let m := ∫x, radialCutoff p R x*u x ∂μ
  have hu0 := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ s f hf0)
  have hui := heatAt_integrable μ hQ s f hfi
  have hum : ∫x, u x ∂μ = 1 := (heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi hs).trans hfm
  have hue := heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hfs hs
  have hcut := radial_probability_entropy_error μ p hR (Lp.stronglyMeasurable u).measurable hu0 hui hum hue hm
  have hmd := hMass s hs hT R hR
  have hEe : (∫x, |u x*Real.log (u x)| ∂μ) ≤ E := by
    simpa only [mul_zero,Real.exp_zero,mul_one,Set.ofPred_true,Measure.restrict_univ,dist_nonneg,u]
      using hEnt s hs hT 0
  have htail := hEnt s hs hT R
  have hmass : (∫x in {x | R ≤ dist p x}, u x ∂μ) ≤ P*Real.exp (-a*R) := by
    simpa only [pow_zero,one_mul] using hTail s hs hT R
  have hg0 : 0 ≤ᵐ[μ] fun x => m⁻¹*(radialCutoff p R x*u x) := by
    filter_upwards [hu0] with x hx
    exact mul_nonneg (inv_nonneg.mpr hmd.1) (mul_nonneg (radialCutoff_bounds p R x).1 hx)
  have hent : boltzmannEntropy μ (radialHeatMeasure μ hQ p R s f) =
      ∫x, (m⁻¹*(radialCutoff p R x*u x))*Real.log (m⁻¹*(radialCutoff p R x*u x)) ∂μ := by
    apply realDensity_entropy μ (f := fun x => m⁻¹*(radialCutoff p R x*u x))
    · exact (((radialCutoff_lipschitz p hR).continuous.measurable.mul (Lp.stronglyMeasurable u).measurable).const_mul m⁻¹)
    · exact hg0
  rw [hent,boltzmannEntropy_heatMeasure_eq μ hQ f hf0]
  have hprod := mul_le_mul hmd.2.2 hEe (integral_nonneg fun _ => abs_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)
  have hm4 := mul_le_mul_of_nonneg_left hmd.2.2 (by norm_num : (0:ℝ) ≤ 4)
  dsimp only at hcut
  change |(∫x, (m⁻¹*(radialCutoff p R x*u x))*Real.log (m⁻¹*(radialCutoff p R x*u x)) ∂μ)-
    (∫x, u x*Real.log (u x) ∂μ)| ≤ _
  nlinarith only [hcut,hprod,hm4,htail,hmass]

variable [SeparableSpace X]

theorem radialHeatMeasure_transport_exponential (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) (hfm : ∫x, f x ∂μ = 1)
    {r : ℝ} (hfs : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a T : ℝ} (ha : 0 ≤ a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s, 0 ≤ s → s ≤ T → ∀ R, 0 < R →
      (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt μ hQ s f x ∂μ →
      (wassersteinSq (radialHeatMeasure μ hQ p R s f) (heatMeasure μ hQ s f)).toReal ≤ D*Real.exp (-a*R) := by
  obtain ⟨M,hM,hMass⟩ := heat_radial_mass_defect_uniform μ hQ p hA hB hvol f hf0 hfi hfm hfs (T := T) ha
  obtain ⟨P,hP,hTail⟩ := heat_moment_tail_uniform μ hQ p hA hB hvol f hf0 hfs 2 (T := T) ha
  refine ⟨4*M*P+2*P,by positivity,?_⟩
  intro s hs hT R hR hm
  let u := heatAt μ hQ s f
  have hu0 := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ s f hf0)
  have hui := heatAt_integrable μ hQ s f hfi
  have hum : ∫x, u x ∂μ = 1 := (heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi hs).trans hfm
  have hu2 := heatAt_dist_pow_integrable μ hQ p hA hB hvol f hfs 2 hs
  have hc := radial_probability_measure_transport_le μ p hR (Lp.stronglyMeasurable u).measurable hu0 hui hum hu2 hm
  have hmd := hMass s hs hT R hR
  have hp2 : (∫x, dist p x^2*u x ∂μ) ≤ P := by
    simpa only [mul_zero,Real.exp_zero,mul_one,Set.ofPred_true,Measure.restrict_univ,dist_nonneg,u] using hTail s hs hT 0
  have htail := hTail s hs hT R
  have hprod := mul_le_mul hmd.2.2 hp2
    (integral_nonneg_of_ae (hu0.mono fun x hx => mul_nonneg (sq_nonneg _) hx)) (mul_nonneg hM (Real.exp_pos _).le)
  change (wassersteinSq (radialHeatMeasure μ hQ p R s f) (heatMeasure μ hQ s f)).toReal ≤ _ at hc
  nlinarith only [hc,hprod,htail]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

noncomputable def radialHeatSobolev (p : X) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (f : Lp ℝ 2 μ) (C : ℝ≥0) : SobolevSpace μ hQ :=
  (heatSobolev μ hQ s hs f).radialProbabilityCutoff μ hQ C p hR

theorem radialHeatSobolev_measure (p : X) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (f : Lp ℝ 2 μ) (C : ℝ≥0) (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂μ, f x ≤ C) :
    radialHeatMeasure μ hQ p R s f =
      μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ (radialHeatSobolev μ hQ p hR hs f C) x)) := by
  have hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (heatSobolev μ hQ s hs f) x| ≤ C := by
    rw [heatSobolev_toLp]
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ s f hf0),heatAt_le_const μ hQ s C.coe_nonneg f hfC] with x hl hu
    rw [abs_of_nonneg hl]; exact hu
  have he := SobolevSpace.radialProbabilityCutoff_coe μ hQ (heatSobolev μ hQ s hs f) C hb p hR
  simp only [heatSobolev_toLp] at he
  exact withDensity_congr_ae (he.symm.fun_comp ENNReal.ofReal)

variable [SigmaFinite μ]

theorem radialHeatSobolev_data (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (C : ℝ≥0) (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂μ, f x ≤ C)
    (hfi : Integrable f μ) (hfm : ∫x, f x ∂μ = 1)
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hm : (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt μ hQ s f x ∂μ) :
    let v := radialHeatSobolev μ hQ p hR hs f C
    (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ v x ∧ SobolevSpace.toLp μ hQ v x ≤ 2*C) ∧
    (∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ v x ≠ 0 → dist p x ≤ 2*R) ∧
    Integrable (SobolevSpace.toLp μ hQ v) μ ∧ (∫x, SobolevSpace.toLp μ hQ v x ∂μ) = 1 := by
  apply SobolevSpace.radialProbabilityCutoff_data μ hQ (heatSobolev μ hQ s hs f) C
  · rw [heatSobolev_toLp]
    exact ((Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ s f hf0)).and (heatAt_le_const μ hQ s C.coe_nonneg f hfC)
  · rw [heatSobolev_toLp]; exact heatAt_integrable μ hQ s f hfi
  · rw [heatSobolev_toLp]
    exact (heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi hs.le).trans hfm
  · exact hm

theorem radialHeatMeasure_data (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (C : ℝ≥0) (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂μ, f x ≤ C)
    (hfi : Integrable f μ) (hfm : ∫x, f x ∂μ = 1)
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hm : (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt μ hQ s f x ∂μ) :
    IsProbabilityMeasure (radialHeatMeasure μ hQ p R s f) ∧
    radialHeatMeasure μ hQ p R s f ≤ ENNReal.ofReal (2*C) • μ ∧
    (∀ᵐ x ∂radialHeatMeasure μ hQ p R s f, dist x p ≤ 2*R) := by
  let v := radialHeatSobolev μ hQ p hR hs f C
  have hd := radialHeatSobolev_data μ hQ p hA hB hvol f C hf0 hfC hfi hfm hR hs hm
  have he := radialHeatSobolev_measure μ hQ p hR hs f C hf0 hfC
  rw [he]
  refine ⟨?_,?_,?_⟩
  · constructor
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ←ofReal_integral_eq_lintegral_ofReal hd.2.2.1 (hd.1.mono fun _ hx => hx.1),hd.2.2.2,ENNReal.ofReal_one]
  · calc
      _ ≤ μ.withDensity (fun _ => ENNReal.ofReal (2*C)) :=
        withDensity_mono (hd.1.mono fun x hx => ENNReal.ofReal_le_ofReal hx.2)
      _ = _ := withDensity_const _
  · apply (ae_withDensity_iff (Lp.stronglyMeasurable (SobolevSpace.toLp μ hQ v)).measurable.ennreal_ofReal).mpr
    filter_upwards [hd.2.1] with x hx hn
    have hh : SobolevSpace.toLp μ hQ v x ≠ 0 := by
      intro hz
      apply hn
      rw [hz,ENNReal.ofReal_zero]
    simpa only [dist_comm] using hx hh

omit [BorelSpace X] [ProperSpace X] in
theorem finiteSecondMoment_of_ae_dist_le (ν : Measure X) [IsProbabilityMeasure ν]
    (p : X) {R : ℝ} (h : ∀ᵐ x ∂ν, dist x p ≤ R) : FiniteSecondMoment ν := by
  refine ⟨p,?_⟩
  have hb : (∫⁻x, ENNReal.ofReal (dist x p)^2 ∂ν) ≤ ∫⁻x, ENNReal.ofReal R^2 ∂ν := by
    apply lintegral_mono_ae
    filter_upwards [h] with x hx
    exact pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal hx) 2
  apply lt_of_le_of_lt hb
  simp only [lintegral_const,measure_univ,mul_one]
  exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top


end

 
section
 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X)
 theorem IsRelaxedSlope.quantitative_compact_bounded_recovery {f G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ f G)
    (M : ℝ≥0) (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ M)
    (p : X) {r : ℝ} (hfS : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) :
    ∃ (us : ℕ → Lp ℝ 2 μ) (gs : ℕ → X → ℝ) (Gs : ℕ → Lp ℝ 2 μ) (H : Lp ℝ 2 μ),
      (∀ i, ∃ C : ℝ≥0, LipschitzWith C (gs i)) ∧
      (∀ i, ⇑(us i) =ᵐ[μ] gs i) ∧ (∀ i, IsSlopeMajorant μ (gs i) (Gs i)) ∧
      Tendsto us atTop (𝓝 f) ∧ Tendsto Gs atTop (𝓝 H) ∧ ‖H‖ ≤ ‖G‖ ∧
      (∀ i x, 0 ≤ gs i x ∧ gs i x ≤ M) ∧ (∀ i x, gs i x ≠ 0 → dist p x ≤ 2*(max r 0+1)) := by
  obtain ⟨us,gs,Gs,hl,ha,hm,hu,hlim,hb⟩ := hG.bounded_recovery μ M hf
  let R := max r 0+1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right r 0]
  have hrR : r < R := by dsimp [R]; linarith [le_max_left r 0]
  let θ := radialCutoff p R
  let C : ℝ≥0 := ⟨R⁻¹,inv_nonneg.mpr hR.le⟩
  have hθ : LipschitzWith C θ := radialCutoff_lipschitz p hR
  have hθb (x : X) : 0 ≤ θ x ∧ θ x ≤ 1 := radialCutoff_bounds p R x
  let Θ := boundedMultiplier μ θ hθ.continuous.measurable 1 (fun x => by rw [abs_of_nonneg (hθb x).1]; exact (hθb x).2)
  have hΘ : ⇑Θ =ᵐ[μ] θ := boundedMultiplier_coe μ _ _ _ _
  have hfix : lpMultiplier μ Θ f = f := by
    apply Lp.ext
    filter_upwards [lpMultiplier_coe μ Θ f,hΘ,hfS] with x hx hθx hs
    rw [hx,hθx]
    by_cases hx0 : f x = 0
    · simp [hx0]
    · rw [show θ x = 1 from radialCutoff_eq_one p hR ((hs hx0).trans hrR.le),one_mul]
  let ws := fun i => lpMultiplier μ Θ (us i)
  let ks := fun i x => θ x*gs i x
  let Ws := fun i => lpMultiplier μ Θ (Gs i)+(C:ℝ) • lpAbs μ (us i-f)
  have hla (i : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (ks i) := by
    obtain ⟨D,hD⟩ := hl i
    exact lipschitz_mul_compact_cutoff hθ hD (radialCutoff_hasCompactSupport p hR)
      (fun x => by rw [abs_of_nonneg (hθb x).1]; exact (hθb x).2)
  have hae (i : ℕ) : ⇑(ws i) =ᵐ[μ] ks i := by
    filter_upwards [lpMultiplier_coe μ Θ (us i),hΘ,ha i] with x hx hθx hu'
    exact hx.trans (by rw [hθx,hu'])
  have hmaj (i : ℕ) : IsSlopeMajorant μ (ks i) (Ws i) := by
    obtain ⟨D,hD⟩ := hl i
    filter_upwards [Lp.coeFn_add (lpMultiplier μ Θ (Gs i)) ((C:ℝ) • lpAbs μ (us i-f)),
      lpMultiplier_coe μ Θ (Gs i),Lp.coeFn_smul (C:ℝ) (lpAbs μ (us i-f)),
      lpAbs_coe μ (us i-f),Lp.coeFn_sub (us i) f,hΘ,ha i,hm i,hfS]
      with x hadd hmul hsm habs hsub hθx hu' hGx hfSx
    have he : Ws i x = θ x*Gs i x+(C:ℝ)*|gs i x-f x| := by
      dsimp only [Ws]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply] at hadd hsm hsub
      rw [hadd,hmul,hsm,habs,hsub,hθx,hu']
    rw [he]
    refine ⟨add_nonneg (mul_nonneg (hθb x).1 hGx.1) (mul_nonneg C.coe_nonneg (abs_nonneg _)),?_⟩
    have hp := localSlope_mul_le hθ.continuous.continuousAt
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hD x))
    change localSlope (fun y => θ y*gs i y) x ≤ _ at hp ⊢
    apply hp.trans
    rw [abs_of_nonneg (hθb x).1,ENNReal.ofReal_add
      (mul_nonneg (hθb x).1 hGx.1) (mul_nonneg C.coe_nonneg (abs_nonneg _)),
      ENNReal.ofReal_mul (hθb x).1,ENNReal.ofReal_mul C.coe_nonneg]
    apply add_le_add (mul_le_mul' le_rfl hGx.2)
    by_cases hxR : dist p x < R
    · rw [radialCutoff_slope_zero p hR hxR,mul_zero]
      exact bot_le
    · have hfx : f x = 0 := by
        by_contra hf0
        exact hxR ((hfSx hf0).trans_lt hrR)
      rw [hfx,sub_zero,mul_comm (ENNReal.ofReal (C:ℝ))]
      apply mul_le_mul' le_rfl
      simpa only [ENNReal.ofReal_coe_nnreal] using localSlope_le_of_lipschitz hθ x
  refine ⟨ws,ks,Ws,lpMultiplier μ Θ G,hla,hae,hmaj,?_,?_,?_,?_,?_⟩
  · simpa only [ws,Function.comp_def,hfix] using (lpMultiplier μ Θ).continuous.continuousAt.tendsto.comp hu
  · have hz := ((lpAbs_continuous μ).continuousAt.tendsto.comp (hu.sub_const f)).const_smul (C:ℝ)
    simpa only [Ws,Function.comp_def,sub_self,lpAbs_zero,smul_zero,add_zero] using
      ((lpMultiplier μ Θ).continuous.continuousAt.tendsto.comp hlim).add hz
  · have hbound := boundedMultiplier_norm_le μ θ hθ.continuous.measurable 1
      (fun x => by rw [abs_of_nonneg (hθb x).1]; exact (hθb x).2)
    exact (Lp.norm_smul_le Θ G).trans (by simpa using mul_le_mul_of_nonneg_right hbound (norm_nonneg G))
  · intro i x
    exact ⟨mul_nonneg (hθb x).1 (hb i x).1,
      (mul_le_mul_of_nonneg_right (hθb x).2 (hb i x).1).trans (by simpa using (hb i x).2)⟩
  · intro i x hx
    by_contra h
    apply hx
    dsimp only [ks]
    rw [show θ x = 0 from radialCutoff_eq_zero p hR (le_of_not_ge h),zero_mul]

end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.quantitative_strong_compact_bounded_recovery (f : SobolevSpace μ hQ)
    (M : ℝ≥0) (hf : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ f x ∧ SobolevSpace.toLp μ hQ f x ≤ M)
    (p : X) {r : ℝ} (hs : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x ≠ 0 → dist p x ≤ r) :
    ∃ (fs : ℕ → SobolevSpace μ hQ) (gs : ℕ → X → ℝ),
      Tendsto fs atTop (𝓝 f) ∧
      (∀ i, ∃ C : ℝ≥0, LipschitzWith C (gs i)) ∧
      (∀ i, SobolevSpace.toLp μ hQ (fs i) =ᵐ[μ] gs i) ∧
      (∀ i x, 0 ≤ gs i x ∧ gs i x ≤ M) ∧
      (∀ i x, gs i x ≠ 0 → dist p x ≤ 2*(max r 0+1)) := by
  obtain ⟨us,gs,Gs,H,hl,ha,hm,hu,hlim,hH,hb,hs⟩ :=
    (SobolevSpace.minimalSlope_isRelaxed μ hQ f).quantitative_compact_bounded_recovery μ M hf p hs
  have he (i : ℕ) : energyLp μ (us i) ≤ ENNReal.ofReal (‖Gs i‖^2/2) := by
    obtain ⟨C,hC⟩ := hl i
    exact energyLp_le_of_lipschitz_majorant μ hC (ha i) (hm i)
  let fs (i : ℕ) : SobolevSpace μ hQ := ⟨us i,ne_top_of_le_ne_top ENNReal.ofReal_ne_top (he i)⟩
  have heb (i : ℕ) : SobolevSpace.energy μ hQ (fs i) ≤ ‖Gs i‖^2/2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (he i)
  have hHb : ‖H‖^2/2 ≤ SobolevSpace.energy μ hQ f := by
    have hh := sq_le_sq₀ (norm_nonneg H) (norm_nonneg (SobolevSpace.minimalSlope μ hQ f)) |>.mpr hH
    rw [SobolevSpace.minimalSlope_norm_sq] at hh
    linarith
  refine ⟨fs,gs,?_,hl,ha,hb,hs⟩
  apply SobolevSpace.tendsto_of_toLp_tendsto_energy_le μ hQ hu
  intro ε hε
  have hh := ((hlim.norm.pow 2).div_const 2).eventually
    (gt_mem_nhds (lt_add_of_pos_right (‖H‖^2/2) hε))
  filter_upwards [hh] with i hi
  exact (heb i).trans (hi.le.trans (by linarith : ‖H‖^2/2+ε ≤ SobolevSpace.energy μ hQ f+ε))


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable def squareCoreRoot (ε r : ℝ) : ℝ := sqrtShift ε (max r 0)
noncomputable def squareCoreContraction (ε r : ℝ) : ℝ := (squareCoreRoot ε r)^2

 theorem squareCoreRoot_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith ⟨(2*Real.sqrt ε)⁻¹,by positivity⟩ (squareCoreRoot ε) := by
  have hm : LipschitzWith 1 (fun r : ℝ => max r 0) := (LipschitzWith.id).max_const 0
  apply LipschitzWith.of_dist_le_mul
  intro a b
  exact ((sqrtShift_lipschitz hε).dist_le_mul (max a 0) (max b 0)).trans
    (mul_le_mul_of_nonneg_left (by simpa only [NNReal.coe_one,one_mul] using hm.dist_le_mul a b)
      (show 0 ≤ (2*Real.sqrt ε)⁻¹ by positivity))

 theorem squareCoreRoot_zero (ε : ℝ) : squareCoreRoot ε 0 = 0 := by
  simp [squareCoreRoot,sqrtShift_zero]
 theorem squareCoreContraction_zero (ε : ℝ) : squareCoreContraction ε 0 = 0 := by
  simp [squareCoreContraction,squareCoreRoot_zero]
 theorem squareCoreRoot_nonneg {ε : ℝ} (hε : 0 < ε) (r : ℝ) : 0 ≤ squareCoreRoot ε r :=
  (sqrtShift_nonneg_le hε (le_max_right r 0)).1
 theorem squareCoreContraction_bounds {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ squareCoreContraction ε r ∧ squareCoreContraction ε r ≤ r := by
  have hh := sqrtShift_nonneg_le hε hr
  simp only [squareCoreContraction,squareCoreRoot,max_eq_left hr]
  refine ⟨sq_nonneg _,?_⟩
  nlinarith [Real.sq_sqrt hr,Real.sqrt_nonneg r]

 theorem squareCoreContraction_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 1 (squareCoreContraction ε) := by
  have hi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
      0 ≤ (sqrtShift ε b)^2-(sqrtShift ε a)^2 ∧
      (sqrtShift ε b)^2-(sqrtShift ε a)^2 ≤ b-a := by
    have hb := ha.trans hab
    rw [sqrtShift_of_nonneg hε ha,sqrtShift_of_nonneg hε hb]
    have hsa := Real.sqrt_le_sqrt (show ε ≤ a+ε by linarith)
    have hsab : Real.sqrt (a+ε) ≤ Real.sqrt (b+ε) := Real.sqrt_le_sqrt (by linarith)
    have hsqA := Real.sq_sqrt (add_nonneg ha hε.le)
    have hsqB := Real.sq_sqrt (add_nonneg hb hε.le)
    constructor
    · nlinarith [Real.sqrt_nonneg ε]
    · nlinarith [Real.sqrt_nonneg ε,mul_nonneg (Real.sqrt_nonneg ε) (sub_nonneg.mpr hsab)]
  have hLip : LipschitzWith 1 (fun r : ℝ => (sqrtShift ε (max r 0))^2) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have hh := ((LipschitzWith.id : LipschitzWith (1:ℝ≥0) (id : ℝ → ℝ)).max_const 0).dist_le_mul a b
    simp only [NNReal.coe_one,one_mul,Real.dist_eq,id_eq] at hh ⊢
    rcases le_total (max a 0) (max b 0) with hab | hba
    · have hs := hi (le_max_right a 0) hab
      rw [abs_of_nonpos (by linarith : (sqrtShift ε (max a 0))^2-(sqrtShift ε (max b 0))^2 ≤ 0)]
      rw [abs_of_nonpos (sub_nonpos.mpr hab)] at hh
      linarith
    · have hs := hi (le_max_right b 0) hba
      rw [abs_of_nonneg hs.1]
      rw [abs_of_nonneg (sub_nonneg.mpr hba)] at hh
      exact hs.2.trans hh
  exact hLip

 theorem squareCoreContraction_tendsto {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun k => squareCoreContraction (entropyScale k) r) atTop (𝓝 r) := by
  have he := entropyScale_tendsto.mono_right nhdsWithin_le_nhds
  have hs := (((tendsto_const_nhds (x := r)).add he).sqrt.sub he.sqrt).pow 2
  simp only [add_zero,Real.sqrt_zero,sub_zero,Real.sq_sqrt hr] at hs
  apply hs.congr
  intro k
  simp only [squareCoreContraction,squareCoreRoot,max_eq_left hr,
    sqrtShift_of_nonneg (entropyScale_pos k) hr]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.squareCoreContraction_tendsto (f : SobolevSpace μ hQ)
    (hf : 0 ≤ SobolevSpace.toLp μ hQ f) :
    Tendsto (fun k => SobolevSpace.compContraction μ hQ
      (squareCoreContraction_lipschitz (entropyScale_pos k))
      (squareCoreContraction_zero (entropyScale k)) f) atTop (𝓝 f) := by
  let g (k : ℕ) := SobolevSpace.compContraction μ hQ
    (squareCoreContraction_lipschitz (entropyScale_pos k))
    (squareCoreContraction_zero (entropyScale k)) f
  have hco (k : ℕ) : SobolevSpace.toLp μ hQ (g k) =ᵐ[μ]
      fun x => squareCoreContraction (entropyScale k) (SobolevSpace.toLp μ hQ f x) :=
    (squareCoreContraction_lipschitz (entropyScale_pos k)).coeFn_compLp
      (squareCoreContraction_zero (entropyScale k)) _
  have hm (k : ℕ) := (Lp.memLp (SobolevSpace.toLp μ hQ (g k))).ae_eq (hco k)
  have he (k : ℕ) : (hm k).toLp _ = SobolevSpace.toLp μ hQ (g k) := by
    apply Lp.ext
    exact (hm k).coeFn_toLp.trans (hco k).symm
  have hi : Integrable (fun x => (SobolevSpace.toLp μ hQ f x)^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using (Lp.memLp (SobolevSpace.toLp μ hQ f)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hc := L2Differentiation.toLp_tendsto_of_dominated μ hm
    (Lp.memLp (SobolevSpace.toLp μ hQ f))
    (fun x => (SobolevSpace.toLp μ hQ f x)^2) hi
    (Eventually.of_forall fun k => ?_)
    (show ∀ᵐ x ∂μ, Tendsto (fun k => squareCoreContraction (entropyScale k) (SobolevSpace.toLp μ hQ f x))
      atTop (𝓝 (SobolevSpace.toLp μ hQ f x)) from ?_)
  · have heF : (Lp.memLp (SobolevSpace.toLp μ hQ f)).toLp _ = SobolevSpace.toLp μ hQ f := by
      apply Lp.ext
      exact (Lp.memLp (SobolevSpace.toLp μ hQ f)).coeFn_toLp
    simp only [he,heF] at hc
    apply SobolevSpace.tendsto_of_toLp_tendsto_energy_le μ hQ hc
    intro ε hε
    exact Eventually.of_forall fun k => (SobolevSpace.energy_compContraction_le μ hQ _ _ f).trans (le_add_of_nonneg_right hε.le)
  · filter_upwards [(Lp.coeFn_nonneg _).mpr hf] with x hx
    change 0 ≤ SobolevSpace.toLp μ hQ f x at hx
    have hb := squareCoreContraction_bounds (entropyScale_pos k) hx
    nlinarith [sq_nonneg (SobolevSpace.toLp μ hQ f x-squareCoreContraction (entropyScale k) (SobolevSpace.toLp μ hQ f x))]
  · filter_upwards [(Lp.coeFn_nonneg _).mpr hf] with x hx
    exact RegularPointCoordinates.squareCoreContraction_tendsto hx


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem SobolevSpace.quantitative_strong_square_core_recovery (f : SobolevSpace μ hQ)
    (M : ℝ≥0) (hf : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ f x ∧ SobolevSpace.toLp μ hQ f x ≤ M)
    (p : X) {r : ℝ} (hs : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x ≠ 0 → dist p x ≤ r) :
    ∃ (qs : ℕ → SobolevSpace μ hQ) (hs : ℕ → X → ℝ),
      Tendsto qs atTop (𝓝 f) ∧
      (∀ i, ∃ C : ℝ≥0, LipschitzWith C (hs i)) ∧
      (∀ i, SobolevSpace.toLp μ hQ (qs i) =ᵐ[μ] fun x => hs i x^2) ∧
      (∀ i x, 0 ≤ hs i x ∧ hs i x^2 ≤ M) ∧
      (∀ i x, hs i x ≠ 0 → dist p x ≤ 2*(max r 0+1)) := by
  classical
  obtain ⟨fs,gs,hl,hLip,hrep,hb,hs⟩ :=
    SobolevSpace.quantitative_strong_compact_bounded_recovery μ hQ f M hf p hs
  have hn (i : ℕ) : 0 ≤ SobolevSpace.toLp μ hQ (fs i) := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [hrep i] with x hx
    rw [hx]
    exact (hb i x).1
  let q (i k : ℕ) := SobolevSpace.compContraction μ hQ
    (squareCoreContraction_lipschitz (entropyScale_pos k))
    (squareCoreContraction_zero (entropyScale k)) (fs i)
  have he (i : ℕ) : ∃ k, dist (q i k) (fs i) < entropyScale i := by
    have ht := SobolevSpace.squareCoreContraction_tendsto μ hQ (fs i) (hn i)
    obtain ⟨k,hk⟩ := Metric.tendsto_atTop.mp ht (entropyScale i) (entropyScale_pos i)
    exact ⟨k,hk k le_rfl⟩
  choose N hN using he
  let qs := fun i => q i (N i)
  let vs := fun i x => squareCoreRoot (entropyScale (N i)) (gs i x)
  have hqs : Tendsto qs atTop (𝓝 f) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have he := (entropyScale_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (show (0:ℝ) < ε/2 by linarith))
    have hf' := (tendsto_iff_dist_tendsto_zero.mp hl).eventually
      (gt_mem_nhds (show (0:ℝ) < ε/2 by linarith))
    obtain ⟨k,hk⟩ := eventually_atTop.mp (he.and hf')
    refine ⟨k,fun i hi => ?_⟩
    have htri := dist_triangle (qs i) (fs i) f
    have hNi := hN i
    have hh := hk i hi
    change dist (qs i) (fs i) < entropyScale i at hNi
    linarith
  refine ⟨qs,vs,hqs,?_,?_,?_,?_⟩
  · intro i
    obtain ⟨C,hC⟩ := hLip i
    exact ⟨_,(squareCoreRoot_lipschitz (entropyScale_pos (N i))).comp hC⟩
  · intro i
    have hc := (squareCoreContraction_lipschitz (entropyScale_pos (N i))).coeFn_compLp
      (squareCoreContraction_zero (entropyScale (N i))) (SobolevSpace.toLp μ hQ (fs i))
    filter_upwards [hc,hrep i] with x hx hx'
    change SobolevSpace.toLp μ hQ (qs i) x =
      squareCoreContraction (entropyScale (N i)) (SobolevSpace.toLp μ hQ (fs i) x) at hx
    rw [hx,hx']
    rfl
  · intro i x
    exact ⟨squareCoreRoot_nonneg (entropyScale_pos (N i)) _,
      (squareCoreContraction_bounds (entropyScale_pos (N i)) (hb i x).1).2.trans (hb i x).2⟩
  · intro i x hx
    apply hs i x
    intro hz
    apply hx
    simp only [vs,hz,squareCoreRoot_zero]


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

theorem SobolevSpace.quantitative_strong_probability_square_recovery (f : SobolevSpace μ hQ)
    (M : ℝ≥0) (hf : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ f x ∧ SobolevSpace.toLp μ hQ f x ≤ M)
    (p : X) {r : ℝ} (hs : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x ≠ 0 → dist p x ≤ r)
    (hm : (∫x, SobolevSpace.toLp μ hQ f x ∂μ) = 1) :
    ∃ (qs : ℕ → SobolevSpace μ hQ) (hs : ℕ → X → ℝ),
      Tendsto qs atTop (𝓝 f) ∧
      (∀ i, ∃ C : ℝ≥0, LipschitzWith C (hs i)) ∧
      (∀ i, SobolevSpace.toLp μ hQ (qs i) =ᵐ[μ] fun x => hs i x^2) ∧
      (∀ i x, 0 ≤ hs i x ∧ hs i x^2 ≤ 2*M) ∧
      (∀ i x, hs i x ≠ 0 → dist p x ≤ 2*(max r 0+1)) ∧
      (∀ i, ∫x, hs i x^2 ∂μ = 1) ∧
      (∀ᵐ x ∂μ, Tendsto (fun i => hs i x^2) atTop (𝓝 (SobolevSpace.toLp μ hQ f x))) ∧
      Tendsto (fun i => ∫x, hs i x^2*Real.log (hs i x^2) ∂μ) atTop
        (𝓝 (∫x, SobolevSpace.toLp μ hQ f x*Real.log (SobolevSpace.toLp μ hQ f x) ∂μ)) := by
  classical
  obtain ⟨qs,gs,hq,hLip,hrep,hb,hs⟩ :=
    SobolevSpace.quantitative_strong_square_core_recovery μ hQ f M hf p hs
  let R := 2*(max r 0+1)
  have hL2 : Tendsto (fun i => SobolevSpace.toLp μ hQ (qs i)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ f)) := (SobolevSpace.toLpCLM μ hQ).continuous.tendsto f |>.comp hq
  obtain ⟨s,hsm,hsa⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  have hga : ∀ᵐ x ∂μ, Tendsto (fun i => gs (s i) x^2) atTop (𝓝 (SobolevSpace.toLp μ hQ f x)) := by
    filter_upwards [hsa,ae_all_iff.mpr (fun i => hrep (s i))] with x hx he
    simpa only [he] using hx
  have hgb (i : ℕ) (x : X) : 0 ≤ gs (s i) x^2 ∧ gs (s i) x^2 ≤ M :=
    ⟨sq_nonneg _,(hb _ _).2⟩
  have hgs (i : ℕ) (x : X) (hx : gs (s i) x^2 ≠ 0) : dist p x ≤ R := by
    apply hs (s i) x
    intro hz
    exact hx (by rw [hz,zero_pow (by norm_num : (2:ℕ) ≠ 0)])
  have hmass : Tendsto (fun i => ∫x, gs (s i) x^2 ∂μ) atTop (𝓝 (1:ℝ)) := by
    rw [←hm]
    exact compact_bounded_integral_tendsto μ p R M
      (fun i => (hLip (s i)).choose_spec.continuous.measurable.pow_const 2)
      hgb hgs hga continuous_id rfl
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hmass.eventually (lt_mem_nhds (by norm_num : (1:ℝ)/2 < 1)))
  let a : ℕ → ℝ := fun i => (∫x, gs (s (i+N)) x^2 ∂μ)⁻¹
  have hmasspos (i : ℕ) : 0 < ∫x, gs (s (i+N)) x^2 ∂μ := by
    have hu := hN (i+N) (Nat.le_add_left N i)
    linarith
  have haP (i : ℕ) : 0 < a i := inv_pos.mpr (hmasspos i)
  have haB (i : ℕ) : a i ≤ 2 := by
    calc
      _ ≤ ((1:ℝ)/2)⁻¹ := (inv_le_inv₀ (hmasspos i) (by norm_num)).mpr
        (hN (i+N) (Nat.le_add_left N i)).le
      _ = 2 := by norm_num
  have haL : Tendsto a atTop (𝓝 (1:ℝ)) := by
    simpa only [a,Function.comp_def,inv_one] using
      (hmass.comp (tendsto_add_atTop_nat N)).inv₀ one_ne_zero
  let vs := fun i => a i • qs (s (i+N))
  let ks := fun i x => Real.sqrt (a i)*gs (s (i+N)) x
  have hkq (i : ℕ) (x : X) : ks i x^2 = a i*gs (s (i+N)) x^2 := by
    dsimp only [ks]
    rw [mul_pow,Real.sq_sqrt (haP i).le]
  have hv : Tendsto vs atTop (𝓝 f) := by
    simpa only [vs,Function.comp_def,one_smul] using
      haL.smul (hq.comp (hsm.tendsto_atTop.comp (tendsto_add_atTop_nat N)))
  have hkl (i : ℕ) : ∃ C : ℝ≥0, LipschitzWith C (ks i) := by
    obtain ⟨C,hC⟩ := hLip (s (i+N))
    exact ⟨_,lipschitzWith_const_mul_real hC (Real.sqrt (a i))⟩
  have hkr (i : ℕ) : SobolevSpace.toLp μ hQ (vs i) =ᵐ[μ] fun x => ks i x^2 := by
    have hre := hrep (s (i+N))
    change SobolevSpace.toLp μ hQ (a i • qs (s (i+N))) =ᵐ[μ] _
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (a i) (SobolevSpace.toLp μ hQ (qs (s (i+N)))),hre] with x hx hx'
    rw [hkq]
    simpa only [Pi.smul_apply,smul_eq_mul,hx'] using hx
  have hkb (i : ℕ) (x : X) : 0 ≤ ks i x ∧ ks i x^2 ≤ 2*M := by
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (hb _ _).1,?_⟩
    rw [hkq]
    exact mul_le_mul (haB i) (hb _ _).2 (sq_nonneg _) (by norm_num)
  have hks (i : ℕ) (x : X) (hx : ks i x ≠ 0) : dist p x ≤ R := by
    apply hs (s (i+N)) x
    intro hz
    apply hx
    simp only [ks,hz,mul_zero]
  have hkm (i : ℕ) : (∫x, ks i x^2 ∂μ) = 1 := by
    simp_rw [hkq]
    rw [integral_const_mul]
    exact inv_mul_cancel₀ (ne_of_gt (hmasspos i))
  have hka : ∀ᵐ x ∂μ, Tendsto (fun i => ks i x^2) atTop (𝓝 (SobolevSpace.toLp μ hQ f x)) := by
    filter_upwards [hga] with x hx
    simp_rw [hkq]
    simpa only [one_mul,Function.comp_def] using haL.mul (hx.comp (tendsto_add_atTop_nat N))
  refine ⟨vs,ks,hv,hkl,hkr,hkb,hks,hkm,hka,?_⟩
  exact compact_bounded_integral_tendsto μ p R (2*M)
    (fun i => (hkl i).choose_spec.continuous.measurable.pow_const 2)
    (fun i x => ⟨sq_nonneg _,(hkb i x).2⟩)
    (fun i x hx => hks i x (by intro hz; exact hx (by rw [hz]; norm_num)))
    hka Real.continuous_mul_log (by simp)


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

theorem density_entropy_regularized_support {a b ε : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    a * Real.log a - b * Real.log b ≤
      (a-b) + (a-b) * Real.log (a+ε) + ε := by
  have hs := density_entropy_supporting_line (show 0 < a+ε by linarith) hb
  have hl : a*Real.log a ≤ a*Real.log (a+ε) := by
    rcases eq_or_lt_of_le ha with he | hp
    · simp [←he]
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log hp (by linarith)) ha
  nlinarith

variable {X : Type*} [MeasurableSpace X]

theorem integral_entropy_regularized_subgradient (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (heF : Integrable (fun x => f x*Real.log (f x)) μ)
    (heG : Integrable (fun x => g x*Real.log (g x)) μ)
    {ε : ℝ} (hε : 0 < ε)
    (hflog : Integrable (fun x => f x*Real.log (f x+ε)) μ)
    (hglog : Integrable (fun x => g x*Real.log (f x+ε)) μ)
    (hmass : (∫x, f x ∂μ) = ∫x, g x ∂μ) :
    (∫x, f x*Real.log (f x) ∂μ)-(∫x, g x*Real.log (g x) ∂μ) ≤
      (∫x, f x*Real.log (f x+ε) ∂μ)-(∫x, g x*Real.log (f x+ε) ∂μ) +
        ε*(μ univ).toReal := by
  have hi := ((hf.sub hg).add (hflog.sub hglog)).add (integrable_const ε)
  have hs := integral_mono_ae (heF.sub heG) hi (by
    filter_upwards [hf0,hg0] with x ha hb
    simpa only [Pi.add_apply,Pi.sub_apply,sub_mul] using
      density_entropy_regularized_support ha hb hε)
  simp only [Pi.add_apply,Pi.sub_apply] at hs
  have h₁ := integral_add ((hf.sub hg).add (hflog.sub hglog)) (integrable_const ε)
  have h₂ := integral_add (hf.sub hg) (hflog.sub hglog)
  simp only [Pi.add_apply,Pi.sub_apply] at h₁ h₂
  rw [integral_sub heF heG,h₁,h₂,integral_sub hf hg,integral_sub hflog hglog,
    hmass,sub_self,zero_add,integral_const,smul_eq_mul,Measure.real,mul_comm (μ univ).toReal ε] at hs
  exact hs

theorem probability_entropy_regularized_subgradient (μ : Measure X) [IsFiniteMeasure μ]
    (ν₀ ν : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν]
    (h0 : ν₀ ≪ μ) (hν : ν ≪ μ)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (he : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    {ε : ℝ} (hε : 0 < ε)
    (hlog0 : Integrable (fun x => Real.log ((ν₀.rnDeriv μ x).toReal+ε)) ν₀)
    (hlog : Integrable (fun x => Real.log ((ν₀.rnDeriv μ x).toReal+ε)) ν) :
    boltzmannEntropy μ ν₀ - boltzmannEntropy μ ν ≤
      (∫x, Real.log ((ν₀.rnDeriv μ x).toReal+ε) ∂ν₀)-
      (∫x, Real.log ((ν₀.rnDeriv μ x).toReal+ε) ∂ν) + ε*(μ univ).toReal := by
  have hi₀ : Integrable (fun x => (ν₀.rnDeriv μ x).toReal) μ := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (ν := μ) (measure_ne_top ν₀ Set.univ))
  have hi : Integrable (fun x => (ν.rnDeriv μ x).toReal) μ := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (ν := μ) (measure_ne_top ν Set.univ))
  have hH := integral_entropy_regularized_subgradient μ _ _ hi₀ hi
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) he0 he hε
    ((integrable_toReal_rnDeriv_mul_iff h0).mpr hlog0)
    ((integrable_toReal_rnDeriv_mul_iff hν).mpr hlog) (by
      rw [Measure.integral_toReal_rnDeriv h0,Measure.integral_toReal_rnDeriv hν]; simp)
  have hI0 := integral_rnDeriv_smul (f := fun x => Real.log ((ν₀.rnDeriv μ x).toReal+ε)) h0
  have hI := integral_rnDeriv_smul (f := fun x => Real.log ((ν₀.rnDeriv μ x).toReal+ε)) hν
  simp only [smul_eq_mul] at hI0 hI
  simpa only [boltzmannEntropy,hI0,hI] using hH

theorem entropy_regularized_subgradient_rep (μ : Measure X) [IsFiniteMeasure μ]
    (ν₀ ν : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν]
    (h0 : ν₀ ≪ μ) (hν : ν ≪ μ)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (he : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    {ε : ℝ} (hε : 0 < ε) (r : X → ℝ)
    (hr : r =ᵐ[μ] fun x => (ν₀.rnDeriv μ x).toReal)
    (hlog0 : Integrable (fun x => Real.log (r x+ε)) ν₀)
    (hlog : Integrable (fun x => Real.log (r x+ε)) ν) :
    boltzmannEntropy μ ν₀ - boltzmannEntropy μ ν ≤
      (∫x, Real.log (r x+ε) ∂ν₀)-(∫x, Real.log (r x+ε) ∂ν) + ε*(μ univ).toReal := by
  have hrep : (fun x => Real.log (r x+ε)) =ᵐ[μ]
      fun x => Real.log ((ν₀.rnDeriv μ x).toReal+ε) :=
    hr.mono fun x hx => by dsimp only at hx ⊢; rw [hx]
  have h := probability_entropy_regularized_subgradient μ ν₀ ν h0 hν he0 he hε
    (hlog0.congr (h0.ae_eq hrep)) (hlog.congr (hν.ae_eq hrep))
  rwa [←integral_congr_ae (h0.ae_eq hrep),←integral_congr_ae (hν.ae_eq hrep)] at h

variable [MetricSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem entropy_regularized_subgradient_localized (μ : Measure X) [SigmaFinite μ]
    (ν₀ ν : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (h0 : ν₀ ≪ μ.restrict B) (hν : ν ≪ μ.restrict B)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (he : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    {ε : ℝ} (hε : 0 < ε) (r : X → ℝ)
    (hr : r =ᵐ[μ] fun x => (ν₀.rnDeriv μ x).toReal)
    (hlog0 : Integrable (fun x => Real.log (r x+ε)) ν₀)
    (hlog : Integrable (fun x => Real.log (r x+ε)) ν) :
    boltzmannEntropy μ ν₀ - boltzmannEntropy μ ν ≤
      (∫x, Real.log (r x+ε) ∂ν₀)-(∫x, Real.log (r x+ε) ∂ν) + ε*(μ B).toReal := by
  have hr' : r =ᵐ[μ.restrict B] fun x => (ν₀.rnDeriv (μ.restrict B) x).toReal := by
    filter_upwards [ae_restrict_of_ae hr,ae_restrict_of_ae (rnDeriv_localized μ ν₀ hB h0),
      ae_restrict_mem hB] with x hx hd hb
    simp only [hx,hd,indicator_of_mem hb]
  have h := entropy_regularized_subgradient_rep (μ.restrict B) ν₀ ν h0 hν
    ((entropy_integrable_localized_iff μ ν₀ hB h0).mp he0)
    ((entropy_integrable_localized_iff μ ν hB hν).mp he) hε r hr' hlog0 hlog
  simpa only [←boltzmannEntropy_localized μ ν₀ hB h0,
    ←boltzmannEntropy_localized μ ν hB hν,Measure.restrict_apply_univ] using h


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem planInitialSecant_log_reweight_error_path (μ : Measure X)
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    {ρ G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ ρ G)
    {ε : ℝ} (hε : 0 < ε) (hlp : ∀ t : Time, ∀ᵐ γ ∂π, ε ≤ ρ (γ t))
    (hil : ∀ t : Time, Integrable (fun γ : C(Time,X) => Real.log (ρ (γ t))) π)
    (t : Time) (ht : 0 < (t : ℝ)) :
    |planInitialSecant (inverseInitialDensityPlan π ρ) ρ t -
        planInitialSecant π (fun x => Real.log (ρ x)) t| ≤
      (t : ℝ) * ((ε^2)⁻¹ * D^2 * (C.toReal * ∫ x, G x^2 ∂μ)) := by
  have hir (s : Time) : Integrable (fun γ : C(Time, X) => ρ (γ s)) π :=
    (compressionPullback_memLp μ π _ (measurable_path_eval s) hC (hcomp s) ρ).integrable (by norm_num)
  have hiq : Integrable (fun γ : C(Time, X) => (ρ (γ t)-ρ (γ 0)) / ρ (γ 0)) π := by
    simp_rw [div_eq_mul_inv]
    apply ((hir t).sub (hir 0)).mul_bdd
    · exact ((Lp.stronglyMeasurable ρ).measurable.comp (measurable_path_eval 0)).inv.aestronglyMeasurable
    · filter_upwards [hlp 0] with γ hγ
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hε.le.trans hγ))]
      exact inv_anti₀ hε hγ
  have hils : Integrable (fun γ : C(Time, X) => Real.log (ρ (γ t)) - Real.log (ρ (γ 0))) π :=
    (hil t).sub (hil 0)
  have hirem := hiq.sub hils
  have hisq := ((compressionPullback_memLp μ π _ (measurable_path_eval t) hC (hcomp t) ρ).sub
    (compressionPullback_memLp μ π _ (measurable_path_eval 0) hC (hcomp 0) ρ)).integrable_sq
  have hrem : |∫ γ : C(Time, X), (ρ (γ t)-ρ (γ 0)) / ρ (γ 0) -
      (Real.log (ρ (γ t))-Real.log (ρ (γ 0))) ∂π| ≤
      (ε^2)⁻¹ * ∫ γ : C(Time, X), (ρ (γ t)-ρ (γ 0))^2 ∂π := by
    apply (abs_integral_le_integral_abs).trans
    rw [← integral_const_mul]
    apply integral_mono_ae hirem.abs (hisq.const_mul _)
    filter_upwards [hlp t, hlp 0] with γ ht h0
    exact log_linear_remainder_abs_le hε h0 ht
  have hsq := hG.testPlan_integrated_square μ π hgeo hC hcomp hD hDb t
  have htotal := hrem.trans (mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (sq_nonneg ε)))
  simp_rw [planInitialSecant, geodesicExtension_eq]
  rw [inverseInitialDensityPlan_integral π (Lp.stronglyMeasurable ρ).measurable
    ((hlp 0).mono fun γ hh => hε.le.trans hh), ← sub_div,
    ← integral_sub hiq hils, abs_div, abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  convert htotal using 1 ; ring

theorem planInitialSecant_log_reweight_tendsto_path (μ : Measure X)
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    {ρ G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ ρ G)
    {ε : ℝ} (hε : 0 < ε) (hlp : ∀ t : Time, ∀ᵐ γ ∂π, ε ≤ ρ (γ t))
    (hil : ∀ t : Time, Integrable (fun γ : C(Time,X) => Real.log (ρ (γ t))) π) :
    Tendsto (fun t => planInitialSecant (inverseInitialDensityPlan π ρ) ρ t -
      planInitialSecant π (fun x => Real.log (ρ x)) t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t : ℝ => t * ((ε^2)⁻¹ * D^2 * (C.toReal * ∫ x, G x^2 ∂μ)))
  · have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      (gt_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall, self_mem_nhdsWithin] with t ht1 ht0
    exact planInitialSecant_log_reweight_error_path μ π hgeo hC hcomp hD hDb hG hε hlp hil
      ⟨t, ht0.le, ht1.le⟩ ht0
  · simpa using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const
      ((ε^2)⁻¹ * D^2 * (C.toReal * ∫ x, G x^2 ∂μ))

omit [MeasurableSpace X] [BorelSpace X] in
theorem inverseInitialDensityPlan_le_path (π : Measure C(Time,X))
    {ρ : X → ℝ} {ε : ℝ} (hε : 0 < ε) (hl : ∀ᵐ γ ∂π, ε ≤ ρ (γ 0)) :
    inverseInitialDensityPlan π ρ ≤ ENNReal.ofReal ε⁻¹ • π := by
  rw [←withDensity_const]
  apply withDensity_mono
  filter_upwards [hl] with γ hγ
  exact ENNReal.ofReal_le_ofReal (inv_anti₀ hε hγ)

theorem path_log_signed_variation [ProperSpace X]
    (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (u ρ : SobolevSpace μ hQ)
    {ε : ℝ} (hε : 0 < ε)
    (hlp : ∀ t : Time, ∀ᵐ γ ∂π, ε ≤ SobolevSpace.toLp μ hQ ρ (γ t))
    (hil : ∀ t : Time, Integrable
      (fun γ : C(Time,X) => Real.log (SobolevSpace.toLp μ hQ ρ (γ t))) π)
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1)) :
    Tendsto (planInitialSecant π (fun x => Real.log (SobolevSpace.toLp μ hQ ρ x)))
      (𝓝[>] (0:ℝ)) (𝓝 (-weightedGradientPair μ hQ
        ((inverseInitialDensityPlan π (SobolevSpace.toLp μ hQ ρ)).map (fun γ => γ 0)) u ρ)) := by
  let r := SobolevSpace.toLp μ hQ ρ
  let π' := inverseInitialDensityPlan π r
  have hlen := inverseInitialDensityPlan_le_path π hε (hlp 0)
  let : IsFiniteMeasure (ENNReal.ofReal ε⁻¹ • π) := Measure.smul_finite π ENNReal.ofReal_ne_top
  let : IsFiniteMeasure π' := isFiniteMeasure_of_le (ENNReal.ofReal ε⁻¹ • π) hlen
  have hac : π' ≪ π := inverseInitialDensityPlan_ac π r
  have hcomp' (t : Time) : π'.map (fun γ => γ t) ≤ (ENNReal.ofReal ε⁻¹*C) • μ := by
    have hh := Measure.map_mono hlen (measurable_path_eval t)
    rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable] at hh
    apply hh.trans
    intro s
    simpa only [Measure.smul_apply,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using
      mul_le_mul_left (hcomp t s) (ENNReal.ofReal ε⁻¹)
  have hd := kantorovich_signed_first_variation μ hQ π' (hac.ae_le hgeo)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC) hcomp'
    (hD.of_measure_le_smul ENNReal.ofReal_ne_top hlen) u ρ hu had (hac.ae_le hc) (hac.ae_le hb)
  have he := planInitialSecant_log_reweight_tendsto_path μ π hgeo hC hcomp hD hDb
    (SobolevSpace.minimalSlope_isRelaxed μ hQ ρ) hε hlp hil
  simpa only [π',r,sub_sub_cancel,sub_zero] using hd.sub he


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem planInitialSecant_log_reweight_error_at (μ : Measure X)
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    {ρ G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ ρ G)
    {ε : ℝ} (hε : 0 < ε) (t : Time) (ht : 0 < (t : ℝ))
    (hl0 : ∀ᵐ γ ∂π, ε ≤ ρ (γ 0))
    (hlt : ∀ᵐ γ ∂π, ε ≤ ρ (γ t))
    (hil0 : Integrable (fun γ : C(Time,X) => Real.log (ρ (γ 0))) π)
    (hilt : Integrable (fun γ : C(Time,X) => Real.log (ρ (γ t))) π) :
    |planInitialSecant (inverseInitialDensityPlan π ρ) ρ t -
        planInitialSecant π (fun x => Real.log (ρ x)) t| ≤
      (t : ℝ) * ((ε^2)⁻¹ * D^2 * (C.toReal * ∫ x, G x^2 ∂μ)) := by
  have hir (s : Time) : Integrable (fun γ : C(Time, X) => ρ (γ s)) π :=
    (compressionPullback_memLp μ π _ (measurable_path_eval s) hC (hcomp s) ρ).integrable (by norm_num)
  have hiq : Integrable (fun γ : C(Time, X) => (ρ (γ t)-ρ (γ 0)) / ρ (γ 0)) π := by
    simp_rw [div_eq_mul_inv]
    apply ((hir t).sub (hir 0)).mul_bdd
    · exact ((Lp.stronglyMeasurable ρ).measurable.comp (measurable_path_eval 0)).inv.aestronglyMeasurable
    · filter_upwards [hl0] with γ hγ
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hε.le.trans hγ))]
      exact inv_anti₀ hε hγ
  have hils : Integrable (fun γ : C(Time, X) => Real.log (ρ (γ t)) - Real.log (ρ (γ 0))) π :=
    (hilt).sub (hil0)
  have hirem := hiq.sub hils
  have hisq := ((compressionPullback_memLp μ π _ (measurable_path_eval t) hC (hcomp t) ρ).sub
    (compressionPullback_memLp μ π _ (measurable_path_eval 0) hC (hcomp 0) ρ)).integrable_sq
  have hrem : |∫ γ : C(Time, X), (ρ (γ t)-ρ (γ 0)) / ρ (γ 0) -
      (Real.log (ρ (γ t))-Real.log (ρ (γ 0))) ∂π| ≤
      (ε^2)⁻¹ * ∫ γ : C(Time, X), (ρ (γ t)-ρ (γ 0))^2 ∂π := by
    apply (abs_integral_le_integral_abs).trans
    rw [← integral_const_mul]
    apply integral_mono_ae hirem.abs (hisq.const_mul _)
    filter_upwards [hlt, hl0] with γ ht h0
    exact log_linear_remainder_abs_le hε h0 ht
  have hsq := hG.testPlan_integrated_square μ π hgeo hC hcomp hD hDb t
  have htotal := hrem.trans (mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (sq_nonneg ε)))
  simp_rw [planInitialSecant, geodesicExtension_eq]
  rw [inverseInitialDensityPlan_integral π (Lp.stronglyMeasurable ρ).measurable
    ((hl0).mono fun γ hh => hε.le.trans hh), ← sub_div,
    ← integral_sub hiq hils, abs_div, abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  convert htotal using 1 ; ring

theorem planInitialSecant_log_reweight_tendsto_eventual (μ : Measure X)
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    {ρ G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ ρ G)
    {ε α : ℝ} (hε : 0 < ε) (hα : 0 < α)
    (hlp : ∀ t : Time, (t:ℝ) < α → ∀ᵐ γ ∂π, ε ≤ ρ (γ t))
    (hil : ∀ t : Time, (t:ℝ) < α →
      Integrable (fun γ : C(Time,X) => Real.log (ρ (γ t))) π) :
    Tendsto (fun t => planInitialSecant (inverseInitialDensityPlan π ρ) ρ t -
      planInitialSecant π (fun x => Real.log (ρ x)) t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t : ℝ => t * ((ε^2)⁻¹ * D^2 * (C.toReal * ∫ x, G x^2 ∂μ)))
  · have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < min 1 α :=
      (gt_mem_nhds (lt_min zero_lt_one hα)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall, self_mem_nhdsWithin] with t ht ht0
    have ht1 := lt_of_lt_of_le ht (min_le_left _ _)
    have hta := lt_of_lt_of_le ht (min_le_right _ _)
    exact planInitialSecant_log_reweight_error_at μ π hgeo hC hcomp hD hDb hG hε
      ⟨t, ht0.le, ht1.le⟩ ht0 (hlp 0 hα) (hlp _ hta) (hil 0 hα) (hil _ hta)
  · simpa using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).mono_left
      nhdsWithin_le_nhds).mul_const ((ε^2)⁻¹ * D^2 * (C.toReal * ∫ x, G x^2 ∂μ))

theorem path_log_signed_variation_eventual [ProperSpace X]
    (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (u ρ : SobolevSpace μ hQ)
    {ε α : ℝ} (hε : 0 < ε) (hα : 0 < α)
    (hlp : ∀ t : Time, (t:ℝ) < α → ∀ᵐ γ ∂π, ε ≤ SobolevSpace.toLp μ hQ ρ (γ t))
    (hil : ∀ t : Time, (t:ℝ) < α → Integrable
      (fun γ : C(Time,X) => Real.log (SobolevSpace.toLp μ hQ ρ (γ t))) π)
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1)) :
    Tendsto (planInitialSecant π (fun x => Real.log (SobolevSpace.toLp μ hQ ρ x)))
      (𝓝[>] (0:ℝ)) (𝓝 (-weightedGradientPair μ hQ
        ((inverseInitialDensityPlan π (SobolevSpace.toLp μ hQ ρ)).map (fun γ => γ 0)) u ρ)) := by
  let r := SobolevSpace.toLp μ hQ ρ
  let π' := inverseInitialDensityPlan π r
  have hlen := inverseInitialDensityPlan_le_path π hε (hlp 0 hα)
  let : IsFiniteMeasure (ENNReal.ofReal ε⁻¹ • π) := Measure.smul_finite π ENNReal.ofReal_ne_top
  let : IsFiniteMeasure π' := isFiniteMeasure_of_le (ENNReal.ofReal ε⁻¹ • π) hlen
  have hac : π' ≪ π := inverseInitialDensityPlan_ac π r
  have hcomp' (t : Time) : π'.map (fun γ => γ t) ≤ (ENNReal.ofReal ε⁻¹*C) • μ := by
    have hh := Measure.map_mono hlen (measurable_path_eval t)
    rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable] at hh
    apply hh.trans
    intro s
    simpa only [Measure.smul_apply,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using
      mul_le_mul_left (hcomp t s) (ENNReal.ofReal ε⁻¹)
  have hd := kantorovich_signed_first_variation μ hQ π' (hac.ae_le hgeo)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC) hcomp'
    (hD.of_measure_le_smul ENNReal.ofReal_ne_top hlen) u ρ hu had (hac.ae_le hc) (hac.ae_le hb)
  have he := planInitialSecant_log_reweight_tendsto_eventual μ π hgeo hC hcomp hD hDb
    (SobolevSpace.minimalSlope_isRelaxed μ hQ ρ) hε hα hlp hil
  simpa only [π',r,sub_sub_cancel,sub_zero] using hd.sub he


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem abs_log_sub_le_div {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log b - Real.log a| ≤ |b-a| / c := by
  have ha' := hc.trans_le ha
  have hb' := hc.trans_le hb
  apply abs_le.mpr
  constructor
  · have hh := Real.log_le_sub_one_of_pos (div_pos ha' hb')
    rw [Real.log_div ha'.ne' hb'.ne'] at hh
    have h1 : a / b - 1 = (a-b)/b := by field_simp
    rw [h1] at hh
    have h2 : (a-b)/b ≤ |b-a|/c := by
      apply (div_le_div_of_nonneg_right (show a-b ≤ |b-a| by
        rw [←abs_sub_comm a b]; exact le_abs_self _) hb'.le).trans
      exact div_le_div_of_nonneg_left (abs_nonneg _) hc hb
    linarith
  · have hh := Real.log_le_sub_one_of_pos (div_pos hb' ha')
    rw [Real.log_div hb'.ne' ha'.ne'] at hh
    have h1 : b / a - 1 = (b-a)/a := by field_simp
    rw [h1] at hh
    apply hh.trans
    apply (div_le_div_of_nonneg_right (le_abs_self _) ha'.le).trans
    exact div_le_div_of_nonneg_left (abs_nonneg _) hc ha

theorem regularized_square_log_secant_bound {a b t T : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) (hT : 0 ≤ T)
    (hab : |b-a| ≤ T*t) :
    |(Real.log (b^2+t^2)-Real.log (a^2+t^2))/t| ≤
      (2*T*(T+2)*(T+1)^2)/(a+t) := by
  have hat : 0 < a+t := by linarith
  have hbt : 0 < b+t := by linarith
  have hTp : 0 < T+1 := by linarith
  have hsum : a+b ≤ (T+2)*(a+t) := by
    have hh := (abs_le.mp hab).2
    nlinarith [mul_nonneg hT ha]
  have hatb : a+t ≤ (T+1)*(b+t) := by
    have hh := (abs_le.mp hab).1
    nlinarith [mul_nonneg hT hb]
  have habsq : (a+t)^2 ≤ (T+1)^2*(b+t)^2 := by
    nlinarith [sq_le_sq₀ hat.le (mul_nonneg hTp.le hbt.le) |>.mpr hatb]
  have hqa : (a+t)^2 ≤ 2*(a^2+t^2) := by nlinarith [sq_nonneg (a-t)]
  have hqb : (b+t)^2 ≤ 2*(b^2+t^2) := by nlinarith [sq_nonneg (b-t)]
  have hone : 1 ≤ (T+1)^2 := by nlinarith
  have hca : (a+t)^2/(2*(T+1)^2) ≤ a^2+t^2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hone (show 0 ≤ 2*(a^2+t^2) by positivity)
    nlinarith
  have hcb : (a+t)^2/(2*(T+1)^2) ≤ b^2+t^2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hqb (sq_nonneg (T+1))
    nlinarith
  have hc : 0 < (a+t)^2/(2*(T+1)^2) := by positivity
  have hlog := abs_log_sub_le_div hc hca hcb
  have hnum : |b^2+t^2-(a^2+t^2)| ≤ T*t*((T+2)*(a+t)) := by
    have he : b^2+t^2-(a^2+t^2) = (b-a)*(a+b) := by ring
    rw [he,abs_mul,abs_of_nonneg (add_nonneg ha hb)]
    exact mul_le_mul hab hsum (add_nonneg ha hb) (mul_nonneg hT ht.le)
  rw [abs_div,abs_of_pos ht]
  apply (div_le_div_of_nonneg_right (hlog.trans
    (div_le_div_of_nonneg_right hnum hc.le)) ht.le).trans
  have he : T*t*((T+2)*(a+t))/((a+t)^2/(2*(T+1)^2))/t =
      (2*T*(T+2)*(T+1)^2)/(a+t) := by
    field_simp
  exact he.le


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 theorem inverseInitialDensityPlan_restrict_initial
    (μ : Measure X) (π : Measure C(Time,X)) {ρ : X → ℝ}
    (hρ : Measurable ρ) (hp : ∀ᵐ x ∂μ, 0 < ρ x)
    (h0 : π.map (fun γ => γ 0) = μ.withDensity (fun x => ENNReal.ofReal (ρ x)))
    {A : Set X} (hA : MeasurableSet A) :
    (inverseInitialDensityPlan (π.restrict ((fun γ => γ 0) ⁻¹' A)) ρ).map (fun γ => γ 0) =
      μ.restrict A := by
  apply inverseInitialDensityPlan_initial (μ.restrict A) _ hρ (ae_restrict_of_ae hp)
  rw [←Measure.restrict_map (measurable_path_eval 0) hA,h0,restrict_withDensity hA]

 theorem restrict_plan_compression (μ : Measure X) (π : Measure C(Time,X))
    {C : ℝ≥0∞} (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) (A : Set C(Time,X))
    (t : Time) : (π.restrict A).map (fun γ => γ t) ≤ C • μ :=
  (Measure.map_mono Measure.restrict_le_self (measurable_path_eval t)).trans (hcomp t)

omit [MeasurableSpace X] [BorelSpace X] in
 theorem lipschitz_geodesic_increment {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {γ : C(Time,X)} (hγ : IsGeodesic γ) (t : Time) :
    |g (γ t)-g (γ 0)| ≤ (L:ℝ) * (t:ℝ) * dist (γ 0) (γ 1) := by
  have hh := hg.dist_le_mul (γ t) (γ 0)
  rw [Real.dist_eq,hγ t 0] at hh
  simpa only [show ((0:Time):ℝ)=0 from rfl,sub_zero,abs_of_nonneg t.property.1,mul_assoc] using hh

 theorem lipschitz_plan_increment_integrable
    (π : Measure C(Time,X)) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)) π) (t : Time) :
    Integrable (fun γ : C(Time,X) => g (γ t)-g (γ 0)) π := by
  apply (hD.const_mul ((L:ℝ)*(t:ℝ))).mono'
    ((hg.continuous.measurable.comp (measurable_path_eval t)).sub
      (hg.continuous.measurable.comp (measurable_path_eval 0))).aestronglyMeasurable
  filter_upwards [hgeo] with γ hγ
  exact lipschitz_geodesic_increment hg hγ t

 theorem lipschitz_plan_secant_restrict_error
    (π : Measure C(Time,X)) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)) π)
    {A : Set C(Time,X)} (hA : MeasurableSet A) (t : Time) (ht : 0 < (t:ℝ)) :
    |planInitialSecant π g t-planInitialSecant (π.restrict A) g t| ≤
      (L:ℝ)*∫γ in Aᶜ, dist (γ 0) (γ 1) ∂π := by
  have hi := lipschitz_plan_increment_integrable π hgeo hg hD t
  have hsplit := integral_add_compl hA hi
  simp only [planInitialSecant,geodesicExtension_eq]
  rw [←sub_div,←hsplit]
  have he : ((∫γ in A, g (γ t)-g (γ 0) ∂π)+
      (∫γ in Aᶜ, g (γ t)-g (γ 0) ∂π))-(∫γ in A, g (γ t)-g (γ 0) ∂π) =
      ∫γ in Aᶜ, g (γ t)-g (γ 0) ∂π := by ring
  rw [he,abs_div,abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  calc
    _ ≤ ∫γ in Aᶜ, |g (γ t)-g (γ 0)| ∂π := abs_integral_le_integral_abs
    _ ≤ ∫γ in Aᶜ, (L:ℝ)*(t:ℝ)*dist (γ 0) (γ 1) ∂π := by
      apply integral_mono_ae hi.abs.integrableOn (hD.const_mul _).integrableOn
      filter_upwards [ae_restrict_of_ae hgeo] with γ hγ
      exact lipschitz_geodesic_increment hg hγ t
    _ = _ := by rw [integral_const_mul]; ring

omit [MetricSpace X] [BorelSpace X] in
 theorem tendsto_integral_log_levels (μ : Measure X) {g f : X → ℝ}
    (hg : Measurable g) (hf : Integrable f μ) :
    Tendsto (fun n : ℕ => ∫x in {x | |g x| ≤ (n:ℝ)}, f x ∂μ) atTop (𝓝 (∫x,f x ∂μ)) := by
  have hs (n : ℕ) : MeasurableSet {x | |g x| ≤ (n:ℝ)} := measurableSet_le hg.abs measurable_const
  simp_rw [←integral_indicator (hs _)]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => hf.aestronglyMeasurable.indicator (hs n)) hf.norm
  · intro n
    exact Eventually.of_forall fun x => by
      by_cases hx : |g x| ≤ (n:ℝ) <;> simp [hx]
  · exact Eventually.of_forall fun x => by
      have he : ∀ᶠ n : ℕ in atTop, |g x| ≤ (n:ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      simp [hn]

omit [MetricSpace X] [BorelSpace X] in
 theorem tendsto_integral_compl_log_levels (μ : Measure X) {g f : X → ℝ}
    (hg : Measurable g) (hf : Integrable f μ) :
    Tendsto (fun n : ℕ => ∫x in {x | |g x| ≤ (n:ℝ)}ᶜ, f x ∂μ) atTop (𝓝 0) := by
  have hh := (tendsto_const_nhds (x := ∫x, f x ∂μ) (f := atTop)).sub
    (tendsto_integral_log_levels μ hg hf)
  simpa only [sub_self] using hh.congr (fun n => by
    rw [←integral_add_compl (measurableSet_le hg.abs measurable_const) hf]
    ring)


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 theorem log_level_path_bound (π : Measure C(Time,X))
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D) (n : ℕ) (t : Time) :
    ∀ᵐ γ ∂π.restrict {γ | |g (γ 0)| ≤ (n:ℝ)},
      |g (γ t)| ≤ (n:ℝ)+(L:ℝ)*D := by
  have hm : MeasurableSet {γ : C(Time,X) | |g (γ 0)| ≤ (n:ℝ)} :=
    measurableSet_le (hg.continuous.measurable.comp (measurable_path_eval 0)).abs measurable_const
  filter_upwards [ae_restrict_mem hm,ae_restrict_of_ae hgeo,ae_restrict_of_ae hDb] with γ hn hγ hD
  have hi := lipschitz_geodesic_increment hg hγ t
  calc
    |g (γ t)| = |(g (γ t)-g (γ 0))+g (γ 0)| := by ring_nf
    _ ≤ |g (γ t)-g (γ 0)|+|g (γ 0)| := abs_add_le _ _
    _ ≤ (L:ℝ)*(t:ℝ)*dist (γ 0) (γ 1)+(n:ℝ) := add_le_add hi hn
    _ ≤ (L:ℝ)*D+(n:ℝ) := by
      apply add_le_add _ le_rfl
      calc
        _ ≤ (L:ℝ)*dist (γ 0) (γ 1) := by
          calc
            _ ≤ (L:ℝ)*1*dist (γ 0) (γ 1) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left t.property.2 L.coe_nonneg) dist_nonneg
            _ = _ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hD L.coe_nonneg
    _ = _ := add_comm _ _

 theorem log_core_restricted_signed_variation [ProperSpace X]
    (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (u ρ : SobolevSpace μ hQ)
    (hp : ∀ᵐ x ∂μ, 0 < SobolevSpace.toLp μ hQ ρ x)
    {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hlog : (fun x => Real.log (SobolevSpace.toLp μ hQ ρ x)) =ᵐ[μ] g)
    (h0 : π.map (fun γ => γ 0) = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1)) (n : ℕ) :
    Tendsto (planInitialSecant (π.restrict {γ | |g (γ 0)| ≤ (n:ℝ)}) g)
      (𝓝[>] (0:ℝ)) (𝓝 (-(∫x in {x | |g x| ≤ (n:ℝ)}, localGamma μ hQ u ρ x ∂μ))) := by
  let A : Set X := {x | |g x| ≤ (n:ℝ)}
  let σ := π.restrict ((fun γ => γ 0) ⁻¹' A)
  let r := SobolevSpace.toLp μ hQ ρ
  have hA : MeasurableSet A := measurableSet_le hg.continuous.measurable.abs measurable_const
  have hσ (s : Time) : σ.map (fun γ => γ s) ≤ C • μ := restrict_plan_compression μ π hcomp _ s
  have hrep (s : Time) : ∀ᵐ γ ∂σ, Real.log (r (γ s)) = g (γ s) :=
    ae_of_ae_map (measurable_path_eval s).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hσ s)).ae_eq hlog)
  have hpos (s : Time) : ∀ᵐ γ ∂σ, 0 < r (γ s) :=
    ae_of_ae_map (measurable_path_eval s).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hσ s)).ae_le hp)
  have hbd (s : Time) : ∀ᵐ γ ∂σ, |g (γ s)| ≤ (n:ℝ)+(L:ℝ)*D :=
    log_level_path_bound π hgeo hg hDb n s
  have hlp (s : Time) : ∀ᵐ γ ∂σ, Real.exp (-((n:ℝ)+(L:ℝ)*D)) ≤ r (γ s) := by
    filter_upwards [hrep s,hpos s,hbd s] with γ hlog' hp' hb'
    rw [←Real.exp_log hp',hlog']
    apply Real.exp_le_exp.mpr
    exact (abs_le.mp hb').1
  have hil (s : Time) : Integrable (fun γ : C(Time,X) => Real.log (r (γ s))) σ := by
    apply (integrable_const ((n:ℝ)+(L:ℝ)*D)).mono'
      (((Lp.stronglyMeasurable r).measurable.comp (measurable_path_eval s)).log.aestronglyMeasurable)
    filter_upwards [hrep s,hbd s] with γ hr hb'
    simpa only [Real.norm_eq_abs,Function.comp_apply,hr] using hb'
  have hd := path_log_signed_variation μ hQ σ (ae_restrict_of_ae hgeo) hC hσ
    (hD.mono_measure Measure.restrict_le_self) (ae_restrict_of_ae hDb) u ρ
    (Real.exp_pos _) hlp hil hu had (ae_restrict_of_ae hc) (ae_restrict_of_ae hb)
  have hinit := inverseInitialDensityPlan_restrict_initial μ π (Lp.stronglyMeasurable r).measurable hp h0 hA
  have hν : μ.restrict A ≤ (1:ℝ≥0∞) • μ := by simpa using (Measure.restrict_le_self (μ := μ) (s := A))
  rw [hinit,weightedGradientPair_eq_bracket μ hQ (C := 1) (by norm_num) hν,
    ←integral_localGamma μ hQ (C := 1) (by norm_num) hν] at hd
  apply hd.congr'
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
  exact planInitialSecant_congr_ae μ σ
    (fun s => Measure.absolutelyContinuous_of_le_smul (hσ s)) hlog ⟨ht0.le,ht1.le⟩

 

 theorem tendsto_of_uniform_secant_tails {F : Filter ℝ} {f : ℝ → ℝ}
    {fₙ : ℕ → ℝ → ℝ} {cₙ eₙ : ℕ → ℝ} {c : ℝ}
    (hc : Tendsto cₙ atTop (𝓝 c)) (he : Tendsto eₙ atTop (𝓝 0))
    (hf : ∀ n, Tendsto (fₙ n) F (𝓝 (cₙ n)))
    (hb : ∀ n, ∀ᶠ t in F, |f t-fₙ n t| ≤ eₙ n) :
    Tendsto f F (𝓝 c) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε/3 := by positivity
  have hc' := (Metric.tendsto_nhds.mp hc) (ε/3) hthird
  have he' := he.eventually (gt_mem_nhds hthird)
  obtain ⟨n,hnc,hne⟩ := (hc'.and he').exists
  have hf' := (Metric.tendsto_nhds.mp (hf n)) (ε/3) hthird
  filter_upwards [hb n,hf'] with t hbt hft
  rw [Real.dist_eq] at hnc hft ⊢
  calc
    |f t-c| = |(f t-fₙ n t)+(fₙ n t-cₙ n)+(cₙ n-c)| := by ring_nf
    _ ≤ |f t-fₙ n t|+|fₙ n t-cₙ n|+|cₙ n-c| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < ε := by linarith

 theorem log_core_signed_variation [ProperSpace X]
    (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (u ρ : SobolevSpace μ hQ)
    (hp : ∀ᵐ x ∂μ, 0 < SobolevSpace.toLp μ hQ ρ x)
    {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hlog : (fun x => Real.log (SobolevSpace.toLp μ hQ ρ x)) =ᵐ[μ] g)
    (h0 : π.map (fun γ => γ 0) = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1)) :
    Tendsto (planInitialSecant π g) (𝓝[>] (0:ℝ)) (𝓝 (-energyForm μ hQ u ρ)) := by
  apply tendsto_of_uniform_secant_tails
    (fₙ := fun n => planInitialSecant (π.restrict {γ | |g (γ 0)| ≤ (n:ℝ)}) g)
    (cₙ := fun n => -(∫x in {x | |g x| ≤ (n:ℝ)}, localGamma μ hQ u ρ x ∂μ))
    (eₙ := fun n => (L:ℝ)*∫γ in {γ | |g (γ 0)| ≤ (n:ℝ)}ᶜ, dist (γ 0) (γ 1) ∂π)
  · simpa only [integral_localGamma_eq_energyForm] using
      (tendsto_integral_log_levels μ hg.continuous.measurable (localGamma_memL1 μ hQ u ρ)).neg
  · simpa only [mul_zero,Function.comp_apply] using
      (tendsto_integral_compl_log_levels π
        (hg.continuous.measurable.comp (measurable_path_eval 0))
        (hD.integrable (by norm_num))).const_mul (L:ℝ)
  · exact log_core_restricted_signed_variation μ hQ π hgeo hC hcomp hD hDb u ρ hp hg hlog h0 hu had hc hb
  · intro n
    have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
      (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
    exact lipschitz_plan_secant_restrict_error π hgeo hg (hD.integrable (by norm_num))
      (measurableSet_le (hg.continuous.measurable.comp (measurable_path_eval 0)).abs measurable_const)
      ⟨t,ht0.le,ht1.le⟩ ht0



 
 theorem log_core_entropy_subgradient [ProperSpace X]
    (μ : Measure X) [SigmaFinite μ] [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀]
    (u ρ : SobolevSpace μ hQ)
    (hp : ∀ᵐ x ∂μ, 0 < SobolevSpace.toLp μ hQ ρ x)
    {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hlog : (fun x => Real.log (SobolevSpace.toLp μ hQ ρ x)) =ᵐ[μ] g)
    (hν : ν₀ = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hmap0 : π.map (fun γ => γ 0) = ν₀)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1))
    (K : ℝ)
    (hconv : ∀ t : Time,
      Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
        Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ ∧
      boltzmannEntropy μ (π.map (fun γ => γ t)) ≤
        (1 - (t : ℝ)) * boltzmannEntropy μ ν₀ + (t : ℝ) * boltzmannEntropy μ ν₁ +
        ((-K) * (t : ℝ) * (1 - (t : ℝ)) / 2) *
          (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π)) :
    -energyForm μ hQ u ρ ≤ boltzmannEntropy μ ν₁ - boltzmannEntropy μ ν₀ -
      (K / 2) * (∫ γ : C(Time, X), dist (γ 0) (γ 1)^2 ∂π) := by
  let r := SobolevSpace.toLp μ hQ ρ
  have hrn : (fun x => (ν₀.rnDeriv μ x).toReal) =ᵐ[μ] r := by
    rw [hν]
    filter_upwards [Measure.rnDeriv_withDensity μ (Lp.stronglyMeasurable r).measurable.ennreal_ofReal,
      hp] with x hx hxpos
    rw [hx, ENNReal.toReal_ofReal hxpos.le]
  have hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal := by
    filter_upwards [hrn,hp] with x hx hh
    rwa [hx]
  have hrep : g =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal := by
    filter_upwards [hrn,hlog] with x hx hh
    rw [hx,hh]
  have hd := log_core_signed_variation μ hQ π hgeo hC hcomp hD hDb
    u ρ hp hg hlog (hmap0.trans hν) hu had hc hb
  have hac (t : Time) : π.map (fun γ => γ t) ≪ μ :=
    Measure.absolutelyContinuous_of_le_smul (hcomp t)
  exact entropy_plan_signed_derivative_le μ ν₀ ν₁ (hmap0 ▸ hac 0) hpos he0 g hg hrep
    π hgeo hmap0 (hD.integrable (by norm_num)) K hac hconv hd


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
 theorem inverseInitialDensityPlan_restrict (π : Measure C(Time,X))
    (ρ : X → ℝ) {A : Set C(Time,X)} (hA : MeasurableSet A) :
    inverseInitialDensityPlan (π.restrict A) ρ = (inverseInitialDensityPlan π ρ).restrict A := by
  exact (restrict_withDensity hA _).symm

noncomputable def pathLogControl (g : X → ℝ) (γ : C(Time,X)) : ℝ :=
  max |g (γ 0)| (dist (γ 0) (γ 1))

 theorem pathLogControl_measurable {g : X → ℝ} (hg : Measurable g) :
    Measurable (pathLogControl g) :=
  (hg.comp (measurable_path_eval 0)).abs.max
    ((continuous_eval_const 0).dist (continuous_eval_const 1)).measurable

omit [MeasurableSpace X] [BorelSpace X] in
 theorem pathLogControl_bound {g : X → ℝ} {γ : C(Time,X)} {n : ℕ}
    (hn : |pathLogControl g γ| ≤ (n:ℝ)) :
    |g (γ 0)| ≤ (n:ℝ) ∧ dist (γ 0) (γ 1) ≤ (n:ℝ) :=
  max_le_iff.mp ((le_abs_self _).trans hn)

 theorem log_core_path_set_variation [ProperSpace X]
    (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (u ρ : SobolevSpace μ hQ)
    (hp : ∀ᵐ x ∂μ, 0 < SobolevSpace.toLp μ hQ ρ x)
    {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hlog : (fun x => Real.log (SobolevSpace.toLp μ hQ ρ x)) =ᵐ[μ] g)
    (h0 : π.map (fun γ => γ 0) = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1)) (n : ℕ) :
    Tendsto (planInitialSecant (π.restrict {γ | |pathLogControl g γ| ≤ (n:ℝ)}) g)
      (𝓝[>] (0:ℝ)) (𝓝 (-(∫γ in {γ | |pathLogControl g γ| ≤ (n:ℝ)},
        localGamma μ hQ u ρ (γ 0) ∂inverseInitialDensityPlan π (SobolevSpace.toLp μ hQ ρ)))) := by
  let A : Set C(Time,X) := {γ | |pathLogControl g γ| ≤ (n:ℝ)}
  let σ := π.restrict A
  let r := SobolevSpace.toLp μ hQ ρ
  have hA : MeasurableSet A := measurableSet_le (pathLogControl_measurable hg.continuous.measurable).abs measurable_const
  have hm : ∀ᵐ γ ∂σ, |g (γ 0)| ≤ (n:ℝ) ∧ dist (γ 0) (γ 1) ≤ (n:ℝ) :=
    (ae_restrict_mem hA).mono fun γ hn => pathLogControl_bound hn
  have hσ (s : Time) : σ.map (fun γ => γ s) ≤ C • μ := restrict_plan_compression μ π hcomp _ s
  have hrep (s : Time) : ∀ᵐ γ ∂σ, Real.log (r (γ s)) = g (γ s) :=
    ae_of_ae_map (measurable_path_eval s).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hσ s)).ae_eq hlog)
  have hpos (s : Time) : ∀ᵐ γ ∂σ, 0 < r (γ s) :=
    ae_of_ae_map (measurable_path_eval s).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hσ s)).ae_le hp)
  have hbd (s : Time) : ∀ᵐ γ ∂σ, |g (γ s)| ≤ (n:ℝ)+(L:ℝ)*(n:ℝ) := by
    filter_upwards [hm,ae_restrict_of_ae hgeo] with γ hn hγ
    have hi := lipschitz_geodesic_increment hg hγ s
    have hmul : (L:ℝ)*(s:ℝ)*dist (γ 0) (γ 1) ≤ (L:ℝ)*(n:ℝ) := by
      calc
        _ ≤ (L:ℝ)*1*dist (γ 0) (γ 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left s.property.2 L.coe_nonneg) dist_nonneg
        _ ≤ (L:ℝ)*1*(n:ℝ) := mul_le_mul_of_nonneg_left hn.2 (by positivity)
        _ = _ := by ring
    have ha := abs_add_le (g (γ s)-g (γ 0)) (g (γ 0))
    simp only [sub_add_cancel] at ha
    linarith [hn.1]
  have hlp (s : Time) : ∀ᵐ γ ∂σ, Real.exp (-((n:ℝ)+(L:ℝ)*(n:ℝ))) ≤ r (γ s) := by
    filter_upwards [hrep s,hpos s,hbd s] with γ hlog' hp' hb'
    rw [←Real.exp_log hp',hlog']
    exact Real.exp_le_exp.mpr (abs_le.mp hb').1
  have hil (s : Time) : Integrable (fun γ : C(Time,X) => Real.log (r (γ s))) σ := by
    apply (integrable_const ((n:ℝ)+(L:ℝ)*(n:ℝ))).mono'
      (((Lp.stronglyMeasurable r).measurable.comp (measurable_path_eval s)).log.aestronglyMeasurable)
    filter_upwards [hrep s,hbd s] with γ hr hb'
    simpa only [Real.norm_eq_abs,Function.comp_apply,hr] using hb'
  have hd := path_log_signed_variation μ hQ σ (ae_restrict_of_ae hgeo) hC hσ
    (hD.mono_measure Measure.restrict_le_self) (hm.mono fun γ hγ => hγ.2) u ρ
    (Real.exp_pos _) hlp hil hu had (ae_restrict_of_ae hc) (ae_restrict_of_ae hb)
  have hinit := inverseInitialDensityPlan_initial μ π (Lp.stronglyMeasurable r).measurable hp h0
  have hν : (inverseInitialDensityPlan σ r).map (fun γ => γ 0) ≤ (1:ℝ≥0∞) • μ := by
    rw [inverseInitialDensityPlan_restrict π r hA,one_smul]
    exact (Measure.map_mono Measure.restrict_le_self (measurable_path_eval 0)).trans_eq hinit
  rw [weightedGradientPair_eq_bracket μ hQ (C := 1) (by norm_num) hν,
    ←integral_localGamma μ hQ (C := 1) (by norm_num) hν] at hd
  have hΓ : Measurable (localGamma μ hQ u ρ) := by
    unfold localGamma
    fun_prop
  rw [integral_map (measurable_path_eval 0).aemeasurable hΓ.aestronglyMeasurable,
    inverseInitialDensityPlan_restrict π r hA] at hd
  apply hd.congr'
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
  exact planInitialSecant_congr_ae μ σ
    (fun s => Measure.absolutelyContinuous_of_le_smul (hσ s)) hlog ⟨ht0.le,ht1.le⟩


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem inverseInitialDensityPlan_initial_nonneg (μ : Measure X) (π : Measure C(Time,X))
    {ρ : X → ℝ} (hρ : Measurable ρ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (h0 : π.map (fun γ => γ 0) = μ.withDensity (fun x => ENNReal.ofReal (ρ x))) :
    (inverseInitialDensityPlan π ρ).map (fun γ => γ 0) = μ.restrict {x | 0 < ρ x} := by
  have hm : Measurable (fun x => ENNReal.ofReal ((ρ x)⁻¹)) := hρ.inv.ennreal_ofReal
  change (π.withDensity ((fun x => ENNReal.ofReal ((ρ x)⁻¹)) ∘ (fun γ => γ 0))).map _ = _
  rw [map_withDensity_pullback π (measurable_path_eval 0) hm, h0,
    ←withDensity_mul μ hρ.ennreal_ofReal hm]
  calc
    _ = μ.withDensity ({x | 0 < ρ x}.indicator (fun _ => (1:ℝ≥0∞))) := by
      apply withDensity_congr_ae
      filter_upwards [hp] with x hx
      by_cases hh : 0 < ρ x
      · simp only [Pi.mul_apply,
          ←ENNReal.ofReal_mul hx,mul_inv_cancel₀ hh.ne',ENNReal.ofReal_one]
        simp [hh]
      · have hz : ρ x = 0 := le_antisymm (le_of_not_gt hh) hx
        simp [hz]
    _ = _ := by
      rw [withDensity_indicator (measurableSet_lt measurable_const hρ)]
      exact withDensity_one

theorem initial_density_pos (μ : Measure X) (π : Measure C(Time,X))
    {ρ : X → ℝ} (hρ : Measurable ρ)
    (h0 : π.map (fun γ => γ 0) = μ.withDensity (fun x => ENNReal.ofReal (ρ x))) :
    ∀ᵐ γ ∂π, 0 < ρ (γ 0) := by
  have hh : ∀ᵐ x ∂π.map (fun γ => γ 0), 0 < ρ x := by
    rw [h0,ae_withDensity_iff hρ.ennreal_ofReal]
    exact ae_of_all _ fun x hx => ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hx)
  exact ae_of_ae_map (measurable_path_eval 0).aemeasurable hh

theorem initial_sqrt_inverse_integrable (μ : Measure X) (π : Measure C(Time,X))
    {h : X → ℝ} (hm : Measurable h) (_ : ∀ x, 0 ≤ h x) (hi : Integrable h μ)
    (h0 : π.map (fun γ => γ 0) = μ.withDensity (fun x => ENNReal.ofReal (h x^2))) :
    Integrable (fun γ => (h (γ 0))⁻¹) π := by
  have hid : Integrable (fun x => (h x)⁻¹) (μ.withDensity (fun x => ENNReal.ofReal (h x^2))) := by
    have he : (fun x => ENNReal.ofReal (h x^2)) = fun x => ((h x^2).toNNReal : ℝ≥0∞) := by
      funext x
      rfl
    rw [he,integrable_withDensity_iff_integrable_smul (hm.pow_const 2).real_toNNReal]
    convert hi using 1
    funext x
    rw [NNReal.smul_def,Real.coe_toNNReal _ (sq_nonneg _),smul_eq_mul]
    by_cases hz : h x = 0
    · simp [hz]
    · field_simp
  have hh : Integrable (fun x => (h x)⁻¹) (π.map (fun γ => γ 0)) := h0 ▸ hid
  exact (integrable_map_measure hm.inv.aestronglyMeasurable
    (measurable_path_eval 0).aemeasurable).mp hh



 
def squareLogControl (T : ℝ) : ℝ := 2*T*(T+2)*(T+1)^2

noncomputable def regularizedPlanLogSecant (π : Measure C(Time,X)) (h : X → ℝ) (t : ℝ) : ℝ :=
  planInitialSecant π (fun x => Real.log (h x^2+t^2)) t

omit [MeasurableSpace X] [BorelSpace X] in
theorem regularized_log_path_bound {h : X → ℝ} {L : ℝ≥0}
    (hh : LipschitzWith L h) (hn : ∀ x, 0 ≤ h x)
    {γ : C(Time,X)} (hγ : IsGeodesic γ) {D : ℝ} (hD : 0 ≤ D)
    (hγD : dist (γ 0) (γ 1) ≤ D) (hp : 0 < h (γ 0))
    (t : Time) (ht : 0 < (t:ℝ)) :
    |(Real.log (h (γ t)^2+(t:ℝ)^2)-Real.log (h (γ 0)^2+(t:ℝ)^2))/(t:ℝ)| ≤
      squareLogControl ((L:ℝ)*D) * (h (γ 0))⁻¹ := by
  have hi := lipschitz_geodesic_increment hh hγ t
  have hinc : |h (γ t)-h (γ 0)| ≤ ((L:ℝ)*D)*(t:ℝ) := by
    apply hi.trans
    nlinarith [mul_le_mul_of_nonneg_left hγD (mul_nonneg L.coe_nonneg ht.le)]
  have he := regularized_square_log_secant_bound (hn _) (hn _) ht
    (mul_nonneg L.coe_nonneg hD) hinc
  apply he.trans
  change squareLogControl ((L:ℝ)*D) / (h (γ 0)+(t:ℝ)) ≤ _
  rw [←div_eq_mul_inv]
  apply div_le_div_of_nonneg_left _ hp (by linarith)
  unfold squareLogControl
  positivity

theorem regularized_log_integrable_secant
    (π : Measure C(Time,X)) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {h : X → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) (hn : ∀ x, 0 ≤ h x)
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (hp : ∀ᵐ γ ∂π, 0 < h (γ 0))
    (hi : Integrable (fun γ => (h (γ 0))⁻¹) π)
    (t : Time) (ht : 0 < (t:ℝ)) :
    Integrable (fun γ : C(Time,X) =>
      (Real.log (h (γ t)^2+(t:ℝ)^2)-Real.log (h (γ 0)^2+(t:ℝ)^2))/(t:ℝ)) π := by
  apply (hi.const_mul (squareLogControl ((L:ℝ)*D))).mono'
  · exact ((((hh.continuous.measurable.comp (measurable_path_eval t)).pow_const 2).add
      measurable_const).log.sub (((hh.continuous.measurable.comp (measurable_path_eval 0)).pow_const 2).add
      measurable_const).log).div_const _ |>.aestronglyMeasurable
  · filter_upwards [hgeo,hb,hp] with γ hγ hb' hp'
    exact regularized_log_path_bound hh hn hγ hD hb' hp' t ht

theorem regularized_log_secant_restrict_error
    (π : Measure C(Time,X)) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {h : X → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) (hn : ∀ x, 0 ≤ h x)
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (hp : ∀ᵐ γ ∂π, 0 < h (γ 0))
    (hi : Integrable (fun γ => (h (γ 0))⁻¹) π)
    {A : Set C(Time,X)} (hA : MeasurableSet A) (t : Time) (ht : 0 < (t:ℝ)) :
    |regularizedPlanLogSecant π h t-regularizedPlanLogSecant (π.restrict A) h t| ≤
      squareLogControl ((L:ℝ)*D) * ∫γ in Aᶜ, (h (γ 0))⁻¹ ∂π := by
  have hir := regularized_log_integrable_secant π hgeo hh hn hD hb hp hi t ht
  simp only [regularizedPlanLogSecant,planInitialSecant,geodesicExtension_eq,←integral_div]
  rw [←integral_add_compl hA hir,add_sub_cancel_left]
  apply abs_integral_le_integral_abs.trans
  rw [←integral_const_mul]
  apply integral_mono_ae hir.abs.integrableOn (hi.const_mul _).integrableOn
  filter_upwards [ae_restrict_of_ae hgeo,ae_restrict_of_ae hb,ae_restrict_of_ae hp] with γ hγ hb' hp'
  exact regularized_log_path_bound hh hn hγ hD hb' hp' t ht


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem integrable_log_of_lower {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {f : Y → ℝ} (hi : Integrable f μ)
    {ε : ℝ} (hε : 0 < ε) (hl : ∀ᵐ y ∂μ, ε ≤ f y) :
    Integrable (fun y => Real.log (f y)) μ := by
  apply (hi.add (integrable_const (|Real.log ε|+1))).mono'
    (Real.measurable_log.comp_aemeasurable hi.aemeasurable).aestronglyMeasurable
  filter_upwards [hl] with y hy
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  have hh := Real.log_le_log hε hy
  have hu := Real.log_le_sub_one_of_pos (hε.trans_le hy)
  have ha := neg_abs_le (Real.log ε)
  have hb := abs_nonneg (Real.log ε)
  constructor <;> dsimp <;> linarith

omit [MeasurableSpace X] [BorelSpace X] in
theorem planInitialSecant_log_regularization_error_at
    (π : Measure C(Time,X)) [IsFiniteMeasure π] {r : X → ℝ}
    {ε : ℝ} (hε : 0 < ε) (t : Time) (ht : 0 < (t:ℝ))
    (hl0 : ∀ᵐ γ ∂π, ε ≤ r (γ 0)) (hlt : ∀ᵐ γ ∂π, ε ≤ r (γ t))
    (hi0 : Integrable (fun γ : C(Time,X) => r (γ 0)) π)
    (hit : Integrable (fun γ : C(Time,X) => r (γ t)) π) :
    |planInitialSecant π (fun x => Real.log (r x+(t:ℝ)^2)) t -
      planInitialSecant π (fun x => Real.log (r x)) t| ≤
      (2/ε * (π Set.univ).toReal) * (t:ℝ) := by
  have hil0 := integrable_log_of_lower π hi0 hε hl0
  have hilt := integrable_log_of_lower π hit hε hlt
  have hil0' := integrable_log_of_lower π (hi0.add (integrable_const ((t:ℝ)^2))) hε
    (hl0.mono fun γ hγ => hγ.trans (le_add_of_nonneg_right (sq_nonneg _)))
  have hilt' := integrable_log_of_lower π (hit.add (integrable_const ((t:ℝ)^2))) hε
    (hlt.mono fun γ hγ => hγ.trans (le_add_of_nonneg_right (sq_nonneg _)))
  simp only [Pi.add_apply] at hil0' hilt'
  have hia : Integrable (fun γ : C(Time,X) => Real.log (r (γ t)+(t:ℝ)^2)-
      Real.log (r (γ 0)+(t:ℝ)^2)) π := hilt'.sub hil0'
  have hib : Integrable (fun γ : C(Time,X) => Real.log (r (γ t))-Real.log (r (γ 0))) π :=
    hilt.sub hil0
  have hi := hia.sub hib
  have hbd : ∀ᵐ γ ∂π,
      |(Real.log (r (γ t)+(t:ℝ)^2)-Real.log (r (γ 0)+(t:ℝ)^2)) -
        (Real.log (r (γ t))-Real.log (r (γ 0)))| ≤ 2*(t:ℝ)^2/ε := by
    filter_upwards [hl0,hlt] with γ h0 ht'
    have h1 := abs_log_sub_le_div hε ht' (ht'.trans (le_add_of_nonneg_right (sq_nonneg (t:ℝ))))
    have h2 := abs_log_sub_le_div hε h0 (h0.trans (le_add_of_nonneg_right (sq_nonneg (t:ℝ))))
    simp only [add_sub_cancel_left,abs_of_nonneg (sq_nonneg (t:ℝ))] at h1 h2
    have hh := abs_add_le (Real.log (r (γ t)+(t:ℝ)^2)-Real.log (r (γ t)))
      (-(Real.log (r (γ 0)+(t:ℝ)^2)-Real.log (r (γ 0))))
    simp only [abs_neg,←sub_eq_add_neg] at hh
    have he : (Real.log (r (γ t)+(t:ℝ)^2)-Real.log (r (γ 0)+(t:ℝ)^2)) -
        (Real.log (r (γ t))-Real.log (r (γ 0))) =
        (Real.log (r (γ t)+(t:ℝ)^2)-Real.log (r (γ t))) -
        (Real.log (r (γ 0)+(t:ℝ)^2)-Real.log (r (γ 0))) := by ring
    rw [he]
    calc
      _ ≤ (t:ℝ)^2/ε+(t:ℝ)^2/ε := hh.trans (add_le_add h1 h2)
      _ = _ := by ring
  simp only [planInitialSecant,geodesicExtension_eq]
  rw [←sub_div,←integral_sub hia hib,abs_div,abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  calc
    _ ≤ ∫γ, |(Real.log (r (γ t)+(t:ℝ)^2)-Real.log (r (γ 0)+(t:ℝ)^2)) -
        (Real.log (r (γ t))-Real.log (r (γ 0)))| ∂π := abs_integral_le_integral_abs
    _ ≤ ∫_ : C(Time,X), 2*(t:ℝ)^2/ε ∂π := integral_mono_ae hi.abs (integrable_const _) hbd
    _ = _ := by simp only [integral_const,smul_eq_mul,Measure.real]; ring


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem sqrt_core_local_variation [ProperSpace X]
    (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDn : 0 ≤ D) (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (u ρ : SobolevSpace μ hQ)
    {h : X → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) (hn : ∀ x, 0 ≤ h x)
    (hrep : (SobolevSpace.toLp μ hQ ρ : X → ℝ) =ᵐ[μ] fun x => h x^2)
    {δ : ℝ} (hδ : 0 < δ) (hl : ∀ᵐ γ ∂π, δ ≤ h (γ 0))
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1)) :
    Tendsto (regularizedPlanLogSecant π h) (𝓝[>] (0:ℝ))
      (𝓝 (-weightedGradientPair μ hQ
        ((inverseInitialDensityPlan π (SobolevSpace.toLp μ hQ ρ)).map (fun γ => γ 0)) u ρ)) := by
  let r := SobolevSpace.toLp μ hQ ρ
  let T := (L:ℝ)*D
  let α := δ/(2*(T+1))
  let ε := (δ/2)^2
  have hT : 0 ≤ T := mul_nonneg L.coe_nonneg hDn
  have hα : 0 < α := by dsimp [α]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hac (s : Time) : π.map (fun γ => γ s) ≪ μ :=
    Measure.absolutelyContinuous_of_le_smul (hcomp s)
  have hrepr (s : Time) : ∀ᵐ γ ∂π, r (γ s) = h (γ s)^2 :=
    ae_of_ae_map (measurable_path_eval s).aemeasurable ((hac s).ae_eq hrep)
  have hlp (s : Time) (hs : (s:ℝ) < α) : ∀ᵐ γ ∂π, ε ≤ r (γ s) := by
    filter_upwards [hgeo,hDb,hl,hrepr s] with γ hγ hγD hγl hγr
    have hi := lipschitz_geodesic_increment hh hγ s
    have hie : (L:ℝ)*(s:ℝ)*dist (γ 0) (γ 1) ≤ T*(s:ℝ) := by
      dsimp [T]
      nlinarith [mul_le_mul_of_nonneg_left hγD (mul_nonneg L.coe_nonneg s.property.1)]
    have hst : (s:ℝ)*(2*(T+1)) < δ := (lt_div_iff₀ (by positivity)).mp hs
    have ht : T*(s:ℝ) < δ/2 := by nlinarith [s.property.1]
    have hlow : δ/2 ≤ h (γ s) := by linarith [(abs_le.mp (hi.trans hie)).1]
    rw [hγr]
    exact sq_le_sq₀ (by positivity) (hn _) |>.mpr hlow
  have hir (s : Time) : Integrable (fun γ : C(Time,X) => r (γ s)) π :=
    (compressionPullback_memLp μ π _ (measurable_path_eval s) hC (hcomp s) r).integrable (by norm_num)
  have hil (s : Time) (hs : (s:ℝ) < α) : Integrable
      (fun γ : C(Time,X) => Real.log (r (γ s))) π :=
    integrable_log_of_lower π (hir s) hε (hlp s hs)
  have hd := path_log_signed_variation_eventual μ hQ π hgeo hC hcomp hD hDb
    u ρ hε hα hlp hil hu had hc hb
  have he : Tendsto (fun t : ℝ =>
      planInitialSecant π (fun x => Real.log (r x+t^2)) t -
        planInitialSecant π (fun x => Real.log (r x)) t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun t : ℝ => (2/ε*(π Set.univ).toReal)*t)
    · have hs : ∀ᶠ t in 𝓝[>] (0:ℝ), t < min 1 α :=
        (gt_mem_nhds (lt_min zero_lt_one hα)).filter_mono nhdsWithin_le_nhds
      filter_upwards [hs,self_mem_nhdsWithin] with t ht ht0
      let s : Time := ⟨t,ht0.le,(lt_of_lt_of_le ht (min_le_left _ _)).le⟩
      have hsa : (s:ℝ) < α := lt_of_lt_of_le ht (min_le_right _ _)
      exact planInitialSecant_log_regularization_error_at π hε s ht0
        (hlp 0 hα) (hlp s hsa) (hir 0) (hir s)
    · simpa using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).mono_left
        nhdsWithin_le_nhds).const_mul (2/ε*(π Set.univ).toReal)
  have hhlim := he.add hd
  simp only [r,sub_add_cancel,zero_add] at hhlim
  apply hhlim.congr'
  have hs : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hs,self_mem_nhdsWithin] with t ht ht0
  have hr : (fun x => Real.log (r x+t^2)) =ᵐ[μ] fun x => Real.log (h x^2+t^2) :=
    hrep.mono fun x hx => by dsimp only [r]; rw [hx]
  exact planInitialSecant_congr_ae μ π hac hr ⟨ht0.le,ht.le⟩



 
theorem sqrt_core_signed_variation [ProperSpace X]
    (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDn : 0 ≤ D) (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (u ρ : SobolevSpace μ hQ)
    {h : X → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) (hn : ∀ x, 0 ≤ h x)
    (hi : Integrable h μ)
    (hrep : (SobolevSpace.toLp μ hQ ρ : X → ℝ) =ᵐ[μ] fun x => h x^2)
    (h0 : π.map (fun γ => γ 0) = μ.withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1)) :
    Tendsto (regularizedPlanLogSecant π h) (𝓝[>] (0:ℝ)) (𝓝 (-energyForm μ hQ u ρ)) := by
  let r := SobolevSpace.toLp μ hQ ρ
  let π' := inverseInitialDensityPlan π r
  let H : C(Time,X) → ℝ := fun γ => (h (γ 0))⁻¹
  have hH : Measurable H := hh.continuous.measurable.inv.comp (measurable_path_eval 0)
  have h0' : π.map (fun γ => γ 0) = μ.withDensity (fun x => ENNReal.ofReal (h x^2)) := by
    rw [h0]
    exact withDensity_congr_ae (hrep.mono fun x hx => congrArg ENNReal.ofReal hx)
  have hip : Integrable H π := initial_sqrt_inverse_integrable μ π hh.continuous.measurable hn hi h0'
  have hph : ∀ᵐ γ ∂π, 0 < h (γ 0) := by
    filter_upwards [initial_density_pos μ π (hh.continuous.measurable.pow_const 2) h0'] with γ hγ
    nlinarith [hn (γ 0)]
  have hrn : ∀ᵐ x ∂μ, 0 ≤ r x := hrep.mono fun x hx => by rw [hx]; positivity
  have hinit : π'.map (fun γ => γ 0) = μ.restrict {x | 0 < r x} :=
    inverseInitialDensityPlan_initial_nonneg μ π (Lp.stronglyMeasurable r).measurable hrn h0
  have hinit_le : π'.map (fun γ => γ 0) ≤ (1:ℝ≥0∞) • μ := by
    rw [hinit,one_smul]
    exact Measure.restrict_le_self
  have hΓ : Measurable (localGamma μ hQ u ρ) := by unfold localGamma; fun_prop
  have hiΓ : Integrable (fun γ : C(Time,X) => localGamma μ hQ u ρ (γ 0)) π' :=
    (localGamma_integrable μ hQ (C := 1) (by norm_num) hinit_le u ρ).comp_measurable (measurable_path_eval 0)
  have heΓ : (∫γ : C(Time,X), localGamma μ hQ u ρ (γ 0) ∂π') = energyForm μ hQ u ρ := by
    rw [←integral_map (measurable_path_eval 0).aemeasurable hΓ.aestronglyMeasurable,hinit,
      ←integral_indicator (measurableSet_lt measurable_const (Lp.stronglyMeasurable r).measurable)]
    have he : {x | 0 < r x}.indicator (localGamma μ hQ u ρ) =ᵐ[μ] localGamma μ hQ u ρ := by
      filter_upwards [hrn,localGamma_zero_on_level μ hQ ρ u 0,localGamma_comm μ hQ u ρ] with x hn' hz hc'
      by_cases hp : 0 < r x
      · simp [hp]
      · have hrz : r x = 0 := le_antisymm (le_of_not_gt hp) hn'
        have hgz : localGamma μ hQ u ρ x = 0 := hc'.trans (hz hrz)
        simp [hp,hgz]
    rw [integral_congr_ae he,integral_localGamma_eq_energyForm]
  let A : ℕ → Set C(Time,X) := fun n => {γ | |H γ| ≤ (n:ℝ)}
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le hH.abs measurable_const
  have hloc (n : ℕ) : Tendsto (regularizedPlanLogSecant (π.restrict (A n)) h)
      (𝓝[>] (0:ℝ)) (𝓝 (-(∫γ in A n, localGamma μ hQ u ρ (γ 0) ∂π'))) := by
    let σ := π.restrict (A n)
    have hσ (s : Time) : σ.map (fun γ => γ s) ≤ C • μ := restrict_plan_compression μ π hcomp (A n) s
    have hl : ∀ᵐ γ ∂σ, (1:ℝ)/((n:ℝ)+1) ≤ h (γ 0) := by
      filter_upwards [ae_restrict_of_ae hph,ae_restrict_mem (hA n)] with γ hp hγ
      have hinv : (h (γ 0))⁻¹ ≤ (n:ℝ)+1 := by
        have hh' := (le_abs_self (H γ)).trans hγ
        dsimp [H] at hh'
        linarith
      have hnpos : 0 < (n:ℝ)+1 := by positivity
      have hmul : 1 ≤ ((n:ℝ)+1)*h (γ 0) := by
        have he := mul_le_mul_of_nonneg_right hinv hp.le
        rwa [inv_mul_cancel₀ hp.ne'] at he
      exact (div_le_iff₀ hnpos).mpr (by nlinarith)
    have hd := sqrt_core_local_variation μ hQ σ (ae_restrict_of_ae hgeo) hC hσ
      (hD.mono_measure Measure.restrict_le_self) hDn (ae_restrict_of_ae hDb) u ρ hh hn hrep
      (by positivity : 0 < (1:ℝ)/((n:ℝ)+1)) hl hu had (ae_restrict_of_ae hc) (ae_restrict_of_ae hb)
    have hν : (inverseInitialDensityPlan σ r).map (fun γ => γ 0) ≤ (1:ℝ≥0∞) • μ := by
      rw [inverseInitialDensityPlan_restrict π r (hA n)]
      exact (Measure.map_mono Measure.restrict_le_self (measurable_path_eval 0)).trans hinit_le
    rw [weightedGradientPair_eq_bracket μ hQ (C := 1) (by norm_num) hν,
      ←integral_localGamma μ hQ (C := 1) (by norm_num) hν] at hd
    rw [integral_map (measurable_path_eval 0).aemeasurable hΓ.aestronglyMeasurable,
      inverseInitialDensityPlan_restrict π r (hA n)] at hd
    exact hd
  apply tendsto_of_uniform_secant_tails
    (fₙ := fun n => regularizedPlanLogSecant (π.restrict (A n)) h)
    (cₙ := fun n => -(∫γ in A n, localGamma μ hQ u ρ (γ 0) ∂π'))
    (eₙ := fun n => squareLogControl ((L:ℝ)*D)*∫γ in (A n)ᶜ, H γ ∂π)
  · simpa only [heΓ] using (tendsto_integral_log_levels π' hH hiΓ).neg
  · simpa only [mul_zero] using (tendsto_integral_compl_log_levels π hH hip).const_mul
      (squareLogControl ((L:ℝ)*D))
  · exact hloc
  · intro n
    have hs : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
      (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
    filter_upwards [hs,self_mem_nhdsWithin] with t ht ht0
    exact regularized_log_secant_restrict_error π hgeo hh hn hDn hDb hph hip (hA n)
      ⟨t,ht0.le,ht.le⟩ ht0



 
theorem entropy_regularized_plan_secant (μ : Measure X) [SigmaFinite μ]
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀]
    (r : Lp ℝ 2 μ) {h : X → ℝ} (_ : Measurable h)
    (hr : (r : X → ℝ) =ᵐ[μ] fun x => h x^2)
    (hrn : (fun x => h x^2) =ᵐ[μ] fun x => (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hmap0 : π.map (fun γ => γ 0) = ν₀)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (hs : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B)
    (K : ℝ) (t : Time) (ht : 0 < (t:ℝ))
    (het : Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
      Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ)
    (hc : boltzmannEntropy μ (π.map (fun γ => γ t)) ≤
      (1-(t:ℝ))*boltzmannEntropy μ ν₀+(t:ℝ)*boltzmannEntropy μ ν₁+
      ((-K)*(t:ℝ)*(1-(t:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂π)) :
    regularizedPlanLogSecant π h t ≤ boltzmannEntropy μ ν₁ - boltzmannEntropy μ ν₀ -
      (K*(1-(t:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂π) + (t:ℝ)*(μ B).toReal := by
  have hν (s : Time) : π.map (fun γ => γ s) ≪ μ :=
    Measure.absolutelyContinuous_of_le_smul (hcomp s)
  have hνB (s : Time) : π.map (fun γ => γ s) ≪ μ.restrict B :=
    Measure.absolutelyContinuous_of_le_smul ((compression_iff_localized μ _ (hs s) C).mp (hcomp s))
  have hi (s : Time) : Integrable (fun x => h x^2) (π.map (fun γ => γ s)) := by
    let : IsProbabilityMeasure (π.map (fun γ => γ s)) :=
      inferInstance
    exact ((Lp.memLp r).of_measure_le_smul hC (hcomp s)).integrable (by norm_num) |>.congr (hν s |>.ae_eq hr)
  have hil (s : Time) : Integrable (fun x => Real.log (h x^2+(t:ℝ)^2)) (π.map (fun γ => γ s)) := by
    let : IsProbabilityMeasure (π.map (fun γ => γ s)) :=
      inferInstance
    exact integrable_log_of_lower _ ((hi s).add (integrable_const _)) (sq_pos_of_pos ht)
      (Eventually.of_forall fun x => by nlinarith [sq_nonneg (h x)])
  have hip (s : Time) : Integrable (fun γ : C(Time,X) => Real.log (h (γ s)^2+(t:ℝ)^2)) π :=
    (hil s).comp_measurable (measurable_path_eval s)
  let : IsProbabilityMeasure (π.map (fun γ => γ t)) :=
    inferInstance
  have hg := entropy_regularized_subgradient_localized μ ν₀ (π.map (fun γ => γ t)) hB
    (hmap0 ▸ hνB 0) (hνB t) he0 het (sq_pos_of_pos ht) _ hrn (hmap0 ▸ hil 0) (hil t)
  have he (s : Time) : (∫γ : C(Time,X), Real.log (h (γ s)^2+(t:ℝ)^2) ∂π) =
      ∫x, Real.log (h x^2+(t:ℝ)^2) ∂π.map (fun γ => γ s) :=
    (integral_map (measurable_path_eval s).aemeasurable (hil s).aestronglyMeasurable).symm
  simp only [regularizedPlanLogSecant,planInitialSecant,geodesicExtension_eq]
  rw [integral_sub (hip t) (hip 0),he t,he 0,hmap0]
  apply (div_le_iff₀ ht).mpr
  nlinarith only [hg,hc]

theorem entropy_regularized_plan_derivative_le (μ : Measure X) [SigmaFinite μ]
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀]
    (r : Lp ℝ 2 μ) {h : X → ℝ} (hh : Measurable h)
    (hr : (r : X → ℝ) =ᵐ[μ] fun x => h x^2)
    (hrn : (fun x => h x^2) =ᵐ[μ] fun x => (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hmap0 : π.map (fun γ => γ 0) = ν₀)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (hs : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B)
    (K : ℝ)
    (hconv : ∀ t : Time,
      Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
        Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ ∧
      boltzmannEntropy μ (π.map (fun γ => γ t)) ≤
        (1-(t:ℝ))*boltzmannEntropy μ ν₀+(t:ℝ)*boltzmannEntropy μ ν₁+
        ((-K)*(t:ℝ)*(1-(t:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂π))
    {d : ℝ} (hd : Tendsto (regularizedPlanLogSecant π h) (𝓝[>] (0:ℝ)) (𝓝 d)) :
    d ≤ boltzmannEntropy μ ν₁ - boltzmannEntropy μ ν₀ -
      (K/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂π) := by
  have hl : Tendsto (fun t : ℝ => boltzmannEntropy μ ν₁-boltzmannEntropy μ ν₀-
      (K*(1-t)/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂π)+t*(μ B).toReal)
      (𝓝[>] (0:ℝ)) (𝓝 (boltzmannEntropy μ ν₁-boltzmannEntropy μ ν₀-
      (K/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂π))) := by
    have hc : Continuous (fun t : ℝ => boltzmannEntropy μ ν₁-boltzmannEntropy μ ν₀-
      (K*(1-t)/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂π)+t*(μ B).toReal) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hd hl
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
  exact entropy_regularized_plan_secant μ ν₀ ν₁ r hh hr hrn he0 π hmap0 hC hcomp
    hB hs K ⟨t,ht0.le,ht1.le⟩ ht0 (hconv _).1 (hconv _).2


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

noncomputable def setRetraction {S : Set X} (p : S) (x : X) : S := by
  classical
  exact ⟨if x ∈ S then x else p, by split_ifs with h; exact h; exact p.property⟩

omit [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
 theorem setRetraction_val_of_mem {S : Set X} (p : S) {x : X} (hx : x ∈ S) :
    (setRetraction p x : X) = x := by simp [setRetraction,hx]

omit [MetricSpace X] [SecondCountableTopology X] [BorelSpace X] in
 theorem setRetraction_measurable {S : Set X} (hS : MeasurableSet S) (p : S) :
    Measurable (setRetraction p) := by
  classical
  exact (measurable_id.ite hS measurable_const).subtype_mk

omit [MetricSpace X] [SecondCountableTopology X] [BorelSpace X] in
 theorem map_setRetraction_val {S : Set X} (hS : MeasurableSet S) (p : S)
    {ν : Measure X} (hν : ∀ᵐ x ∂ν, x ∈ S) :
    (ν.map (setRetraction p)).map (fun x : S => (x:X)) = ν := by
  rw [Measure.map_map measurable_subtype_coe (setRetraction_measurable hS p)]
  calc
    _ = ν.map id := Measure.map_congr (hν.mono fun x hx => setRetraction_val_of_mem p hx)
    _ = ν := Measure.map_id

omit [MetricSpace X] [SecondCountableTopology X] [BorelSpace X] in
 theorem map_pair_setRetraction_val {S : Set X} (hS : MeasurableSet S) (p : S)
    {π : Measure (X×X)} (hπ : ∀ᵐ xy ∂π, xy.1 ∈ S ∧ xy.2 ∈ S) :
    (π.map (fun xy => (setRetraction p xy.1,setRetraction p xy.2))).map
      (fun xy : S×S => ((xy.1:X),(xy.2:X))) = π := by
  rw [Measure.map_map (g := fun xy : S×S => ((xy.1:X),(xy.2:X)))
    (f := fun xy : X×X => (setRetraction p xy.1,setRetraction p xy.2))
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd))
    (((setRetraction_measurable hS p).comp measurable_fst).prodMk
      ((setRetraction_measurable hS p).comp measurable_snd))]
  calc
    _ = π.map id := Measure.map_congr (hπ.mono fun xy hxy => by
      simp only [Function.comp_apply,id_eq,setRetraction_val_of_mem p hxy.1,
        setRetraction_val_of_mem p hxy.2])
    _ = π := Measure.map_id

 theorem transportCost_subtype_map {S : Set X} (π : Measure (S×S)) :
    transportCost (π.map (fun xy : S×S => ((xy.1:X),(xy.2:X)))) = transportCost π := by
  unfold transportCost
  exact lintegral_map ((measurable_fst.dist measurable_snd).ennreal_ofReal.pow_const 2)
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd))

 theorem IsOptimalCoupling.retract_to_set {ν₀ ν₁ : Measure X}
    {π : Measure (X×X)} (hp : IsOptimalCoupling ν₀ ν₁ π)
    {S : Set X} (hS : MeasurableSet S) (p : S)
    (h₀ : ∀ᵐ x ∂ν₀, x ∈ S) (h₁ : ∀ᵐ x ∂ν₁, x ∈ S) :
    IsOptimalCoupling (ν₀.map (setRetraction p)) (ν₁.map (setRetraction p))
      (π.map (fun xy => (setRetraction p xy.1,setRetraction p xy.2))) := by
  have hm := setRetraction_measurable hS p
  have hmp : Measurable (fun xy : X×X => (setRetraction p xy.1,setRetraction p xy.2)) :=
    (hm.comp measurable_fst).prodMk (hm.comp measurable_snd)
  have hemb : Measurable (fun xy : S×S => ((xy.1:X),(xy.2:X))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  have hf : (π.map (fun xy => (setRetraction p xy.1,setRetraction p xy.2))).map Prod.fst =
      ν₀.map (setRetraction p) := by
    rw [Measure.map_map measurable_fst hmp]
    rw [←hp.1,Measure.map_map hm measurable_fst]
    rfl
  have hs : (π.map (fun xy => (setRetraction p xy.1,setRetraction p xy.2))).map Prod.snd =
      ν₁.map (setRetraction p) := by
    rw [Measure.map_map measurable_snd hmp]
    rw [←hp.2.1,Measure.map_map hm measurable_snd]
    rfl
  refine ⟨hf,hs,?_⟩
  intro π' hf' hs'
  have hπS : ∀ᵐ xy ∂π, xy.1 ∈ S ∧ xy.2 ∈ S := by
    have h₀' : ∀ᵐ xy ∂π, xy.1 ∈ S := (ae_map_iff measurable_fst.aemeasurable hS).mp (by
      change ∀ᵐ x ∂π.map Prod.fst, x ∈ S
      rw [hp.1]
      exact h₀)
    have h₁' : ∀ᵐ xy ∂π, xy.2 ∈ S := (ae_map_iff measurable_snd.aemeasurable hS).mp (by
      change ∀ᵐ x ∂π.map Prod.snd, x ∈ S
      rw [hp.2.1]
      exact h₁)
    filter_upwards [h₀',h₁'] with xy hx hy
    exact ⟨hx,hy⟩
  have hfLift : (π'.map (fun xy : S×S => ((xy.1:X),(xy.2:X)))).map Prod.fst = ν₀ := by
    rw [Measure.map_map measurable_fst hemb]
    change π'.map ((fun x : S => (x:X)) ∘ Prod.fst) = _
    rw [←Measure.map_map measurable_subtype_coe measurable_fst,hf',map_setRetraction_val hS p h₀]
  have hsLift : (π'.map (fun xy : S×S => ((xy.1:X),(xy.2:X)))).map Prod.snd = ν₁ := by
    rw [Measure.map_map measurable_snd hemb]
    change π'.map ((fun x : S => (x:X)) ∘ Prod.snd) = _
    rw [←Measure.map_map measurable_subtype_coe measurable_snd,hs',map_setRetraction_val hS p h₁]
  have hh := hp.2.2 _ hfLift hsLift
  rw [transportCost_subtype_map] at hh
  rw [←map_pair_setRetraction_val hS p hπS,transportCost_subtype_map] at hh
  exact hh


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X]

theorem clipped_distance_square_lipschitz (p : X) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith ⟨R,hR⟩ (fun x => (min R (dist p x))^2/2) := by
  have hclip : LipschitzWith 1 (fun x => min R (dist p x)) :=
    (LipschitzWith.dist_right p).const_min R
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx0 : 0 ≤ min R (dist p x) := le_min hR dist_nonneg
  have hy0 : 0 ≤ min R (dist p y) := le_min hR dist_nonneg
  have hxR := min_le_left R (dist p x)
  have hyR := min_le_left R (dist p y)
  have hd := hclip.dist_le_mul x y
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,abs_le] at hd
  have hs0 : 0 ≤ min R (dist p x)+min R (dist p y) := add_nonneg hx0 hy0
  have h1 := mul_le_mul_of_nonneg_right hd.1 hs0
  have h2 := mul_le_mul_of_nonneg_right hd.2 hs0
  have h3 := mul_le_mul_of_nonneg_left (add_le_add hxR hyR) (dist_nonneg (x := x) (y := y))
  rw [Real.dist_eq,abs_le]
  change -(R*dist x y) ≤ _ ∧ _ ≤ R*dist x y
  constructor <;> nlinarith only [h1,h2,h3]

theorem truncated_squared_distance_eq_clip (p : X) {R M a : ℝ}
    (hR : 0 ≤ R) (hcut : M+a ≤ R^2/2) (x : X) :
    min M (dist p x^2/2-a) = min M ((min R (dist p x))^2/2-a) := by
  by_cases hx : dist p x ≤ R
  · rw [min_eq_right hx]
  · have hRx := le_of_lt (lt_of_not_ge hx)
    have hsq := sq_le_sq₀ hR dist_nonneg |>.mpr hRx
    rw [min_eq_left hRx, min_eq_left (by linarith : M ≤ dist p x^2/2-a),
      min_eq_left (by linarith : M ≤ R^2/2-a)]

theorem truncated_squared_distance_lipschitz (p : X) {R M a : ℝ}
    (hR : 0 ≤ R) (hcut : M+a ≤ R^2/2) :
    LipschitzWith ⟨R,hR⟩ (fun x => min M (dist p x^2/2-a)) := by
  have h : LipschitzWith ⟨R,hR⟩ (fun x => (min R (dist p x))^2/2-a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_sub_right]
    exact (clipped_distance_square_lipschitz p hR).dist_le_mul x y
  have hh := h.const_min M
  convert hh using 1
  funext x
  exact truncated_squared_distance_eq_clip p hR hcut x

noncomputable def truncatedCostTransform {S : Set X} (a : S → ℝ) (M : ℝ) (y : X) : ℝ :=
  sInf (range (fun x : S => min M (dist (x:X) y^2/2-a x)))

theorem truncatedCostTransform_bdd {S : Set X} {a : S → ℝ} {M A : ℝ}
    (ha : ∀ x, a x ≤ A) (y : X) :
    BddBelow (range (fun x : S => min M (dist (x:X) y^2/2-a x))) := by
  refine ⟨min M (-A),?_⟩
  rintro _ ⟨x,rfl⟩
  exact min_le_min_left M (by nlinarith [sq_nonneg (dist (x:X) y),ha x])

theorem truncatedCostTransform_le_cost {S : Set X} {a : S → ℝ} {M A : ℝ}
    (ha : ∀ x, a x ≤ A) (x : S) (y : X) :
    truncatedCostTransform a M y ≤ dist (x:X) y^2/2-a x :=
  (csInf_le (truncatedCostTransform_bdd ha y) (mem_range_self x)).trans (min_le_right _ _)

theorem truncatedCostTransform_le {S : Set X} [Nonempty S] {a : S → ℝ} {M A : ℝ}
    (ha : ∀ x, a x ≤ A) (y : X) : truncatedCostTransform a M y ≤ M := by
  obtain ⟨x⟩ := ‹Nonempty S›
  exact (csInf_le (truncatedCostTransform_bdd ha y) (mem_range_self x)).trans (min_le_left _ _)

theorem le_truncatedCostTransform {S : Set X} [Nonempty S] {a : S → ℝ} {M b : ℝ}
    (y : X) (hM : b ≤ M) (h : ∀ x : S, b ≤ dist (x:X) y^2/2-a x) :
    b ≤ truncatedCostTransform a M y := by
  apply le_csInf (range_nonempty _)
  rintro _ ⟨x,rfl⟩
  exact le_min hM (h x)

theorem truncatedCostTransform_lipschitz {S : Set X} [Nonempty S]
    {a : S → ℝ} {M A R : ℝ} (ha : ∀ x, a x ≤ A)
    (hR : 0 ≤ R) (hcut : M+A ≤ R^2/2) :
    LipschitzWith ⟨R,hR⟩ (truncatedCostTransform a M) := by
  have hf (x : S) : LipschitzWith ⟨R,hR⟩
      (fun y : X => min M (dist (x:X) y^2/2-a x)) :=
    truncated_squared_distance_lipschitz (x:X) hR (by linarith [ha x])
  have hle (x y : X) : truncatedCostTransform a M x ≤
      truncatedCostTransform a M y + R*dist x y := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨v,hv,happrox⟩ := exists_lt_of_csInf_lt (range_nonempty _)
      (lt_add_of_pos_right (truncatedCostTransform a M y) hε)
    obtain ⟨z,rfl⟩ := hv
    have h1 := csInf_le (truncatedCostTransform_bdd (M := M) ha x) (mem_range_self z)
    have h2 := (hf z).dist_le_mul x y
    rw [Real.dist_eq,abs_le] at h2
    change truncatedCostTransform a M x ≤ _ at h1
    change -(R*dist x y) ≤ _ ∧ _ ≤ R*dist x y at h2
    linarith [h2.2]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,abs_le]
  have hxy := hle x y
  have hyx := hle y x
  rw [dist_comm y x] at hyx
  change -(R*dist x y) ≤ _ ∧ _ ≤ R*dist x y
  constructor <;> linarith

theorem truncatedCostTransform_eq_const_outside {S : Set X} [Nonempty S]
    {a : S → ℝ} {M A R B : ℝ} (ha : ∀ x, a x ≤ A)
    (hR : 0 ≤ R) (hcut : M+A ≤ R^2/2) (p : X)
    (hS : ∀ x : S, dist p x ≤ B) {y : X} (hy : B+R ≤ dist p y) :
    truncatedCostTransform a M y = M := by
  apply le_antisymm (truncatedCostTransform_le ha y)
  apply le_truncatedCostTransform y le_rfl
  intro x
  have ht := dist_triangle p (x:X) y
  have hRx : R ≤ dist (x:X) y := by linarith [hS x]
  have hsq := sq_le_sq₀ hR dist_nonneg |>.mpr hRx
  linarith [ha x]


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [ProperSpace X]
  {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
  (p : X) (R : ℝ) (hzero : ∀ x, R < dist p x → f x = 0)

include hf hzero in
 theorem hopfRadius_zero_outside {t : ℝ} (ht : 0 < t) {x : X}
    (hx : R+2*t*(L:ℝ) < dist p x) : hopfRadius f t x = 0 := by
  obtain ⟨y,hy,he⟩ := hopfRadius_attained hf ht x
  have hd := hopfLax_minimizer_dist hf ht hy
  have hyR : R < dist p y := by
    linarith [dist_triangle p y x, dist_comm y x]
  have hq := hopfLax_zero_outside hf p R hzero ht hx
  change hopfLax f t x = f y + dist x y^2/(2*t) at hy
  rw [hq,hzero y hyR,zero_add] at hy
  have hdist : dist x y = 0 := by
    have hh : dist x y^2 = 0 := (div_eq_zero_iff).mp hy.symm |>.resolve_right (by positivity)
    nlinarith [dist_nonneg (x := x) (y := y)]
  exact he.trans hdist

include hf hzero in
 theorem hopfLeftRadius_zero_outside {x : X}
    (hx : R+2*(L:ℝ) < dist p x) : hopfLeftRadius f x = 0 := by
  have hz (n : ℕ) : hopfRadius f (hopfLeftTime n) x = 0 := by
    apply hopfRadius_zero_outside hf p R hzero (hopfLeftTime_pos n)
    have ht := (hopfLeftTime_bounds n).2
    nlinarith [L.coe_nonneg]
  unfold hopfLeftRadius
  simp only [hz,ciSup_const]

include hf hzero in
 theorem hopfScaledRadius_zero_outside (n : ℕ) {x : X}
    (hx : R+2*(L:ℝ) < dist p x) : hopfRadius f (hopfLeftTime n) x/hopfLeftTime n = 0 := by
  have ht := (hopfLeftTime_bounds n).2
  rw [hopfRadius_zero_outside hf p R hzero (hopfLeftTime_pos n)
    (by nlinarith [L.coe_nonneg]),zero_div]

include hf hzero in
 theorem hopfLeftLax_zero_outside (n : ℕ) {x : X}
    (hx : R+2*(L:ℝ) < dist p x) : hopfLax f (hopfLeftTime n) x = 0 := by
  apply hopfLax_zero_outside hf p R hzero (hopfLeftTime_pos n)
  have ht := (hopfLeftTime_bounds n).2
  nlinarith [L.coe_nonneg]


end

 
section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X)
  (p : X) (R : ℝ) (hzero : ∀ x, R < dist p x → f x = 0)

include hf hgeo in
omit [MeasurableSpace X] [BorelSpace X] in
 theorem hopfScaledRadius_bounds_proper (n : ℕ) (x : X) :
    0 ≤ hopfRadius f (hopfLeftTime n) x/hopfLeftTime n ∧
    hopfRadius f (hopfLeftTime n) x/hopfLeftTime n ≤ L := by
  constructor
  · exact div_nonneg (hopfRadius_bounds hf (hopfLeftTime_pos n) x).1 (hopfLeftTime_pos n).le
  · exact (div_le_iff₀ (hopfLeftTime_pos n)).mpr (by
      simpa only [mul_comm] using hopfRadius_le_sharp hf hgeo (hopfLeftTime_pos n) x)

include hf hgeo hzero in
 theorem hopfLeftRadius_memLp_proper : MemLp (hopfLeftRadius f) 2 μ := by
  have hi := memLp_indicator_const (μ := μ) 2 measurableSet_closedBall (L:ℝ)
    (Or.inr (isCompact_closedBall p (R+2*(L:ℝ))).measure_lt_top.ne)
  apply hi.mono' (hopfLeftRadius_measurable hf).aestronglyMeasurable
  refine Eventually.of_forall fun x => ?_
  by_cases hx : x ∈ closedBall p (R+2*(L:ℝ))
  · rw [indicator_of_mem hx,Real.norm_eq_abs,abs_of_nonneg (hopfLeftRadius_bounds hf hgeo x).1]
    exact (hopfLeftRadius_bounds hf hgeo x).2
  · rw [indicator_of_notMem hx,hopfLeftRadius_zero_outside hf p R hzero
      (by simpa only [mem_closedBall,dist_comm,not_le] using hx),norm_zero]

include hf hgeo hzero in
 theorem hopfScaledRadius_memLp_proper (n : ℕ) :
    MemLp (fun x => hopfRadius f (hopfLeftTime n) x/hopfLeftTime n) 2 μ := by
  have hi := memLp_indicator_const (μ := μ) 2 measurableSet_closedBall (L:ℝ)
    (Or.inr (isCompact_closedBall p (R+2*(L:ℝ))).measure_lt_top.ne)
  apply hi.mono' ((hopfRadius_measurable hf (hopfLeftTime_pos n)).div_const _).aestronglyMeasurable
  refine Eventually.of_forall fun x => ?_
  by_cases hx : x ∈ closedBall p (R+2*(L:ℝ))
  · rw [indicator_of_mem hx,Real.norm_eq_abs,abs_of_nonneg (hopfScaledRadius_bounds_proper hf hgeo n x).1]
    exact (hopfScaledRadius_bounds_proper hf hgeo n x).2
  · rw [indicator_of_notMem hx,hopfScaledRadius_zero_outside hf p R hzero n
      (by simpa only [mem_closedBall,dist_comm,not_le] using hx),norm_zero]

include hf hgeo hzero in
 theorem hopfScaledRadius_toLp_tendsto_proper :
    Tendsto (fun n => (hopfScaledRadius_memLp_proper μ hf hgeo p R hzero n).toLp
      (fun x => hopfRadius f (hopfLeftTime n) x/hopfLeftTime n)) atTop
      (𝓝 ((hopfLeftRadius_memLp_proper μ hf hgeo p R hzero).toLp (hopfLeftRadius f))) := by
  apply L2Differentiation.toLp_tendsto_of_dominated μ _ _
    ((closedBall p (R+2*(L:ℝ))).indicator (fun _ => (L:ℝ)^2))
    ((integrableOn_const (C := (L:ℝ)^2)
      (isCompact_closedBall p (R+2*(L:ℝ))).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall)
  · exact Eventually.of_forall (fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ closedBall p (R+2*(L:ℝ))
      · rw [indicator_of_mem hx]
        have ha := hopfScaledRadius_bounds_proper hf hgeo n x
        have hb := hopfLeftRadius_bounds hf hgeo x
        nlinarith [sq_nonneg ((hopfRadius f (hopfLeftTime n) x/hopfLeftTime n)-hopfLeftRadius f x)]
      · have hx' : R+2*(L:ℝ) < dist p x := by simpa only [mem_closedBall,dist_comm,not_le] using hx
        rw [indicator_of_notMem hx,hopfScaledRadius_zero_outside hf p R hzero n hx',
          hopfLeftRadius_zero_outside hf p R hzero hx']
        norm_num)
  · exact Eventually.of_forall (fun x => by
      have hh := (hopfLeftRadius_tendsto hf hgeo x).div hopfLeftTime_tendsto (by norm_num : (1:ℝ) ≠ 0)
      change Tendsto (fun n => hopfRadius f (hopfLeftTime n) x/hopfLeftTime n) atTop
        (𝓝 (hopfLeftRadius f x/1)) at hh
      simpa only [div_one] using hh)

include hf hgeo hzero in
 theorem hopfLeft_toLp_tendsto_proper :
    Tendsto (fun n => ((hopfLax_continuous hf (hopfLeftTime_pos n)).memLp_of_hasCompactSupport
      (hopfLax_hasCompactSupport hf p R hzero (hopfLeftTime_pos n)) (p := 2) (μ := μ)).toLp
      (hopfLax f (hopfLeftTime n))) atTop
      (𝓝 (((hopfLax_continuous hf (show (0:ℝ) < 1 by norm_num)).memLp_of_hasCompactSupport
        (hopfLax_hasCompactSupport hf p R hzero (by norm_num : (0:ℝ) < 1))
        (p := 2) (μ := μ)).toLp (hopfLax f 1))) := by
  have hb (n : ℕ) (x : X) : |hopfLax f (hopfLeftTime n) x-hopfLax f 1 x| ≤ (L:ℝ)^2 := by
    have hh := hopfLax_time_difference_sharp hf hgeo (show (0:ℝ) < 1 by norm_num) (hopfLeftTime_pos n) x
    have ht := hopfLeftTime_bounds n
    rw [abs_of_nonpos (by linarith : hopfLeftTime n-1 ≤ 0)] at hh
    have hmul := mul_le_mul_of_nonneg_left (show -(hopfLeftTime n-1) ≤ 1 by linarith) (sq_nonneg (L:ℝ))
    nlinarith
  apply L2Differentiation.toLp_tendsto_of_dominated μ _ _
    ((closedBall p (R+2*(L:ℝ))).indicator (fun _ => ((L:ℝ)^2)^2))
    ((integrableOn_const (C := ((L:ℝ)^2)^2)
      (isCompact_closedBall p (R+2*(L:ℝ))).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall)
  · exact Eventually.of_forall (fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ closedBall p (R+2*(L:ℝ))
      · rw [indicator_of_mem hx]
        have hs := (sq_le_sq₀ (abs_nonneg _) (sq_nonneg _)).mpr (hb n x)
        simpa only [sq_abs] using hs
      · have hx' : R+2*(L:ℝ) < dist p x := by simpa only [mem_closedBall,dist_comm,not_le] using hx
        rw [indicator_of_notMem hx,hopfLeftLax_zero_outside hf p R hzero n hx',
          hopfLax_zero_outside hf p R hzero (show (0:ℝ) < 1 by norm_num) (by simpa using hx')]
        norm_num)
  · refine Eventually.of_forall fun x => ?_
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hzero' : Tendsto (fun n => (L:ℝ)^2/2*|hopfLeftTime n-1|) atTop (𝓝 (0:ℝ)) := by
      simpa only [Pi.mul_apply,Pi.sub_apply,sub_self,abs_zero,mul_zero] using
        ((tendsto_const_nhds (x := (L:ℝ)^2/2)).mul
          ((hopfLeftTime_tendsto.sub (tendsto_const_nhds (x := (1:ℝ)))).abs))
    apply squeeze_zero (fun _ => dist_nonneg) _ hzero'
    intro n
    simpa only [Real.dist_eq] using
      hopfLax_time_difference_sharp hf hgeo (show (0:ℝ) < 1 by norm_num) (hopfLeftTime_pos n) x

include hf hgeo hzero in
 theorem hopfLeftRadius_isRelaxed_proper :
    IsRelaxedSlope μ
      (((hopfLax_continuous hf (show (0:ℝ) < 1 by norm_num)).memLp_of_hasCompactSupport
        (hopfLax_hasCompactSupport hf p R hzero (show (0:ℝ) < 1 by norm_num))
        (p := 2) (μ := μ)).toLp (hopfLax f 1))
      ((hopfLeftRadius_memLp_proper μ hf hgeo p R hzero).toLp (hopfLeftRadius f)) := by
  refine ⟨fun n => ((hopfLax_continuous hf (hopfLeftTime_pos n)).memLp_of_hasCompactSupport
    (hopfLax_hasCompactSupport hf p R hzero (hopfLeftTime_pos n)) (p := 2) (μ := μ)).toLp
      (hopfLax f (hopfLeftTime n)),
    fun n => hopfLax f (hopfLeftTime n),
    fun n => (hopfScaledRadius_memLp_proper μ hf hgeo p R hzero n).toLp
      (fun x => hopfRadius f (hopfLeftTime n) x/hopfLeftTime n),
    fun n => ⟨L,hopfLax_lipschitz hf hgeo (hopfLeftTime_pos n)⟩,?_,?_,
    hopfLeft_toLp_tendsto_proper μ hf hgeo p R hzero,
    hopfScaledRadius_toLp_tendsto_proper μ hf hgeo p R hzero⟩
  · intro n
    exact MemLp.coeFn_toLp _
  · intro n
    filter_upwards [(hopfScaledRadius_memLp_proper μ hf hgeo p R hzero n).coeFn_toLp] with x hx
    rw [hx]
    exact ⟨(hopfScaledRadius_bounds_proper hf hgeo n x).1,hopfLax_slope_le hf (hopfLeftTime_pos n) x⟩


end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)
 theorem hopfLeftRadius_minimalSlope_bound_proper {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X)
    (p : X) (R : ℝ) (hzero : ∀ x, R < dist p x → f x = 0) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ
      (SobolevSpace.ofLipschitzCompact μ hQ
        (hopfLax_lipschitz hf hgeo (show (0:ℝ) < 1 by norm_num))
        (hopfLax_hasCompactSupport hf p R hzero (by norm_num : (0:ℝ) < 1))) x ≤ hopfLeftRadius f x := by
  let u := SobolevSpace.ofLipschitzCompact μ hQ
    (hopfLax_lipschitz hf hgeo (show (0:ℝ) < 1 by norm_num))
    (hopfLax_hasCompactSupport hf p R hzero (by norm_num : (0:ℝ) < 1))
  have he : SobolevSpace.toLp μ hQ u =
      ((hopfLax_continuous hf (show (0:ℝ) < 1 by norm_num)).memLp_of_hasCompactSupport
        (hopfLax_hasCompactSupport hf p R hzero (by norm_num : (0:ℝ) < 1)) (p := 2) (μ := μ)).toLp (hopfLax f 1) := by
    apply Lp.ext
    exact (SobolevSpace.ofLipschitzCompact_coe μ hQ _ _).trans (MemLp.coeFn_toLp _).symm
  have hr := hopfLeftRadius_isRelaxed_proper μ hf hgeo p R hzero
  rw [←he] at hr
  have hle := (Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_le μ hQ u hr)
  filter_upwards [hle,(hopfLeftRadius_memLp_proper μ hf hgeo p R hzero).coeFn_toLp] with x hx heq
  exact hx.trans_eq heq


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

 theorem IsOptimalCoupling.bounded_sobolev_potential
    (hgeo : IsGeodesicSpace X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] (hac : ν₀ ≪ μ)
    {π : Measure (X×X)} (hp : IsOptimalCoupling ν₀ ν₁ π)
    (p : X) {B : ℝ} (hB : 0 ≤ B)
    (h₀ : ∀ᵐ x ∂ν₀, x ∈ closedBall p B) (h₁ : ∀ᵐ x ∂ν₁, x ∈ closedBall p B) :
    ∃ (u : SobolevSpace μ hQ) (φ ψ : X → ℝ) (L : ℝ≥0),
      LipschitzWith L φ ∧ LipschitzWith L ψ ∧ HasCompactSupport φ ∧ HasCompactSupport ψ ∧
      (φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ xy ∂π, φ xy.1+ψ xy.2 = dist xy.1 xy.2^2/2) ∧
      (∀ᵐ xy ∂π, SobolevSpace.minimalSlope μ hQ u xy.1 ≤ dist xy.1 xy.2) := by
  let S := closedBall p B
  let pS : S := ⟨p,by simpa only [S,mem_closedBall,dist_self] using hB⟩
  let : Nonempty S := ⟨pS⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall p B)
  have hm := setRetraction_measurable (S := S) measurableSet_closedBall pS
  let ν₀S := ν₀.map (setRetraction pS)
  let ν₁S := ν₁.map (setRetraction pS)
  let πS := π.map (fun xy => (setRetraction pS xy.1,setRetraction pS xy.2))
  let : IsProbabilityMeasure ν₀S := inferInstance
  let : IsProbabilityMeasure ν₁S := inferInstance
  have hpS : IsOptimalCoupling ν₀S ν₁S πS := hp.retract_to_set measurableSet_closedBall pS h₀ h₁
  obtain ⟨a,b,⟨L₀,haLip,hbLip⟩,had,hc⟩ := hpS.compact_potentials ν₀S ν₁S
  let M : ℝ := ‖b‖
  let A : ℝ := ‖a‖
  let R : ℝ := M+A+1
  have ha : ∀ x, a x ≤ A := fun x => (le_abs_self _).trans (a.norm_coe_le_norm x)
  have hb : ∀ x, b x ≤ M := fun x => (le_abs_self _).trans (b.norm_coe_le_norm x)
  have hR : 0 ≤ R := by dsimp [R,M,A]; positivity
  have hcut : M+A ≤ R^2/2 := by dsimp [R]; nlinarith [sq_nonneg (M+A)]
  let T : X → ℝ := truncatedCostTransform (⇑a) M
  have hT : LipschitzWith ⟨R,hR⟩ T := truncatedCostTransform_lipschitz ha hR hcut
  have hT0 : ∀ x, B+R < dist p x → T x = M := by
    intro x hx
    apply truncatedCostTransform_eq_const_outside ha hR hcut p _ hx.le
    intro y
    simpa only [dist_comm] using (mem_closedBall.mp y.property)
  have hdual (x : S) (y : X) : a x+T y ≤ dist (x:X) y^2/2 := by
    have hh := truncatedCostTransform_le_cost (M := M) ha x y
    change T y ≤ _ at hh
    linarith
  have hlo (y : S) : b y ≤ T y := by
    apply le_truncatedCostTransform (y:X) (hb y)
    intro x
    have hh := had x y
    change a x+b y ≤ dist (x:X) (y:X)^2/2 at hh
    linarith
  let f : X → ℝ := fun x => M-T x
  have hf : LipschitzWith ⟨R,hR⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [f,dist_sub_left] using hT.dist_le_mul x y
  have hf0 : ∀ x, B+R < dist p x → f x = 0 := by
    intro x hx
    simp only [f,hT0 x hx,sub_self]
  let ψ : X → ℝ := fun x => T x-M
  have hψ : LipschitzWith ⟨R,hR⟩ ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [ψ,dist_sub_right] using hT.dist_le_mul x y
  have hsψ : HasCompactSupport ψ := by
    apply HasCompactSupport.intro (isCompact_closedBall p (B+R))
    intro x hx
    simp only [ψ,hT0 x (by simpa only [mem_closedBall,dist_comm,not_le] using hx),sub_self]
  have hLip := hopfLax_lipschitz hf hgeo (by norm_num : (0:ℝ) < 1)
  have hsφ := hopfLax_hasCompactSupport hf p (B+R) hf0 (by norm_num : (0:ℝ) < 1)
  let u := SobolevSpace.ofLipschitzCompact μ hQ hLip hsφ
  have hsource (x : S) : a x+M ≤ hopfLax f 1 x := by
    apply le_csInf ⟨_,mem_range_self (x:X)⟩
    rintro _ ⟨z,rfl⟩
    have hh := hdual x z
    simp only [f,mul_one]
    linarith
  have hcS (x y : S) (hxy : a x+b y = dist x y^2/2) :
      hopfLax f 1 (x:X)+ψ (y:X) = dist (x:X) (y:X)^2/2 := by
    have hTy : T y = b y := by
      have hh := hdual x (y:X)
      change a x+b y = dist (x:X) (y:X)^2/2 at hxy
      exact le_antisymm (by linarith) (hlo y)
    have hupper := hopfLax_le_cost hf (by norm_num : (0:ℝ) < 1) (x:X) (y:X)
    have hlower := hsource x
    simp only [f,mul_one,hTy] at hupper
    change a x+b y = dist (x:X) (y:X)^2/2 at hxy
    dsimp [ψ]
    rw [hTy]
    linarith
  have hcontact : ∀ᵐ xy ∂π, hopfLax f 1 xy.1+ψ xy.2 = dist xy.1 xy.2^2/2 := by
    have hc' := ae_of_ae_map ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd)).aemeasurable hc
    have h₀' : ∀ᵐ xy ∂π, xy.1 ∈ S := ae_of_ae_map measurable_fst.aemeasurable (by
      rw [hp.1]
      exact h₀)
    have h₁' : ∀ᵐ xy ∂π, xy.2 ∈ S := ae_of_ae_map measurable_snd.aemeasurable (by
      rw [hp.2.1]
      exact h₁)
    filter_upwards [hc',h₀',h₁'] with xy hxy hx hy
    have hh := hcS _ _ hxy
    simpa only [Function.comp_apply,setRetraction_val_of_mem pS hx,setRetraction_val_of_mem pS hy] using hh
  refine ⟨u,hopfLax f 1,ψ,⟨R,hR⟩,hLip,hψ,hsφ,hsψ,
    (SobolevSpace.ofLipschitzCompact_coe μ hQ hLip hsφ).symm,?_,hcontact,?_⟩
  · intro x y
    have hh := hopfLax_le_cost hf (by norm_num : (0:ℝ) < 1) x y
    simp only [f,mul_one] at hh
    dsimp [ψ]
    linarith
  · have hbound := (hopfLeftRadius_minimalSlope_bound_proper μ hQ hf hgeo p (B+R) hf0).filter_mono hac.ae_le
    rw [←hp.1] at hbound
    have hb' := ae_of_ae_map measurable_fst.aemeasurable hbound
    filter_upwards [hb',hcontact] with xy hh hxy
    apply hh.trans (hopfLeftRadius_le_minimizer hf ?_)
    change hopfLax f 1 xy.1 = f xy.2+dist xy.1 xy.2^2/(2*1)
    dsimp [ψ] at hxy
    dsimp [f]
    linarith


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem sqrt_core_entropy_subgradient [ProperSpace X]
    (μ : Measure X) [SigmaFinite μ] [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀]
    (u ρ : SobolevSpace μ hQ)
    {h : X → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) (hn : ∀ x, 0 ≤ h x)
    (hi : Integrable h μ)
    (hrep : (SobolevSpace.toLp μ hQ ρ : X → ℝ) =ᵐ[μ] fun x => h x^2)
    (hν : ν₀ = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hmap0 : π.map (fun γ => γ 0) = ν₀)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDn : 0 ≤ D) (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (hs : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B)
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1))
    (K : ℝ)
    (hconv : ∀ t : Time,
      Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
        Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ ∧
      boltzmannEntropy μ (π.map (fun γ => γ t)) ≤
        (1-(t:ℝ))*boltzmannEntropy μ ν₀+(t:ℝ)*boltzmannEntropy μ ν₁+
        ((-K)*(t:ℝ)*(1-(t:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂π)) :
    -energyForm μ hQ u ρ ≤ boltzmannEntropy μ ν₁-boltzmannEntropy μ ν₀-
      (K/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂π) := by
  let r := SobolevSpace.toLp μ hQ ρ
  have hrn : (fun x => h x^2) =ᵐ[μ] fun x => (ν₀.rnDeriv μ x).toReal := by
    rw [hν]
    filter_upwards [Measure.rnDeriv_withDensity μ (Lp.stronglyMeasurable r).measurable.ennreal_ofReal,
      hrep] with x hx hs
    rw [hx,hs,ENNReal.toReal_ofReal (sq_nonneg _)]
  have hd := sqrt_core_signed_variation μ hQ π hgeo hC hcomp hD hDn hDb
    u ρ hh hn hi hrep (hmap0.trans hν) hu had hc hb
  exact entropy_regularized_plan_derivative_le μ ν₀ ν₁ r hh.continuous.measurable hrep hrn he0
    π hmap0 hC hcomp hB hs K hconv hd

 theorem NoncollapsedRCD.sqrt_core_energy_subgradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (ρ : SobolevSpace (hausdorff n X) hX.quadratic)
    {h : X → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) (hhn : ∀ x, 0 ≤ h x)
    (hi : Integrable h (hausdorff n X))
    (hrep : (SobolevSpace.toLp _ hX.quadratic ρ : X → ℝ) =ᵐ[hausdorff n X] fun x => h x^2)
    (hν : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ x))) :
    ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (φ ψ : X → ℝ) (A : ℝ≥0),
      LipschitzWith A φ ∧ LipschitzWith A ψ ∧ HasCompactSupport φ ∧ HasCompactSupport ψ ∧
      (φ =ᵐ[hausdorff n X] SobolevSpace.toLp _ hX.quadratic u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁) = (wassersteinSq ν₀ ν₁).toReal/2 ∧
      -energyForm (hausdorff n X) hX.quadratic u ρ ≤
        boltzmannEntropy (hausdorff n X) ν₁-boltzmannEntropy (hausdorff n X) ν₀-
        (K/2)*(wassersteinSq ν₀ ν₁).toReal := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨π,hπ,hg,hp,hdi,hall⟩ := hX.exists_bounded_entropy_plan K n hn ν₀ ν₁ hC h0 h1 p hR hs0 hs1
  let := hπ
  have he := optimalPlan_endpoints ν₀ ν₁ π hp
  obtain ⟨u,φ,ψ,A,hφ,hψ,hsφ,hsψ,hu,had,hcontact,hb⟩ :=
    hp.bounded_sobolev_potential μ hX.quadratic hX.geodesic ν₀ ν₁
      (Measure.absolutelyContinuous_of_le_smul h0) p hR hs0 hs1
  have hm : Measurable (fun γ : C(Time,X) => (γ 0,γ 1)) :=
    (measurable_path_eval 0).prodMk (measurable_path_eval 1)
  have hc := ae_of_ae_map hm.aemeasurable hcontact
  have hb' := ae_of_ae_map hm.aemeasurable hb
  let B := closedBall p (3*R)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B := by
    apply ae_map_iff (measurable_path_eval t).aemeasurable (by measurability) |>.mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ π hg hp p hR hs0 hs1).mono fun γ hγ => hγ.2 t
  have hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π := by
    exact (memLp_two_iff_integrable_sq ((measurable_path_eval 0).dist
      (measurable_path_eval 1)).aestronglyMeasurable).mpr hdi
  have hcost : (wassersteinSq ν₀ ν₁).toReal = ∫γ, dist (γ 0) (γ 1)^2 ∂π := by
    rw [wassersteinSq_eq_cost hp,transportCost_plan_eq_integral π hdi,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hbound := sqrt_core_entropy_subgradient μ hX.quadratic ν₀ ν₁ u ρ hh hhn hi hrep hν
    (he.1 ▸ (hall 0).2.1) π hg he.1 (compressionBudget_ne_top K n (2*R) hC)
    (fun t => (hall t).1) hD (by positivity : 0 ≤ 2*R)
    (optimalPlanDistanceBound_of_bounded ν₀ ν₁ p hs0 hs1 π hπ hg hp)
    measurableSet_closedBall hs hu had hc hb' K (fun t => (hall t).2)
  refine ⟨u,φ,ψ,A,hφ,hψ,hsφ,hsψ,hu,had,?_,?_⟩
  · have hφi : Integrable φ ν₀ := hφ.continuous.integrable_of_hasCompactSupport hsφ
    have hψi : Integrable ψ ν₁ := hψ.continuous.integrable_of_hasCompactSupport hsψ
    have hφπ : Integrable (fun γ : C(Time,X) => φ (γ 0)) π := by
      apply Integrable.comp_measurable _ (measurable_path_eval 0)
      rwa [he.1]
    have hψπ : Integrable (fun γ : C(Time,X) => ψ (γ 1)) π := by
      apply Integrable.comp_measurable _ (measurable_path_eval 1)
      rwa [he.2]
    rw [←he.1,←he.2,integral_map (measurable_path_eval 0).aemeasurable hφ.continuous.measurable.aestronglyMeasurable,
      integral_map (measurable_path_eval 1).aemeasurable hψ.continuous.measurable.aestronglyMeasurable,
      ←integral_add hφπ hψπ,integral_congr_ae hc,integral_div,he.1,he.2,hcost]
  · rwa [←hcost] at hbound


end

 
section

 

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

 theorem IsOptimalCoupling.uniform_compact_potentials (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {π : Measure (X×X)} (hp : IsOptimalCoupling μ ν π) :
    ∃ φ ψ : C(X,ℝ),
      LipschitzWith (2*⟨‖compactDistanceCost (X := X)‖,norm_nonneg _⟩) φ ∧
      LipschitzWith (2*⟨‖compactDistanceCost (X := X)‖,norm_nonneg _⟩) ψ ∧
      (∀ x, |φ x| ≤ 2*‖compactSquaredCost (X := X)‖) ∧
      (∀ x, |ψ x| ≤ 3*‖compactSquaredCost (X := X)‖) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ xy ∂π, φ xy.1+ψ xy.2 = dist xy.1 xy.2^2/2) := by
  obtain ⟨π',f,g,hprob,hfst,hsnd,hf,hg,hfb,hgb,had,hcontact,_,_⟩ :=
    compact_transport_primal_dual_attained μ ν (-compactSquaredCost (X := X))
      compactSquaredCost_lipschitz.neg
  let : IsProbabilityMeasure π' := hprob
  let φ : C(X,ℝ) := -f
  let ψ : C(X,ℝ) := -g
  have had' (x y : X) : φ x+ψ y ≤ dist x y^2/2 := by
    have hh := had (x,y)
    change -(dist x y^2/2) ≤ f x+g y at hh
    change -f x+-g y ≤ _
    linarith
  have hc' : ∀ᵐ xy ∂π', φ xy.1+ψ xy.2 = dist xy.1 xy.2^2/2 := by
    filter_upwards [hcontact] with xy hh
    change -(dist xy.1 xy.2^2/2) = f xy.1+g xy.2 at hh
    change -f xy.1+-g xy.2 = _
    linarith
  have hq := compact_contact_isOptimal hfst hsnd φ ψ had' hc'
  let := coupling_probability_of_fst hp.1
  have he := compact_optimal_cost_eq hp hq
  rw [compact_transportCost_integral,compact_transportCost_integral] at he
  have he' := (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)).mp he
  have hec := integral_congr_ae hc'
  change (∫xy,separatedSum φ ψ xy ∂π') = _ at hec
  rw [compact_coupling_separated_integral μ ν π' hfst hsnd,integral_div,←he'] at hec
  let h : C(X×X,ℝ) := compactSquaredCost-separatedSum φ ψ
  have hi := compact_continuous_integrable π h
  have hz : (∫xy,h xy ∂π) = 0 := by
    change (∫xy,compactSquaredCost xy-separatedSum φ ψ xy ∂π) = 0
    rw [integral_sub (compact_continuous_integrable π compactSquaredCost)
      (compact_continuous_integrable π (separatedSum φ ψ))]
    change (∫xy,dist xy.1 xy.2^2/2 ∂π)-(∫xy,separatedSum φ ψ xy ∂π) = 0
    rw [integral_div,compact_coupling_separated_integral μ ν π hp.1 hp.2.1,hec,sub_self]
  have hn : 0 ≤ᵐ[π] (fun xy => h xy) :=
    Eventually.of_forall (fun xy => sub_nonneg.mpr (had' xy.1 xy.2))
  refine ⟨φ,ψ,hf.neg,hg.neg,?_,?_,had',?_⟩
  · intro x
    simpa only [φ,ContinuousMap.neg_apply,abs_neg,norm_neg] using hfb x
  · intro x
    simpa only [ψ,ContinuousMap.neg_apply,abs_neg,norm_neg] using hgb x
  · filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz] with xy hxy
    change dist xy.1 xy.2^2/2-(φ xy.1+ψ xy.2) = 0 at hxy
    linarith


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

 theorem IsOptimalCoupling.linear_radius_bounded_sobolev_potential
    (hgeo : IsGeodesicSpace X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] (hac : ν₀ ≪ μ)
    {π : Measure (X×X)} (hp : IsOptimalCoupling ν₀ ν₁ π)
    (p : X) {B : ℝ} (hB : 0 ≤ B)
    (h₀ : ∀ᵐ x ∂ν₀, x ∈ closedBall p B) (h₁ : ∀ᵐ x ∂ν₁, x ∈ closedBall p B) :
    ∃ (u : SobolevSpace μ hQ) (φ ψ : X → ℝ),
      LipschitzWith ⟨5*B,by positivity⟩ φ ∧
      LipschitzWith ⟨5*B,by positivity⟩ ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 10*B^2) ∧
      (∀ x, -10*B^2 ≤ ψ x ∧ ψ x ≤ 0) ∧
      tsupport φ ⊆ closedBall p (B+5*B) ∧
      tsupport ψ ⊆ closedBall p (B+5*B) ∧
      HasCompactSupport φ ∧ HasCompactSupport ψ ∧
      (φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ xy ∂π, φ xy.1+ψ xy.2 = dist xy.1 xy.2^2/2) ∧
      (∀ᵐ xy ∂π, SobolevSpace.minimalSlope μ hQ u xy.1 ≤ dist xy.1 xy.2) := by
  let S := closedBall p B
  let pS : S := ⟨p,by simpa only [S,mem_closedBall,dist_self] using hB⟩
  let : Nonempty S := ⟨pS⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall p B)
  have hm := setRetraction_measurable (S := S) measurableSet_closedBall pS
  let ν₀S := ν₀.map (setRetraction pS)
  let ν₁S := ν₁.map (setRetraction pS)
  let πS := π.map (fun xy => (setRetraction pS xy.1,setRetraction pS xy.2))
  let : IsProbabilityMeasure ν₀S := inferInstance
  let : IsProbabilityMeasure ν₁S := inferInstance
  have hpS : IsOptimalCoupling ν₀S ν₁S πS := hp.retract_to_set measurableSet_closedBall pS h₀ h₁
  obtain ⟨a,b,haLip,hbLip,haB,hbB,had,hc⟩ := hpS.uniform_compact_potentials ν₀S ν₁S
  have hnorm : ‖compactSquaredCost (X := S)‖ ≤ 2*B^2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    rintro ⟨x,y⟩
    have hx : dist (x:X) p ≤ B := x.property
    have hy : dist (y:X) p ≤ B := y.property
    have hd : dist x y ≤ 2*B := by
      change dist (x:X) (y:X) ≤ _
      have ht := dist_triangle (x:X) p (y:X)
      rw [dist_comm p (y:X)] at ht
      linarith
    change |dist x y^2/2| ≤ _
    rw [abs_of_nonneg (by positivity)]
    nlinarith [dist_nonneg (x := x) (y := y)]
  let M : ℝ := 6*B^2
  let A : ℝ := 4*B^2
  let R : ℝ := 5*B
  have ha : ∀ x, a x ≤ A := by
    intro x
    have hh := (le_abs_self _).trans (haB x)
    dsimp [A]
    linarith
  have hb : ∀ x, b x ≤ M := by
    intro x
    have hh := (le_abs_self _).trans (hbB x)
    dsimp [M]
    linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcut : M+A ≤ R^2/2 := by dsimp [R,M,A]; nlinarith [sq_nonneg B]
  let T : X → ℝ := truncatedCostTransform (⇑a) M
  have hT : LipschitzWith ⟨R,hR⟩ T := truncatedCostTransform_lipschitz ha hR hcut
  have hT0 : ∀ x, B+R < dist p x → T x = M := by
    intro x hx
    apply truncatedCostTransform_eq_const_outside ha hR hcut p _ hx.le
    intro y
    simpa only [dist_comm] using (mem_closedBall.mp y.property)
  have hdual (x : S) (y : X) : a x+T y ≤ dist (x:X) y^2/2 := by
    have hh := truncatedCostTransform_le_cost (M := M) ha x y
    change T y ≤ _ at hh
    linarith
  have hlo (y : S) : b y ≤ T y := by
    apply le_truncatedCostTransform (y:X) (hb y)
    intro x
    have hh := had x y
    change a x+b y ≤ dist (x:X) (y:X)^2/2 at hh
    linarith
  have hTb (x : X) : -A ≤ T x ∧ T x ≤ M := by
    refine ⟨le_truncatedCostTransform x (by dsimp [A,M]; nlinarith [sq_nonneg B]) ?_,truncatedCostTransform_le ha x⟩
    intro y
    have hh := ha y
    nlinarith [sq_nonneg (dist (y:X) x)]
  let f : X → ℝ := fun x => M-T x
  have hfb (x : X) : 0 ≤ f x ∧ f x ≤ 10*B^2 := by
    have hh := hTb x
    dsimp [f,M,A] at *
    constructor <;> linarith
  have hf : LipschitzWith ⟨R,hR⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [f,dist_sub_left] using hT.dist_le_mul x y
  have hf0 : ∀ x, B+R < dist p x → f x = 0 := by
    intro x hx
    simp only [f,hT0 x hx,sub_self]
  let ψ : X → ℝ := fun x => T x-M
  have hψ : LipschitzWith ⟨R,hR⟩ ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [ψ,dist_sub_right] using hT.dist_le_mul x y
  have hsψ : HasCompactSupport ψ := by
    apply HasCompactSupport.intro (isCompact_closedBall p (B+R))
    intro x hx
    simp only [ψ,hT0 x (by simpa only [mem_closedBall,dist_comm,not_le] using hx),sub_self]
  have hLip := hopfLax_lipschitz hf hgeo (by norm_num : (0:ℝ) < 1)
  have hsφ := hopfLax_hasCompactSupport hf p (B+R) hf0 (by norm_num : (0:ℝ) < 1)
  have hφb (x : X) : 0 ≤ hopfLax f 1 x ∧ hopfLax f 1 x ≤ 10*B^2 := by
    obtain ⟨y,hy,_⟩ := hopfLax_exists_minimizer hf (by norm_num : (0:ℝ) < 1) x
    refine ⟨?_,(hopfLax_bounds hf (by norm_num : (0:ℝ) < 1) x).2.trans (hfb x).2⟩
    change hopfLax f 1 x = f y+dist x y^2/(2*1) at hy
    rw [hy]
    exact add_nonneg (hfb y).1 (by positivity)
  have hψb (x : X) : -10*B^2 ≤ ψ x ∧ ψ x ≤ 0 := by
    have hh := hTb x
    dsimp [ψ,M,A] at *
    constructor <;> linarith
  have hφ0 : ∀ x, B+R < dist p x → hopfLax f 1 x = 0 := by
    intro x hx
    apply le_antisymm _ (hφb x).1
    have hh := (hopfLax_bounds hf (by norm_num : (0:ℝ) < 1) x).2
    rwa [hf0 x hx] at hh
  have htφ : tsupport (hopfLax f 1) ⊆ closedBall p (B+R) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    exact hx (hφ0 x (by simpa only [mem_closedBall,dist_comm,not_le] using hn))
  have htψ : tsupport ψ ⊆ closedBall p (B+R) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    apply hx
    simp only [ψ,hT0 x (by simpa only [mem_closedBall,dist_comm,not_le] using hn),sub_self]
  let u := SobolevSpace.ofLipschitzCompact μ hQ hLip hsφ
  have hsource (x : S) : a x+M ≤ hopfLax f 1 x := by
    apply le_csInf ⟨_,mem_range_self (x:X)⟩
    rintro _ ⟨z,rfl⟩
    have hh := hdual x z
    simp only [f,mul_one]
    linarith
  have hcS (x y : S) (hxy : a x+b y = dist x y^2/2) :
      hopfLax f 1 (x:X)+ψ (y:X) = dist (x:X) (y:X)^2/2 := by
    have hTy : T y = b y := by
      have hh := hdual x (y:X)
      change a x+b y = dist (x:X) (y:X)^2/2 at hxy
      exact le_antisymm (by linarith) (hlo y)
    have hupper := hopfLax_le_cost hf (by norm_num : (0:ℝ) < 1) (x:X) (y:X)
    have hlower := hsource x
    simp only [f,mul_one,hTy] at hupper
    change a x+b y = dist (x:X) (y:X)^2/2 at hxy
    dsimp [ψ]
    rw [hTy]
    linarith
  have hcontact : ∀ᵐ xy ∂π, hopfLax f 1 xy.1+ψ xy.2 = dist xy.1 xy.2^2/2 := by
    have hc' := ae_of_ae_map ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd)).aemeasurable hc
    have h₀' : ∀ᵐ xy ∂π, xy.1 ∈ S := ae_of_ae_map measurable_fst.aemeasurable (by
      rw [hp.1]
      exact h₀)
    have h₁' : ∀ᵐ xy ∂π, xy.2 ∈ S := ae_of_ae_map measurable_snd.aemeasurable (by
      rw [hp.2.1]
      exact h₁)
    filter_upwards [hc',h₀',h₁'] with xy hxy hx hy
    have hh := hcS _ _ hxy
    simpa only [Function.comp_apply,setRetraction_val_of_mem pS hx,setRetraction_val_of_mem pS hy] using hh
  refine ⟨u,hopfLax f 1,ψ,hLip,hψ,hφb,hψb,htφ,htψ,hsφ,hsψ,
    (SobolevSpace.ofLipschitzCompact_coe μ hQ hLip hsφ).symm,?_,hcontact,?_⟩
  · intro x y
    have hh := hopfLax_le_cost hf (by norm_num : (0:ℝ) < 1) x y
    simp only [f,mul_one] at hh
    dsimp [ψ]
    linarith
  · have hbound := (hopfLeftRadius_minimalSlope_bound_proper μ hQ hf hgeo p (B+R) hf0).filter_mono hac.ae_le
    rw [←hp.1] at hbound
    have hb' := ae_of_ae_map measurable_fst.aemeasurable hbound
    filter_upwards [hb',hcontact] with xy hh hxy
    apply hh.trans (hopfLeftRadius_le_minimizer hf ?_)
    change hopfLax f 1 xy.1 = f xy.2+dist xy.1 xy.2^2/(2*1)
    dsimp [ψ] at hxy
    dsimp [f]
    linarith


end

 
section
 
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace
 theorem NoncollapsedRCD.linear_radius_sqrt_core_energy_subgradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (ρ : SobolevSpace (hausdorff n X) hX.quadratic)
    {h : X → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) (hhn : ∀ x, 0 ≤ h x)
    (hi : Integrable h (hausdorff n X))
    (hrep : (SobolevSpace.toLp _ hX.quadratic ρ : X → ℝ) =ᵐ[hausdorff n X] fun x => h x^2)
    (hν : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ x))) :
    ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (φ ψ : X → ℝ),
      LipschitzWith ⟨5*R,by positivity⟩ φ ∧
      LipschitzWith ⟨5*R,by positivity⟩ ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 10*R^2) ∧
      (∀ x, -10*R^2 ≤ ψ x ∧ ψ x ≤ 0) ∧
      tsupport φ ⊆ closedBall p (R+(5*R)) ∧
      tsupport ψ ⊆ closedBall p (R+(5*R)) ∧
      HasCompactSupport φ ∧ HasCompactSupport ψ ∧
      (φ =ᵐ[hausdorff n X] SobolevSpace.toLp _ hX.quadratic u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁) = (wassersteinSq ν₀ ν₁).toReal/2 ∧
      -energyForm (hausdorff n X) hX.quadratic u ρ ≤
        boltzmannEntropy (hausdorff n X) ν₁-boltzmannEntropy (hausdorff n X) ν₀-
        (K/2)*(wassersteinSq ν₀ ν₁).toReal := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨π,hπ,hg,hp,hdi,hall⟩ := hX.exists_bounded_entropy_plan K n hn ν₀ ν₁ hC h0 h1 p hR hs0 hs1
  let := hπ
  have he := optimalPlan_endpoints ν₀ ν₁ π hp
  obtain ⟨u,φ,ψ,hφ,hψ,hφb,hψb,htφ,htψ,hsφ,hsψ,hu,had,hcontact,hb⟩ :=
    hp.linear_radius_bounded_sobolev_potential μ hX.quadratic hX.geodesic ν₀ ν₁
      (Measure.absolutelyContinuous_of_le_smul h0) p hR hs0 hs1
  have hm : Measurable (fun γ : C(Time,X) => (γ 0,γ 1)) :=
    (measurable_path_eval 0).prodMk (measurable_path_eval 1)
  have hc := ae_of_ae_map hm.aemeasurable hcontact
  have hb' := ae_of_ae_map hm.aemeasurable hb
  let B := closedBall p (3*R)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B := by
    apply ae_map_iff (measurable_path_eval t).aemeasurable (by measurability) |>.mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ π hg hp p hR hs0 hs1).mono fun γ hγ => hγ.2 t
  have hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π := by
    exact (memLp_two_iff_integrable_sq ((measurable_path_eval 0).dist
      (measurable_path_eval 1)).aestronglyMeasurable).mpr hdi
  have hcost : (wassersteinSq ν₀ ν₁).toReal = ∫γ, dist (γ 0) (γ 1)^2 ∂π := by
    rw [wassersteinSq_eq_cost hp,transportCost_plan_eq_integral π hdi,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hbound := sqrt_core_entropy_subgradient μ hX.quadratic ν₀ ν₁ u ρ hh hhn hi hrep hν
    (he.1 ▸ (hall 0).2.1) π hg he.1 (compressionBudget_ne_top K n (2*R) hC)
    (fun t => (hall t).1) hD (by positivity : 0 ≤ 2*R)
    (optimalPlanDistanceBound_of_bounded ν₀ ν₁ p hs0 hs1 π hπ hg hp)
    measurableSet_closedBall hs hu had hc hb' K (fun t => (hall t).2)
  refine ⟨u,φ,ψ,hφ,hψ,hφb,hψb,htφ,htψ,hsφ,hsψ,hu,had,?_,?_⟩
  · have hφi : Integrable φ ν₀ := hφ.continuous.integrable_of_hasCompactSupport hsφ
    have hψi : Integrable ψ ν₁ := hψ.continuous.integrable_of_hasCompactSupport hsψ
    have hφπ : Integrable (fun γ : C(Time,X) => φ (γ 0)) π := by
      apply Integrable.comp_measurable _ (measurable_path_eval 0)
      rwa [he.1]
    have hψπ : Integrable (fun γ : C(Time,X) => ψ (γ 1)) π := by
      apply Integrable.comp_measurable _ (measurable_path_eval 1)
      rwa [he.2]
    rw [←he.1,←he.2,integral_map (measurable_path_eval 0).aemeasurable hφ.continuous.measurable.aestronglyMeasurable,
      integral_map (measurable_path_eval 1).aemeasurable hψ.continuous.measurable.aestronglyMeasurable,
      ←integral_add hφπ hψπ,integral_congr_ae hc,integral_div,he.1,he.2,hcost]
  · rwa [←hcost] at hbound


end

 
section

 
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem optimal_plan_cost_real {ν₀ ν₁ : Measure X} {π : Measure C(Time,X)}
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map fun γ => (γ 0,γ 1)))
    (hi : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) π) :
    (wassersteinSq ν₀ ν₁).toReal = ∫γ, dist (γ 0) (γ 1)^2 ∂π := by
  rw [wassersteinSq_eq_cost hp,transportCost_plan_eq_integral π hi,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]

theorem optimal_plan_dual_le {ν₀ ν₁ : Measure X} {π : Measure C(Time,X)}
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map fun γ => (γ 0,γ 1)))
    (hi : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) π)
    {φ ψ : X → ℝ} (hφ : Integrable φ ν₀) (hψ : Integrable ψ ν₁)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2) :
    (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁) ≤ (wassersteinSq ν₀ ν₁).toReal/2 := by
  have he := optimalPlan_endpoints ν₀ ν₁ π hp
  have hφπ : Integrable (fun γ : C(Time,X) => φ (γ 0)) π := by
    exact Integrable.comp_measurable (he.1.symm ▸ hφ) (measurable_path_eval 0)
  have hψπ : Integrable (fun γ : C(Time,X) => ψ (γ 1)) π := by
    exact Integrable.comp_measurable (he.2.symm ▸ hψ) (measurable_path_eval 1)
  have hh := integral_mono (hφπ.add hψπ) (hi.div_const 2) (fun γ => had (γ 0) (γ 1))
  simp only [Pi.add_apply] at hh
  rw [integral_add hφπ hψπ,integral_div] at hh
  rw [←integral_map (measurable_path_eval 0).aemeasurable (he.1.symm ▸ hφ.aestronglyMeasurable),
    ←integral_map (measurable_path_eval 1).aemeasurable (he.2.symm ▸ hψ.aestronglyMeasurable),
    he.1,he.2,←optimal_plan_cost_real hp hi] at hh
  exact hh

theorem optimal_plan_dual_eq {ν₀ ν₁ : Measure X} {π : Measure C(Time,X)}
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map fun γ => (γ 0,γ 1)))
    (hi : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) π)
    {φ ψ : X → ℝ} (hφ : Integrable φ ν₀) (hψ : Integrable ψ ν₁)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2) :
    (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁) = (wassersteinSq ν₀ ν₁).toReal/2 := by
  have he := optimalPlan_endpoints ν₀ ν₁ π hp
  have hφπ : Integrable (fun γ : C(Time,X) => φ (γ 0)) π :=
    Integrable.comp_measurable (he.1.symm ▸ hφ) (measurable_path_eval 0)
  have hψπ : Integrable (fun γ : C(Time,X) => ψ (γ 1)) π :=
    Integrable.comp_measurable (he.2.symm ▸ hψ) (measurable_path_eval 1)
  have hh := integral_congr_ae hc
  rw [integral_add hφπ hψπ,integral_div,
    ←integral_map (measurable_path_eval 0).aemeasurable (he.1.symm ▸ hφ.aestronglyMeasurable),
    ←integral_map (measurable_path_eval 1).aemeasurable (he.2.symm ▸ hψ.aestronglyMeasurable),
    he.1,he.2,←optimal_plan_cost_real hp hi] at hh
  exact hh


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

 theorem IsOptimalCoupling.uniform_bounded_sobolev_potential
    (hgeo : IsGeodesicSpace X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] (hac : ν₀ ≪ μ)
    {π : Measure (X×X)} (hp : IsOptimalCoupling ν₀ ν₁ π)
    (p : X) {B : ℝ} (hB : 0 ≤ B)
    (h₀ : ∀ᵐ x ∂ν₀, x ∈ closedBall p B) (h₁ : ∀ᵐ x ∂ν₁, x ∈ closedBall p B) :
    ∃ (u : SobolevSpace μ hQ) (φ ψ : X → ℝ),
      LipschitzWith ⟨10*B^2+1,by positivity⟩ φ ∧
      LipschitzWith ⟨10*B^2+1,by positivity⟩ ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 10*B^2) ∧
      (∀ x, -10*B^2 ≤ ψ x ∧ ψ x ≤ 0) ∧
      tsupport φ ⊆ closedBall p (B+(10*B^2+1)) ∧
      tsupport ψ ⊆ closedBall p (B+(10*B^2+1)) ∧
      HasCompactSupport φ ∧ HasCompactSupport ψ ∧
      (φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ xy ∂π, φ xy.1+ψ xy.2 = dist xy.1 xy.2^2/2) ∧
      (∀ᵐ xy ∂π, SobolevSpace.minimalSlope μ hQ u xy.1 ≤ dist xy.1 xy.2) := by
  let S := closedBall p B
  let pS : S := ⟨p,by simpa only [S,mem_closedBall,dist_self] using hB⟩
  let : Nonempty S := ⟨pS⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall p B)
  have hm := setRetraction_measurable (S := S) measurableSet_closedBall pS
  let ν₀S := ν₀.map (setRetraction pS)
  let ν₁S := ν₁.map (setRetraction pS)
  let πS := π.map (fun xy => (setRetraction pS xy.1,setRetraction pS xy.2))
  let : IsProbabilityMeasure ν₀S := inferInstance
  let : IsProbabilityMeasure ν₁S := inferInstance
  have hpS : IsOptimalCoupling ν₀S ν₁S πS := hp.retract_to_set measurableSet_closedBall pS h₀ h₁
  obtain ⟨a,b,haLip,hbLip,haB,hbB,had,hc⟩ := hpS.uniform_compact_potentials ν₀S ν₁S
  have hnorm : ‖compactSquaredCost (X := S)‖ ≤ 2*B^2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    rintro ⟨x,y⟩
    have hx : dist (x:X) p ≤ B := x.property
    have hy : dist (y:X) p ≤ B := y.property
    have hd : dist x y ≤ 2*B := by
      change dist (x:X) (y:X) ≤ _
      have ht := dist_triangle (x:X) p (y:X)
      rw [dist_comm p (y:X)] at ht
      linarith
    change |dist x y^2/2| ≤ _
    rw [abs_of_nonneg (by positivity)]
    nlinarith [dist_nonneg (x := x) (y := y)]
  let M : ℝ := 6*B^2
  let A : ℝ := 4*B^2
  let R : ℝ := 10*B^2+1
  have ha : ∀ x, a x ≤ A := by
    intro x
    have hh := (le_abs_self _).trans (haB x)
    dsimp [A]
    linarith
  have hb : ∀ x, b x ≤ M := by
    intro x
    have hh := (le_abs_self _).trans (hbB x)
    dsimp [M]
    linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcut : M+A ≤ R^2/2 := by dsimp [R,M,A]; nlinarith [sq_nonneg (10*B^2)]
  let T : X → ℝ := truncatedCostTransform (⇑a) M
  have hT : LipschitzWith ⟨R,hR⟩ T := truncatedCostTransform_lipschitz ha hR hcut
  have hT0 : ∀ x, B+R < dist p x → T x = M := by
    intro x hx
    apply truncatedCostTransform_eq_const_outside ha hR hcut p _ hx.le
    intro y
    simpa only [dist_comm] using (mem_closedBall.mp y.property)
  have hdual (x : S) (y : X) : a x+T y ≤ dist (x:X) y^2/2 := by
    have hh := truncatedCostTransform_le_cost (M := M) ha x y
    change T y ≤ _ at hh
    linarith
  have hlo (y : S) : b y ≤ T y := by
    apply le_truncatedCostTransform (y:X) (hb y)
    intro x
    have hh := had x y
    change a x+b y ≤ dist (x:X) (y:X)^2/2 at hh
    linarith
  have hTb (x : X) : -A ≤ T x ∧ T x ≤ M := by
    refine ⟨le_truncatedCostTransform x (by dsimp [A,M]; nlinarith [sq_nonneg B]) ?_,truncatedCostTransform_le ha x⟩
    intro y
    have hh := ha y
    nlinarith [sq_nonneg (dist (y:X) x)]
  let f : X → ℝ := fun x => M-T x
  have hfb (x : X) : 0 ≤ f x ∧ f x ≤ 10*B^2 := by
    have hh := hTb x
    dsimp [f,M,A] at *
    constructor <;> linarith
  have hf : LipschitzWith ⟨R,hR⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [f,dist_sub_left] using hT.dist_le_mul x y
  have hf0 : ∀ x, B+R < dist p x → f x = 0 := by
    intro x hx
    simp only [f,hT0 x hx,sub_self]
  let ψ : X → ℝ := fun x => T x-M
  have hψ : LipschitzWith ⟨R,hR⟩ ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [ψ,dist_sub_right] using hT.dist_le_mul x y
  have hsψ : HasCompactSupport ψ := by
    apply HasCompactSupport.intro (isCompact_closedBall p (B+R))
    intro x hx
    simp only [ψ,hT0 x (by simpa only [mem_closedBall,dist_comm,not_le] using hx),sub_self]
  have hLip := hopfLax_lipschitz hf hgeo (by norm_num : (0:ℝ) < 1)
  have hsφ := hopfLax_hasCompactSupport hf p (B+R) hf0 (by norm_num : (0:ℝ) < 1)
  have hφb (x : X) : 0 ≤ hopfLax f 1 x ∧ hopfLax f 1 x ≤ 10*B^2 := by
    obtain ⟨y,hy,_⟩ := hopfLax_exists_minimizer hf (by norm_num : (0:ℝ) < 1) x
    refine ⟨?_,(hopfLax_bounds hf (by norm_num : (0:ℝ) < 1) x).2.trans (hfb x).2⟩
    change hopfLax f 1 x = f y+dist x y^2/(2*1) at hy
    rw [hy]
    exact add_nonneg (hfb y).1 (by positivity)
  have hψb (x : X) : -10*B^2 ≤ ψ x ∧ ψ x ≤ 0 := by
    have hh := hTb x
    dsimp [ψ,M,A] at *
    constructor <;> linarith
  have hφ0 : ∀ x, B+R < dist p x → hopfLax f 1 x = 0 := by
    intro x hx
    apply le_antisymm _ (hφb x).1
    have hh := (hopfLax_bounds hf (by norm_num : (0:ℝ) < 1) x).2
    rwa [hf0 x hx] at hh
  have htφ : tsupport (hopfLax f 1) ⊆ closedBall p (B+R) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    exact hx (hφ0 x (by simpa only [mem_closedBall,dist_comm,not_le] using hn))
  have htψ : tsupport ψ ⊆ closedBall p (B+R) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    apply hx
    simp only [ψ,hT0 x (by simpa only [mem_closedBall,dist_comm,not_le] using hn),sub_self]
  let u := SobolevSpace.ofLipschitzCompact μ hQ hLip hsφ
  have hsource (x : S) : a x+M ≤ hopfLax f 1 x := by
    apply le_csInf ⟨_,mem_range_self (x:X)⟩
    rintro _ ⟨z,rfl⟩
    have hh := hdual x z
    simp only [f,mul_one]
    linarith
  have hcS (x y : S) (hxy : a x+b y = dist x y^2/2) :
      hopfLax f 1 (x:X)+ψ (y:X) = dist (x:X) (y:X)^2/2 := by
    have hTy : T y = b y := by
      have hh := hdual x (y:X)
      change a x+b y = dist (x:X) (y:X)^2/2 at hxy
      exact le_antisymm (by linarith) (hlo y)
    have hupper := hopfLax_le_cost hf (by norm_num : (0:ℝ) < 1) (x:X) (y:X)
    have hlower := hsource x
    simp only [f,mul_one,hTy] at hupper
    change a x+b y = dist (x:X) (y:X)^2/2 at hxy
    dsimp [ψ]
    rw [hTy]
    linarith
  have hcontact : ∀ᵐ xy ∂π, hopfLax f 1 xy.1+ψ xy.2 = dist xy.1 xy.2^2/2 := by
    have hc' := ae_of_ae_map ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd)).aemeasurable hc
    have h₀' : ∀ᵐ xy ∂π, xy.1 ∈ S := ae_of_ae_map measurable_fst.aemeasurable (by
      rw [hp.1]
      exact h₀)
    have h₁' : ∀ᵐ xy ∂π, xy.2 ∈ S := ae_of_ae_map measurable_snd.aemeasurable (by
      rw [hp.2.1]
      exact h₁)
    filter_upwards [hc',h₀',h₁'] with xy hxy hx hy
    have hh := hcS _ _ hxy
    simpa only [Function.comp_apply,setRetraction_val_of_mem pS hx,setRetraction_val_of_mem pS hy] using hh
  refine ⟨u,hopfLax f 1,ψ,hLip,hψ,hφb,hψb,htφ,htψ,hsφ,hsψ,
    (SobolevSpace.ofLipschitzCompact_coe μ hQ hLip hsφ).symm,?_,hcontact,?_⟩
  · intro x y
    have hh := hopfLax_le_cost hf (by norm_num : (0:ℝ) < 1) x y
    simp only [f,mul_one] at hh
    dsimp [ψ]
    linarith
  · have hbound := (hopfLeftRadius_minimalSlope_bound_proper μ hQ hf hgeo p (B+R) hf0).filter_mono hac.ae_le
    rw [←hp.1] at hbound
    have hb' := ae_of_ae_map measurable_fst.aemeasurable hbound
    filter_upwards [hb',hcontact] with xy hh hxy
    apply hh.trans (hopfLeftRadius_le_minimizer hf ?_)
    change hopfLax f 1 xy.1 = f xy.2+dist xy.1 xy.2^2/(2*1)
    dsimp [ψ] at hxy
    dsimp [f]
    linarith


end

 
section
 
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace
 theorem NoncollapsedRCD.uniform_sqrt_core_energy_subgradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (ρ : SobolevSpace (hausdorff n X) hX.quadratic)
    {h : X → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) (hhn : ∀ x, 0 ≤ h x)
    (hi : Integrable h (hausdorff n X))
    (hrep : (SobolevSpace.toLp _ hX.quadratic ρ : X → ℝ) =ᵐ[hausdorff n X] fun x => h x^2)
    (hν : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ x))) :
    ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (φ ψ : X → ℝ),
      LipschitzWith ⟨10*R^2+1,by positivity⟩ φ ∧
      LipschitzWith ⟨10*R^2+1,by positivity⟩ ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 10*R^2) ∧
      (∀ x, -10*R^2 ≤ ψ x ∧ ψ x ≤ 0) ∧
      tsupport φ ⊆ closedBall p (R+(10*R^2+1)) ∧
      tsupport ψ ⊆ closedBall p (R+(10*R^2+1)) ∧
      HasCompactSupport φ ∧ HasCompactSupport ψ ∧
      (φ =ᵐ[hausdorff n X] SobolevSpace.toLp _ hX.quadratic u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁) = (wassersteinSq ν₀ ν₁).toReal/2 ∧
      -energyForm (hausdorff n X) hX.quadratic u ρ ≤
        boltzmannEntropy (hausdorff n X) ν₁-boltzmannEntropy (hausdorff n X) ν₀-
        (K/2)*(wassersteinSq ν₀ ν₁).toReal := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨π,hπ,hg,hp,hdi,hall⟩ := hX.exists_bounded_entropy_plan K n hn ν₀ ν₁ hC h0 h1 p hR hs0 hs1
  let := hπ
  have he := optimalPlan_endpoints ν₀ ν₁ π hp
  obtain ⟨u,φ,ψ,hφ,hψ,hφb,hψb,htφ,htψ,hsφ,hsψ,hu,had,hcontact,hb⟩ :=
    hp.uniform_bounded_sobolev_potential μ hX.quadratic hX.geodesic ν₀ ν₁
      (Measure.absolutelyContinuous_of_le_smul h0) p hR hs0 hs1
  have hm : Measurable (fun γ : C(Time,X) => (γ 0,γ 1)) :=
    (measurable_path_eval 0).prodMk (measurable_path_eval 1)
  have hc := ae_of_ae_map hm.aemeasurable hcontact
  have hb' := ae_of_ae_map hm.aemeasurable hb
  let B := closedBall p (3*R)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B := by
    apply ae_map_iff (measurable_path_eval t).aemeasurable (by measurability) |>.mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ π hg hp p hR hs0 hs1).mono fun γ hγ => hγ.2 t
  have hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π := by
    exact (memLp_two_iff_integrable_sq ((measurable_path_eval 0).dist
      (measurable_path_eval 1)).aestronglyMeasurable).mpr hdi
  have hcost : (wassersteinSq ν₀ ν₁).toReal = ∫γ, dist (γ 0) (γ 1)^2 ∂π := by
    rw [wassersteinSq_eq_cost hp,transportCost_plan_eq_integral π hdi,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hbound := sqrt_core_entropy_subgradient μ hX.quadratic ν₀ ν₁ u ρ hh hhn hi hrep hν
    (he.1 ▸ (hall 0).2.1) π hg he.1 (compressionBudget_ne_top K n (2*R) hC)
    (fun t => (hall t).1) hD (by positivity : 0 ≤ 2*R)
    (optimalPlanDistanceBound_of_bounded ν₀ ν₁ p hs0 hs1 π hπ hg hp)
    measurableSet_closedBall hs hu had hc hb' K (fun t => (hall t).2)
  refine ⟨u,φ,ψ,hφ,hψ,hφb,hψb,htφ,htψ,hsφ,hsψ,hu,had,?_,?_⟩
  · have hφi : Integrable φ ν₀ := hφ.continuous.integrable_of_hasCompactSupport hsφ
    have hψi : Integrable ψ ν₁ := hψ.continuous.integrable_of_hasCompactSupport hsψ
    have hφπ : Integrable (fun γ : C(Time,X) => φ (γ 0)) π := by
      apply Integrable.comp_measurable _ (measurable_path_eval 0)
      rwa [he.1]
    have hψπ : Integrable (fun γ : C(Time,X) => ψ (γ 1)) π := by
      apply Integrable.comp_measurable _ (measurable_path_eval 1)
      rwa [he.2]
    rw [←he.1,←he.2,integral_map (measurable_path_eval 0).aemeasurable hφ.continuous.measurable.aestronglyMeasurable,
      integral_map (measurable_path_eval 1).aemeasurable hψ.continuous.measurable.aestronglyMeasurable,
      ←integral_add hφπ hψπ,integral_congr_ae hc,integral_div,he.1,he.2,hcost]
  · rwa [←hcost] at hbound



 
theorem NoncollapsedRCD.bounded_density_dual_limit
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) (νs : ℕ → Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] [∀ i, IsProbabilityMeasure (νs i)]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (hcs : ∀ i, νs i ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (hss : ∀ i, ∀ᵐ x ∂νs i, dist x p ≤ R)
    {fs : ℕ → X → ℝ} {f : X → ℝ} {M : ℝ}
    (hfm : ∀ i, Measurable (fs i)) (hfn : ∀ i x, 0 ≤ fs i x ∧ fs i x ≤ M)
    (hfs : ∀ i x, fs i x ≠ 0 → x ∈ closedBall p R)
    (hf0m : Measurable f) (hf0n : ∀ᵐ x ∂hausdorff n X, 0 ≤ f x)
    (hfl : ∀ᵐ x ∂hausdorff n X, Tendsto (fun i => fs i x) atTop (𝓝 (f x)))
    (hd : ∀ i, νs i = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (fs i x)))
    (hd0 : ν₀ = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (f x)))
    {φs ψs : ℕ → X → ℝ} {φ ψ : X → ℝ} {A : ℝ} {L : ℝ≥0}
    (hφs : ∀ i, LipschitzWith L (φs i)) (hψs : ∀ i, LipschitzWith L (ψs i))
    (hφB : ∀ i x, |φs i x| ≤ A) (hψB : ∀ i x, |ψs i x| ≤ A)
    (hφ : LipschitzWith L φ) (hψ : LipschitzWith L ψ)
    (hφb : ∀ x, |φ x| ≤ A) (hψb : ∀ x, |ψ x| ≤ A)
    (hφl : ∀ x, Tendsto (fun i => φs i x) atTop (𝓝 (φ x)))
    (hψl : ∀ x, Tendsto (fun i => ψs i x) atTop (𝓝 (ψ x)))
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hdual : ∀ i, (∫x, φs i x ∂νs i)+(∫x, ψs i x ∂ν₁) =
      (wassersteinSq (νs i) ν₁).toReal/2) :
    Tendsto (fun i => (wassersteinSq (νs i) ν₁).toReal) atTop
      (𝓝 (wassersteinSq ν₀ ν₁).toReal) ∧
    (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁) = (wassersteinSq ν₀ ν₁).toReal/2 := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hφi : Integrable φ ν₀ := Integrable.of_bound hφ.continuous.aestronglyMeasurable A
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hφb x)
  have hψi : Integrable ψ ν₁ := Integrable.of_bound hψ.continuous.aestronglyMeasurable A
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hψb x)
  have heS (i : ℕ) (g : X → ℝ) : (∫x, g x ∂νs i) = ∫x, fs i x*g x ∂μ := by
    rw [hd i]
    exact integral_realDensity μ (hfm i) (Eventually.of_forall fun x => (hfn i x).1)
  have he0 (g : X → ℝ) : (∫x, g x ∂ν₀) = ∫x, f x*g x ∂μ := by
    rw [hd0]
    exact integral_realDensity μ hf0m hf0n
  have htφ : Tendsto (fun i => ∫x, φs i x ∂νs i) atTop (𝓝 (∫x, φ x ∂ν₀)) := by
    simp_rw [heS,he0]
    exact bounded_density_potential_integral_tendsto μ p R M A hfm hfn hfs
      (fun i => (hφs i).continuous.measurable) hφB hfl (Eventually.of_forall hφl)
  have htψ : Tendsto (fun i => ∫x, ψs i x ∂ν₁) atTop (𝓝 (∫x, ψ x ∂ν₁)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => A)
    · exact fun i => (hψs i).continuous.aestronglyMeasurable
    · exact integrable_const _
    · exact fun i => Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hψB i x
    · exact Eventually.of_forall hψl
  let d := (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁)
  have htd : Tendsto (fun i => (wassersteinSq (νs i) ν₁).toReal/2) atTop (𝓝 d) := by
    simpa only [hdual,d] using htφ.add htψ
  obtain ⟨π,hπ,hg,hp,hdi,hall⟩ := hX.exists_bounded_entropy_plan K n hn ν₀ ν₁ hC h0 h1 p hR hs0 hs1
  let := hπ
  have hupper : d ≤ (wassersteinSq ν₀ ν₁).toReal/2 := optimal_plan_dual_le hp hdi hφi hψi had
  obtain ⟨u,a,b,ha,hb,hab,hbb,hta,htb,hsa,hsb,hu,had0,hcontact,hgrad⟩ :=
    hp.uniform_bounded_sobolev_potential μ hX.quadratic hX.geodesic ν₀ ν₁
      (Measure.absolutelyContinuous_of_le_smul h0) p hR hs0 hs1
  have hai (ν : Measure X) [IsFiniteMeasure ν] : Integrable a ν :=
    ha.continuous.integrable_of_hasCompactSupport hsa
  have hbi (ν : Measure X) [IsFiniteMeasure ν] : Integrable b ν :=
    hb.continuous.integrable_of_hasCompactSupport hsb
  have heq : (∫x, a x ∂ν₀)+(∫x, b x ∂ν₁) = (wassersteinSq ν₀ ν₁).toReal/2 := by
    apply optimal_plan_dual_eq hp hdi (hai ν₀) (hbi ν₁)
    exact ae_of_ae_map ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable hcontact
  have haB (x : X) : |a x| ≤ 10*R^2 := by rw [abs_of_nonneg (hab x).1]; exact (hab x).2
  have hta0 : Tendsto (fun i => ∫x, a x ∂νs i) atTop (𝓝 (∫x, a x ∂ν₀)) := by
    simp_rw [heS,he0]
    exact bounded_density_potential_integral_tendsto μ p R M (10*R^2) hfm hfn hfs
      (fun _ => ha.continuous.measurable) (fun _ => haB) hfl (Eventually.of_forall fun _ => tendsto_const_nhds)
  have hlow : (wassersteinSq ν₀ ν₁).toReal/2 ≤ d := by
    apply le_of_tendsto_of_tendsto (by simpa only [heq] using hta0.add_const (∫x, b x ∂ν₁)) htd
    apply Eventually.of_forall
    intro i
    obtain ⟨πi,hπi,hgi,hpi,hdii,halli⟩ :=
      hX.exists_bounded_entropy_plan K n hn (νs i) ν₁ hC (hcs i) h1 p hR (hss i) hs1
    exact optimal_plan_dual_le hpi hdii (hai (νs i)) (hbi ν₁) had0
  have he : d = (wassersteinSq ν₀ ν₁).toReal/2 := le_antisymm hupper hlow
  refine ⟨?_,he⟩
  have hh := htd.mul_const 2
  simpa only [he,div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hh


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem common_support_lipschitz_subsequence (p : X) (R A : ℝ) (L : ℝ≥0)
    (fs : ℕ → X → ℝ) (hLip : ∀ i, LipschitzWith L (fs i))
    (hb : ∀ i x, |fs i x| ≤ A) (hs : ∀ i, tsupport (fs i) ⊆ closedBall p R) :
    ∃ (φ : X → ℝ) (s : ℕ → ℕ), StrictMono s ∧
      LipschitzWith L φ ∧ (∀ x, |φ x| ≤ A) ∧
      tsupport φ ⊆ closedBall p R ∧
      TendstoUniformly (fun i => fs (s i)) φ atTop := by
  classical
  let S := closedBall p R
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall p R)
  let cs (i : ℕ) : C(S,ℝ) := ⟨fun x => fs i x,(hLip i).continuous.comp continuous_subtype_val⟩
  have hc (i : ℕ) : LipschitzWith L (cs i) ∧ ∀ x, |cs i x| ≤ A := by
    refine ⟨?_,fun x => hb i x⟩
    exact LipschitzWith.of_dist_le_mul fun x y => (hLip i).dist_le_mul (x:X) (y:X)
  obtain ⟨f,hf,s,hsm,hlim⟩ := (compact_lipschitz_bounded_cmaps (X := S) L A).tendsto_subseq hc
  let φ : X → ℝ := fun x => if hx : x ∈ S then f ⟨x,hx⟩ else 0
  have huni : TendstoUniformly (fun i => fs (s i)) φ atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hd := (tendsto_iff_dist_tendsto_zero.mp hlim).eventually (gt_mem_nhds hε)
    filter_upwards [hd] with i hi x
    by_cases hx : x ∈ S
    · have hh := ContinuousMap.dist_apply_le_dist (f := cs (s i)) (g := f) (⟨x,hx⟩ : S)
      simpa only [φ,dite_eq_left hx,cs,ContinuousMap.coe_mk,dist_comm] using hh.trans_lt hi
    · have hz := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs (s i) ht))
      simp only [φ,dite_eq_right hx,hz,dist_self]
      exact hε
  have hpt (x : X) : Tendsto (fun i => fs (s i) x) atTop (𝓝 (φ x)) := huni.tendsto_at x
  refine ⟨φ,s,hsm,?_,?_,?_,huni⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hpt x).dist (hpt y))
      (Eventually.of_forall fun i => (hLip (s i)).dist_le_mul x y)
  · intro x
    exact le_of_tendsto (hpt x).abs (Eventually.of_forall fun i => hb (s i) x)
  · apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    change x ∉ S at hn
    exact hx (by simp only [φ,dite_eq_right hn])


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem SobolevSpace.resolvent_dense_approx (v : SobolevSpace μ hQ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Lp ℝ 2 μ, dist v (SobolevSpace.resolvent μ hQ g) < ε := by
  have hk : (SobolevSpace.toLpCLM μ hQ).ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    exact Subtype.val_injective
  have hd : (SobolevSpace.resolvent μ hQ).range.topologicalClosure = ⊤ := by
    rw [SobolevSpace.resolvent,←ContinuousLinearMap.orthogonal_ker,hk,
      Submodule.bot_orthogonal_eq_top]
  have hv : v ∈ closure (Set.range (SobolevSpace.resolvent μ hQ)) := by
    change v ∈ (SobolevSpace.resolvent μ hQ).range.topologicalClosure
    rw [hd]
    trivial
  obtain ⟨w,⟨g,rfl⟩,hg⟩ := Metric.mem_closure_iff.mp hv ε hε
  exact ⟨g,hg⟩

theorem SobolevSpace.inner_tendsto_of_toLp_tendsto_bounded
    {us : ℕ → SobolevSpace μ hQ} {u : SobolevSpace μ hQ} {C : ℝ}
    (hb : ∀ i, ‖us i‖ ≤ C)
    (hl : Tendsto (fun i => SobolevSpace.toLp μ hQ (us i)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ u))) (v : SobolevSpace μ hQ) :
    Tendsto (fun i => inner ℝ (us i) v) atTop (𝓝 (inner ℝ u v)) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 0)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε/(4*(C+‖u‖+1))
  have hden : 0 < 4*(C+‖u‖+1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨g,hg⟩ := SobolevSpace.resolvent_dense_approx μ hQ v hδ
  let w := SobolevSpace.resolvent μ hQ g
  have ht : Tendsto (fun i => inner ℝ (us i) w) atTop (𝓝 (inner ℝ u w)) := by
    have he (a : SobolevSpace μ hQ) : inner ℝ a w = inner ℝ g (SobolevSpace.toLp μ hQ a) := by
      rw [real_inner_comm]
      exact SobolevSpace.resolvent_inner μ hQ g a
    simp_rw [he]
    exact (tendsto_const_nhds (x := g)).inner (𝕜 := ℝ) hl
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (ε/2) (by linarith)
  refine ⟨N,fun i hi => ?_⟩
  have hw1 : |inner ℝ (us i) (v-w)| ≤ C*δ := by
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hb i)
      (by simpa only [dist_eq_norm] using hg.le) (norm_nonneg _) hC)
  have hw2 : |inner ℝ u (v-w)| ≤ ‖u‖*δ := by
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dist_eq_norm] using hg.le) (norm_nonneg _))
  have hmid : |inner ℝ (us i) w-inner ℝ u w| < ε/2 := by
    simpa only [Real.dist_eq] using hN i hi
  have hid : inner ℝ (us i) v-inner ℝ u v =
      inner ℝ (us i) (v-w)+(inner ℝ (us i) w-inner ℝ u w)-inner ℝ u (v-w) := by
    simp only [inner_sub_right]
    ring
  have hbd : |inner ℝ (us i) (v-w)+(inner ℝ (us i) w-inner ℝ u w)-inner ℝ u (v-w)| ≤
      |inner ℝ (us i) (v-w)|+|inner ℝ (us i) w-inner ℝ u w|+|inner ℝ u (v-w)| := by
    have h1 := abs_sub (inner ℝ (us i) (v-w)+(inner ℝ (us i) w-inner ℝ u w)) (inner ℝ u (v-w))
    have h2 := abs_add_le (inner ℝ (us i) (v-w)) (inner ℝ (us i) w-inner ℝ u w)
    linarith
  rw [Real.dist_eq,hid]
  apply lt_of_le_of_lt hbd
  have hsmall : (C+‖u‖)*δ ≤ ε/4 := by
    calc
      _ ≤ (C+‖u‖+1)*δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε/4 := by
        dsimp [δ]
        field_simp
  nlinarith

 theorem SobolevSpace.energyForm_tendsto_of_toLp_tendsto_bounded
    {us : ℕ → SobolevSpace μ hQ} {u : SobolevSpace μ hQ} {C : ℝ}
    (hb : ∀ i, ‖us i‖ ≤ C)
    (hl : Tendsto (fun i => SobolevSpace.toLp μ hQ (us i)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ u))) (v : SobolevSpace μ hQ) :
    Tendsto (fun i => energyForm μ hQ (us i) v) atTop (𝓝 (energyForm μ hQ u v)) := by
  exact (SobolevSpace.inner_tendsto_of_toLp_tendsto_bounded μ hQ hb hl v).sub
    (hl.inner tendsto_const_nhds)

 theorem SobolevSpace.energyForm_tendsto_weak_strong
    {us vs : ℕ → SobolevSpace μ hQ} {u v : SobolevSpace μ hQ} {C : ℝ}
    (hb : ∀ i, ‖us i‖ ≤ C)
    (hl : Tendsto (fun i => SobolevSpace.toLp μ hQ (us i)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ u))) (hv : Tendsto vs atTop (𝓝 v)) :
    Tendsto (fun i => energyForm μ hQ (us i) (vs i)) atTop (𝓝 (energyForm μ hQ u v)) := by
  have hd : Tendsto (fun i => inner ℝ (us i) (vs i-v)) atTop (𝓝 (0:ℝ)) := by
    apply squeeze_zero_norm (a := fun i => C*‖vs i-v‖)
    · intro i
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _))
    · simpa only [sub_self,norm_zero,mul_zero] using (hv.sub (tendsto_const_nhds (x := v))).norm.const_mul C
  have hi := hd.add (SobolevSpace.inner_tendsto_of_toLp_tendsto_bounded μ hQ hb hl v)
  simp only [inner_sub_right,sub_add_cancel,zero_add] at hi
  exact hi.sub (hl.inner ((SobolevSpace.toLpCLM μ hQ).continuous.tendsto v |>.comp hv))


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem SobolevSpace.eq_of_lipschitz_rep (u : SobolevSpace μ hQ)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f)
    (hr : f =ᵐ[μ] SobolevSpace.toLp μ hQ u) :
    u = SobolevSpace.ofLipschitzCompact μ hQ hf hs := by
  apply Subtype.ext
  apply Lp.ext
  exact hr.symm.trans (SobolevSpace.ofLipschitzCompact_coe μ hQ hf hs).symm

theorem SobolevSpace.norm_le_of_common_support (p : X) (R A : ℝ) (L : ℝ≥0)
    (u : SobolevSpace μ hQ) {f : X → ℝ} (hf : LipschitzWith L f)
    (hb : ∀ x, |f x| ≤ A) (hs : tsupport f ⊆ closedBall p R)
    (hr : f =ᵐ[μ] SobolevSpace.toLp μ hQ u) :
    ‖u‖ ≤ Real.sqrt ((A^2+(L:ℝ)^2)*(μ (closedBall p R)).toReal) := by
  have hsc : HasCompactSupport f := (isCompact_closedBall p R).of_isClosed_subset (isClosed_tsupport f) hs
  have he := SobolevSpace.ofLipschitzCompact_energy_le μ hQ hf hsc
    measurableSet_closedBall (isCompact_closedBall p R).measure_lt_top.ne hs
  rw [←SobolevSpace.eq_of_lipschitz_rep μ hQ u hf hsc hr] at he
  let B := (closedBall p R).indicator (fun _ : X => A^2)
  have hB : Integrable B μ :=
    (integrableOn_const (isCompact_closedBall p R).measure_lt_top.ne).integrable_indicator measurableSet_closedBall
  have hi : Integrable (fun x => SobolevSpace.toLp μ hQ u x^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      (Lp.memLp (SobolevSpace.toLp μ hQ u)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hbd : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ u x^2 ≤ B x := by
    filter_upwards [hr] with x hx
    rw [←hx]
    by_cases hm : x ∈ closedBall p R
    · dsimp only [B]
      rw [indicator_of_mem hm]
      have hh := hb x
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh)).mpr hh
    · dsimp only [B]
      rw [indicator_of_notMem hm,image_eq_zero_of_notMem_tsupport (fun ht => hm (hs ht))]
      norm_num
  have hn := integral_mono_ae hi hB hbd
  have hBI : (∫x, B x ∂μ) = A^2*(μ (closedBall p R)).toReal := by
    dsimp only [B]
    rw [integral_indicator_const _ measurableSet_closedBall]
    simp only [smul_eq_mul,Measure.real,mul_comm]
  rw [integral_sq_Lp,hBI] at hn
  have hnorm := SobolevSpace.norm_sq μ hQ u
  unfold SobolevSpace.normSq at hnorm
  have hsqrt := Real.sq_sqrt (show 0 ≤ (A^2+(L:ℝ)^2)*(μ (closedBall p R)).toReal by positivity)
  nlinarith [norm_nonneg u,Real.sqrt_nonneg ((A^2+(L:ℝ)^2)*(μ (closedBall p R)).toReal)]

theorem SobolevSpace.toLp_tendsto_of_common_support (p : X) (R A : ℝ) (L : ℝ≥0)
    {us : ℕ → SobolevSpace μ hQ} {u : SobolevSpace μ hQ}
    {fs : ℕ → X → ℝ} {f : X → ℝ}
    (_ : ∀ i, LipschitzWith L (fs i)) (_ : LipschitzWith L f)
    (hbs : ∀ i x, |fs i x| ≤ A) (hb : ∀ x, |f x| ≤ A)
    (hss : ∀ i, tsupport (fs i) ⊆ closedBall p R) (hs : tsupport f ⊆ closedBall p R)
    (hrs : ∀ i, fs i =ᵐ[μ] SobolevSpace.toLp μ hQ (us i))
    (hr : f =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (ht : ∀ x, Tendsto (fun i => fs i x) atTop (𝓝 (f x))) :
    Tendsto (fun i => SobolevSpace.toLp μ hQ (us i)) atTop (𝓝 (SobolevSpace.toLp μ hQ u)) := by
  have hms (i : ℕ) : MemLp (fs i) 2 μ := (Lp.memLp (SobolevSpace.toLp μ hQ (us i))).ae_eq (hrs i).symm
  have hm : MemLp f 2 μ := (Lp.memLp (SobolevSpace.toLp μ hQ u)).ae_eq hr.symm
  have he (i : ℕ) : (hms i).toLp (fs i) = SobolevSpace.toLp μ hQ (us i) := by
    apply Lp.ext
    exact (hms i).coeFn_toLp.trans (hrs i)
  have he0 : hm.toLp f = SobolevSpace.toLp μ hQ u := by
    apply Lp.ext
    exact hm.coeFn_toLp.trans hr
  have hh := L2Differentiation.toLp_tendsto_of_dominated μ hms hm
    ((closedBall p R).indicator (fun _ => 4*A^2))
    ((integrableOn_const (isCompact_closedBall p R).measure_lt_top.ne).integrable_indicator measurableSet_closedBall)
    (Eventually.of_forall fun i => ?_) (Eventually.of_forall ht)
  · simpa only [he,he0] using hh
  · filter_upwards with x
    by_cases hx : x ∈ closedBall p R
    · rw [indicator_of_mem hx]
      have h1 := abs_le.mp (hbs i x)
      have h2 := abs_le.mp (hb x)
      have hA : 0 ≤ A := (abs_nonneg _).trans (hb x)
      nlinarith [sq_nonneg (fs i x-f x),sq_nonneg (fs i x+f x)]
    · rw [indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport (fun ht => hx (hss i ht)),
        image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))]
      norm_num


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

theorem SobolevSpace.common_support_dual_subsequence (p : X) (R A : ℝ) (L : ℝ≥0)
    (us : ℕ → SobolevSpace μ hQ) (φs ψs : ℕ → X → ℝ)
    (hφ : ∀ i, LipschitzWith L (φs i)) (hψ : ∀ i, LipschitzWith L (ψs i))
    (hbφ : ∀ i x, |φs i x| ≤ A) (hbψ : ∀ i x, |ψs i x| ≤ A)
    (hsφ : ∀ i, tsupport (φs i) ⊆ closedBall p R)
    (hsψ : ∀ i, tsupport (ψs i) ⊆ closedBall p R)
    (hre : ∀ i, φs i =ᵐ[μ] SobolevSpace.toLp μ hQ (us i)) :
    ∃ (u : SobolevSpace μ hQ) (φ ψ : X → ℝ) (s : ℕ → ℕ),
      StrictMono s ∧ LipschitzWith L φ ∧ LipschitzWith L ψ ∧
      (∀ x, |φ x| ≤ A) ∧ (∀ x, |ψ x| ≤ A) ∧
      tsupport φ ⊆ closedBall p R ∧ tsupport ψ ⊆ closedBall p R ∧
      (φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (∀ x, Tendsto (fun i => φs (s i) x) atTop (𝓝 (φ x))) ∧
      (∀ x, Tendsto (fun i => ψs (s i) x) atTop (𝓝 (ψ x))) ∧
      (∀ i, ‖us (s i)‖ ≤ Real.sqrt ((A^2+(L:ℝ)^2)*(μ (closedBall p R)).toReal)) ∧
      Tendsto (fun i => SobolevSpace.toLp μ hQ (us (s i))) atTop (𝓝 (SobolevSpace.toLp μ hQ u)) := by
  obtain ⟨φ,s,hsm,hφl,hφb,hφsup,hφlim⟩ := common_support_lipschitz_subsequence p R A L φs hφ hbφ hsφ
  obtain ⟨ψ,t,htm,hψl,hψb,hψsup,hψlim⟩ := common_support_lipschitz_subsequence p R A L
    (fun i => ψs (s i)) (fun i => hψ (s i)) (fun i => hbψ (s i)) (fun i => hsψ (s i))
  have hcφ : HasCompactSupport φ := (isCompact_closedBall p R).of_isClosed_subset (isClosed_tsupport φ) hφsup
  let u := SobolevSpace.ofLipschitzCompact μ hQ hφl hcφ
  have hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u := (SobolevSpace.ofLipschitzCompact_coe μ hQ hφl hcφ).symm
  have hφpt (x : X) : Tendsto (fun i => φs (s (t i)) x) atTop (𝓝 (φ x)) :=
    (hφlim.tendsto_at x).comp htm.tendsto_atTop
  refine ⟨u,φ,ψ,s ∘ t,hsm.comp htm,hφl,hψl,hφb,hψb,hφsup,hψsup,hu,hφpt,
    fun x => hψlim.tendsto_at x,?_,?_⟩
  · intro i
    exact SobolevSpace.norm_le_of_common_support μ hQ p R A L (us (s (t i)))
      (hφ _) (hbφ _) (hsφ _) (hre _)
  · exact SobolevSpace.toLp_tendsto_of_common_support μ hQ p R A L
      (fun i => hφ _) hφl (fun i => hbφ _) hφb (fun i => hsφ _) hφsup (fun i => hre _) hu hφpt


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.quantitative_H1_energy_subgradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (ρ : SobolevSpace (hausdorff n X) hX.quadratic)
    (M : ℝ≥0)
    (hρ : ∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp _ hX.quadratic ρ x ∧
      SobolevSpace.toLp _ hX.quadratic ρ x ≤ M)
    (hρS : ∀ᵐ x ∂hausdorff n X, SobolevSpace.toLp _ hX.quadratic ρ x ≠ 0 → dist p x ≤ R)
    (hρM : (∫x, SobolevSpace.toLp _ hX.quadratic ρ x ∂hausdorff n X) = 1)
    (hν : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ x))) :
    ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (φ ψ : X → ℝ),
      LipschitzWith ⟨5*(2*(max R 0+1)),by positivity⟩ φ ∧
      LipschitzWith ⟨5*(2*(max R 0+1)),by positivity⟩ ψ ∧
      (∀ x, |φ x| ≤ 10*(2*(max R 0+1))^2) ∧ (∀ x, |ψ x| ≤ 10*(2*(max R 0+1))^2) ∧
      tsupport φ ⊆ closedBall p (6*(2*(max R 0+1))) ∧
      tsupport ψ ⊆ closedBall p (6*(2*(max R 0+1))) ∧
      HasCompactSupport φ ∧ HasCompactSupport ψ ∧
      (φ =ᵐ[hausdorff n X] SobolevSpace.toLp _ hX.quadratic u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁) = (wassersteinSq ν₀ ν₁).toReal/2 ∧
      -energyForm (hausdorff n X) hX.quadratic u ρ ≤
        boltzmannEntropy (hausdorff n X) ν₁-boltzmannEntropy (hausdorff n X) ν₀-
        (K/2)*(wassersteinSq ν₀ ν₁).toReal := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨qs,hs,hq,hLip,hrep,hb,hsup,hm,hpt,hEnt⟩ :=
    SobolevSpace.quantitative_strong_probability_square_recovery μ hX.quadratic ρ M hρ p hρS hρM
  let B := 2*(max R 0+1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hRB : R ≤ B := by dsimp [B]; linarith [le_max_left R 0,le_max_right R 0]
  have hsc (i : ℕ) : HasCompactSupport (hs i) := by
    apply (isCompact_closedBall p B).of_isClosed_subset (isClosed_tsupport _) (closure_minimal _ isClosed_closedBall)
    intro x hx
    simpa only [mem_closedBall,dist_comm] using hsup i x hx
  let νs : ℕ → Measure X := fun i => μ.withDensity (fun x => ENNReal.ofReal (hs i x^2))
  let (i : ℕ) : IsProbabilityMeasure (νs i) :=
    squareDensity_probability μ (compactSquare_integrable μ (hLip i).choose_spec.continuous (hsc i)) (hm i)
  let D : ℝ≥0∞ := max C (ENNReal.ofReal (2*M))
  have hD : D ≠ ∞ := by
    simp only [D, ne_eq, max_eq_top, not_or]
    exact ⟨hC, ENNReal.ofReal_ne_top⟩
  have h0D : ν₀ ≤ D • μ := h0.trans (by gcongr; exact le_max_left _ _)
  have h1D : ν₁ ≤ D • μ := h1.trans (by gcongr; exact le_max_left _ _)
  have hDs (i : ℕ) : νs i ≤ D • μ := by
    calc
      _ ≤ μ.withDensity (fun _ => ENNReal.ofReal (2*M)) :=
        withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hb i x).2)
      _ = ENNReal.ofReal (2*M) • μ := withDensity_const _
      _ ≤ D • μ := by gcongr; exact le_max_right _ _
  have hSqs (i : ℕ) (x : X) (hx : hs i x^2 ≠ 0) : x ∈ closedBall p B := by
    have hh : hs i x ≠ 0 := by intro hz; apply hx; rw [hz]; norm_num
    simpa only [mem_closedBall,dist_comm] using hsup i x hh
  have hSs (i : ℕ) : ∀ᵐ x ∂νs i, dist x p ≤ B := by
    apply (ae_withDensity_iff ((hLip i).choose_spec.continuous.measurable.pow_const 2).ennreal_ofReal).mpr
    filter_upwards with x hx
    apply hSqs i x
    intro hz
    exact hx (by rw [hz,ENNReal.ofReal_zero])
  have hνs (i : ℕ) : νs i = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hX.quadratic (qs i) x)) := by
    apply withDensity_congr_ae
    exact (hrep i).symm.fun_comp ENNReal.ofReal
  have hcore (i : ℕ) := hX.linear_radius_sqrt_core_energy_subgradient K n hn (νs i) ν₁ hD
    (hDs i) h1D p hB (hSs i) (hs1.mono fun x hx => hx.trans hRB) (qs i)
    (hLip i).choose_spec (fun x => (hb i x).1)
    ((hLip i).choose_spec.continuous.integrable_of_hasCompactSupport (hsc i)) (hrep i) (hνs i)
  choose us φs ψs hφs hψs hφb hψb hφsup hψsup hφsc hψsc hus hads hduals hineqs using hcore
  let L : ℝ≥0 := ⟨5*B,by positivity⟩
  have hφabs (i : ℕ) (x : X) : |φs i x| ≤ 10*B^2 := by
    rw [abs_of_nonneg (hφb i x).1]
    exact (hφb i x).2
  have hψabs (i : ℕ) (x : X) : |ψs i x| ≤ 10*B^2 := by
    rw [abs_of_nonpos (hψb i x).2]
    linarith [(hψb i x).1]
  obtain ⟨u,φ,ψ,s,hsm,hφ,hψ,hφB,hψB,hφS,hψS,hu,hφlim,hψlim,hub,hul⟩ :=
    SobolevSpace.common_support_dual_subsequence μ hX.quadratic p (B+(5*B)) (10*B^2) L
      us φs ψs hφs hψs hφabs hψabs hφsup hψsup hus
  have had (x y : X) : φ x+ψ y ≤ dist x y^2/2 :=
    le_of_tendsto ((hφlim x).add (hψlim y)) (Eventually.of_forall fun i => hads (s i) x y)
  have heL := SobolevSpace.energyForm_tendsto_weak_strong μ hX.quadratic hub hul (hq.comp hsm.tendsto_atTop)
  have hρm : Measurable (SobolevSpace.toLp μ hX.quadratic ρ : X → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have hpt' : ∀ᵐ x ∂μ, Tendsto (fun i => hs (s i) x^2) atTop (𝓝 (SobolevSpace.toLp μ hX.quadratic ρ x)) :=
    hpt.mono fun x hx => hx.comp hsm.tendsto_atTop
  have hcost := hX.bounded_density_dual_limit K n hn ν₀ ν₁ (fun i => νs (s i)) hD h0D h1D
    (fun i => hDs (s i)) p hB (hs0.mono fun x hx => hx.trans hRB) (hs1.mono fun x hx => hx.trans hRB)
    (fun i => hSs (s i))
    (fun i => (hLip (s i)).choose_spec.continuous.measurable.pow_const 2)
    (M := (2*M:ℝ)) (fun i x => ⟨sq_nonneg _,(hb (s i) x).2⟩) (fun i => hSqs (s i))
    hρm (hρ.mono fun x hx => hx.1) hpt' (fun i => rfl) hν
    (fun i => hφs (s i)) (fun i => hψs (s i)) (fun i => hφabs (s i)) (fun i => hψabs (s i))
    hφ hψ hφB hψB hφlim hψlim had (fun i => hduals (s i))
  have hEL : Tendsto (fun i => boltzmannEntropy μ (νs (s i))) atTop (𝓝 (boltzmannEntropy μ ν₀)) := by
    have he0 : boltzmannEntropy μ ν₀ = ∫x, SobolevSpace.toLp μ hX.quadratic ρ x*
        Real.log (SobolevSpace.toLp μ hX.quadratic ρ x) ∂μ := by
      rw [hν]
      exact realDensity_entropy μ hρm (hρ.mono fun x hx => hx.1)
    have hes (i : ℕ) : boltzmannEntropy μ (νs i) = ∫x, hs i x^2*Real.log (hs i x^2) ∂μ :=
      squareDensity_entropy μ (hLip i).choose_spec.continuous.measurable
    rw [he0]
    simp_rw [hes]
    exact hEnt.comp hsm.tendsto_atTop
  have hBS : B+(5*B) = 6*B := by ring
  refine ⟨u,φ,ψ,hφ,hψ,hφB,hψB,by simpa only [hBS] using hφS,by simpa only [hBS] using hψS,
    (isCompact_closedBall p _).of_isClosed_subset (isClosed_tsupport φ) hφS,
    (isCompact_closedBall p _).of_isClosed_subset (isClosed_tsupport ψ) hψS,
    hu,had,hcost.2,?_⟩
  exact le_of_tendsto_of_tendsto heL.neg
    (((tendsto_const_nhds (x := boltzmannEntropy μ ν₁)).sub hEL).sub (hcost.1.const_mul (K/2)))
    (Eventually.of_forall fun i => hineqs (s i))


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem FullCD.compact_dual_le (μ : Measure X) {K : ℝ} {n : ℕ} (hcd : FullCD μ K n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (h0 : ν₀ ≪ μ) (h1 : ν₁ ≪ μ) (h02 : FiniteSecondMoment ν₀) (h12 : FiniteSecondMoment ν₁)
    {φ ψ : X → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφs : HasCompactSupport φ) (hψs : HasCompactSupport ψ)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2) :
    (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁) ≤ (wassersteinSq ν₀ ν₁).toReal/2 := by
  obtain ⟨π,hp,_,hopt,_⟩ := hcd ν₀ ν₁ inferInstance inferInstance h0 h1 h02 h12
  have hm0 := h02
  obtain ⟨p,_⟩ := hm0
  exact optimal_plan_dual_le hopt
    (optimalPlan_dist_sq_integrable ν₀ ν₁ π hopt p (h02.integrable_dist_sq p) (h12.integrable_dist_sq p))
    (hφ.integrable_of_hasCompactSupport hφs) (hψ.integrable_of_hasCompactSupport hψs) had

variable (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] [SeparableSpace X] [μ.Regular] in
theorem energyForm_abs_le_norm (u v : SobolevSpace μ hQ) :
    |energyForm μ hQ u v| ≤ 2*‖u‖*‖v‖ := by
  unfold energyForm
  calc
    _ ≤ |inner ℝ u v|+|inner ℝ (SobolevSpace.toLp μ hQ u) (SobolevSpace.toLp μ hQ v)| := abs_sub _ _
    _ ≤ ‖u‖*‖v‖+‖SobolevSpace.toLp μ hQ u‖*‖SobolevSpace.toLp μ hQ v‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ‖u‖*‖v‖+‖u‖*‖v‖ := add_le_add le_rfl
      (mul_le_mul (SobolevSpace.norm_toLp_le μ hQ u) (SobolevSpace.norm_toLp_le μ hQ v)
        (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem heat_cutoff_dual_secant {K : ℝ} {n : ℕ} (hcd : FullCD μ K n)
    (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (ν : Measure X) [IsProbabilityMeasure ν]
    (hν : ν ≪ μ) (hν2 : FiniteSecondMoment ν)
    {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    [IsProbabilityMeasure (heatMeasure μ hQ t f)]
    (hm2 : FiniteSecondMoment (heatMeasure μ hQ t f))
    (ρ u : SobolevSpace μ hQ) (η : Measure X)
    (hρ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ ρ x)
    (hη : η = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    {φ ψ : X → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφs : HasCompactSupport φ) (hψs : HasCompactSupport ψ)
    (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hdual : (∫x, φ x ∂η)+(∫x, ψ x ∂ν) = (wassersteinSq η ν).toReal/2)
    {E : ℝ} (hE : -energyForm μ hQ u ρ ≤ E) :
    ((wassersteinSq η ν).toReal-(wassersteinSq (heatMeasure μ hQ t f) ν).toReal)/(2*h) ≤
      E+‖u‖*((2*(1+1/(t/2)))^2*‖f‖*h)+
      ‖u‖*(h⁻¹+2)*‖ρ-heatSobolev μ hQ (t+h) (add_pos ht hh) f‖ := by
  have hw := hcd.compact_dual_le μ (heatMeasure μ hQ t f) ν
    (withDensity_absolutelyContinuous _ _) hν hm2 hν2 hφ hψ hφs hψs had
  rw [integral_heatMeasure μ hQ f hf t φ] at hw
  have he0 : (∫x, φ x*heatAt μ hQ t f x ∂μ) = inner ℝ (heatAt μ hQ t f) (SobolevSpace.toLp μ hQ u) := by
    rw [L2.inner_def]
    exact integral_congr_ae (hu.mono fun x hx => by simp only [hx,Real.inner_apply,mul_comm])
  have he1 : (∫x, φ x ∂η) = inner ℝ (SobolevSpace.toLp μ hQ ρ) (SobolevSpace.toLp μ hQ u) := by
    rw [hη,integral_withDensity_eq_integral_toReal_smul₀
      (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ ρ)).aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu,hρ] using fun x hx hn => by
      simp only [hx,ENNReal.toReal_ofReal hn,smul_eq_mul,Real.inner_apply]
  rw [he0] at hw
  rw [he1] at hdual
  let q := heatSobolev μ hQ (t+h) (add_pos ht hh) f
  let v := h⁻¹ • (heatAt μ hQ (t+h) f-heatAt μ hQ t f)
  let A := heatGeneratorAt μ hQ (t+h) f
  have hc := real_inner_le_norm (v+A) (SobolevSpace.toLp μ hQ u)
  have hc' : inner ℝ v (SobolevSpace.toLp μ hQ u)+energyForm μ hQ u q ≤
      ((2*(1+1/(t/2)))^2*‖f‖*h)*‖u‖ := by
    have he : energyForm μ hQ u q = inner ℝ A (SobolevSpace.toLp μ hQ u) := by
      rw [energyForm_comm,heatGenerator_form]
      simp only [A,heatGeneratorAt_of_pos μ hQ (t+h) (add_pos ht hh)]
    rw [he,←inner_add_left]
    exact hc.trans (mul_le_mul (heatEviRemainder_le μ hQ f ht hh)
      (SobolevSpace.norm_toLp_le μ hQ u) (norm_nonneg _) (by positivity))
  have hd : |inner ℝ (SobolevSpace.toLp μ hQ (ρ-q)) (SobolevSpace.toLp μ hQ u)| ≤ ‖ρ-q‖*‖u‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (SobolevSpace.norm_toLp_le μ hQ (ρ-q))
      (SobolevSpace.norm_toLp_le μ hQ u) (norm_nonneg _) (norm_nonneg _))
  have he := (le_abs_self (energyForm μ hQ u (ρ-q))).trans (energyForm_abs_le_norm μ hQ u (ρ-q))
  rw [energyForm_sub_right] at he
  have hs : ((wassersteinSq η ν).toReal-(wassersteinSq (heatMeasure μ hQ t f) ν).toReal)/(2*h) ≤
      inner ℝ v (SobolevSpace.toLp μ hQ u)+h⁻¹*(‖ρ-q‖*‖u‖) := by
    have hbase : ((wassersteinSq η ν).toReal-(wassersteinSq (heatMeasure μ hQ t f) ν).toReal)/2 ≤
        inner ℝ (SobolevSpace.toLp μ hQ ρ-heatAt μ hQ t f) (SobolevSpace.toLp μ hQ u) := by
      rw [inner_sub_left]; linarith
    have hsplit : SobolevSpace.toLp μ hQ ρ-heatAt μ hQ t f =
        (heatAt μ hQ (t+h) f-heatAt μ hQ t f)+SobolevSpace.toLp μ hQ (ρ-q) := by
      simp only [map_sub,q,heatSobolev_toLp]; abel
    rw [hsplit,inner_add_left] at hbase
    have hh' := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hh.le)
    have hd' := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hd) (inv_nonneg.mpr hh.le)
    dsimp only [v]
    rw [inner_smul_left]
    simp only [RCLike.conj_to_real]
    calc
      _ = h⁻¹*(((wassersteinSq η ν).toReal-(wassersteinSq (heatMeasure μ hQ t f) ν).toReal)/2) := by ring
      _ ≤ _ := by linarith
  change _ ≤ E+‖u‖*((2*(1+1/(t/2)))^2*‖f‖*h)+‖u‖*(h⁻¹+2)*‖ρ-q‖
  nlinarith only [hs,hE,he,hc']


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

theorem SobolevSpace.linearRadiusPotential_norm_le (p : X) {A B : ℝ}
    (hA : 0 ≤ A) (_ : 0 ≤ B)
    (hvol : ∀ r : ℝ, 1 ≤ r → μ.real (closedBall p (2*r)) ≤ A*Real.exp (B*r))
    {R : ℝ} (hR : 1 ≤ R) (u : SobolevSpace μ hQ) {φ : X → ℝ}
    (hφ : LipschitzWith ⟨5*(2*(max R 0+1)),by positivity⟩ φ)
    (hb : ∀ x, |φ x| ≤ 10*(2*(max R 0+1))^2)
    (hs : tsupport φ ⊆ closedBall p (6*(2*(max R 0+1))))
    (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) :
    ‖u‖ ≤ 1000*(A+1)*Real.exp ((6*B+2)*R) := by
  have hR0 : 0 ≤ R := by linarith
  have hr : max R 0 = R := max_eq_left hR0
  have hB0 : 0 ≤ 2*(max R 0+1) := by positivity
  have hex : R ≤ Real.exp R := by linarith [Real.add_one_le_exp R]
  have he2 : R^2 ≤ Real.exp (2*R) := by
    calc
      _ ≤ (Real.exp R)^2 := (sq_le_sq₀ hR0 (Real.exp_pos R).le).mpr hex
      _ = _ := by rw [←Real.exp_nat_mul]; congr 1
  have hb' : ∀ x, |φ x| ≤ 160*Real.exp (2*R) := by
    intro x
    apply (hb x).trans
    rw [hr]
    have hsum : (2*(R+1))^2 ≤ (4*R)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    nlinarith
  have hL : (5*(2*(max R 0+1))) ≤ 20*Real.exp (2*R) := by
    rw [hr]
    have hRe : R ≤ Real.exp (2*R) := hex.trans (Real.exp_le_exp.mpr (by linarith))
    linarith
  let L : ℝ≥0 := ⟨20*Real.exp (2*R),by positivity⟩
  have hφ' : LipschitzWith L φ := hφ.weaken hL
  have hs' : tsupport φ ⊆ closedBall p (24*R) := hs.trans (closedBall_subset_closedBall (by rw [hr]; linarith))
  have hv := hvol (12*R) (by linarith)
  rw [show 2*(12*R) = 24*R by ring] at hv
  have hn := SobolevSpace.norm_le_of_common_support μ hQ p (24*R) (160*Real.exp (2*R)) L u hφ' hb' hs' hu
  apply hn.trans
  have htarget : 0 ≤ 1000*(A+1)*Real.exp ((6*B+2)*R) := by positivity
  apply (Real.sqrt_le_iff).mpr
  refine ⟨htarget,?_⟩
  have hA' : A ≤ (A+1)^2 := by nlinarith [sq_nonneg A]
  have hc : (160*Real.exp (2*R))^2+(L:ℝ)^2 ≤ 1000^2*Real.exp (4*R) := by
    change (160*Real.exp (2*R))^2+(20*Real.exp (2*R))^2 ≤ _
    have he : (Real.exp (2*R))^2 = Real.exp (4*R) := by rw [←Real.exp_nat_mul]; congr 1; ring
    simp only [mul_pow]
    rw [he]
    nlinarith [Real.exp_pos (4*R)]
  calc
    _ ≤ (1000^2*Real.exp (4*R))*(A*Real.exp (B*(12*R))) :=
      mul_le_mul hc hv ENNReal.toReal_nonneg (by positivity)
    _ ≤ (1000^2*Real.exp (4*R))*((A+1)^2*Real.exp (B*(12*R))) := by gcongr
    _ = (1000*(A+1)*Real.exp ((6*B+2)*R))^2 := by
      rw [mul_pow,mul_pow,←Real.exp_nat_mul]
      have he : 2*((6*B+2)*R) = 4*R+B*(12*R) := by ring
      norm_num only [Nat.cast_ofNat]
      rw [he,Real.exp_add]
      ring


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.cutoff_heat_secant
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → (hausdorff n X).real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfi : Integrable f (hausdorff n X)) (hfm : ∫x, f x ∂hausdorff n X = 1)
    {r : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≤ ENNReal.ofReal C • hausdorff n X)
    {R t h : ℝ} (hR : 1 ≤ R) (ht : 0 < t) (hh : 0 < h)
    (hνS : ∀ᵐ x ∂ν, dist x p ≤ 2*R)
    (hm : (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt (hausdorff n X) hX.quadratic (t+h) f x ∂hausdorff n X) :
    let μ := hausdorff n X
    let η := radialHeatMeasure μ hX.quadratic p R (t+h) f
    let ρ := radialHeatSobolev μ hX.quadratic p (zero_lt_one.trans_le hR) (add_pos ht hh) f C
    ((wassersteinSq η ν).toReal-(wassersteinSq (heatMeasure μ hX.quadratic t f) ν).toReal)/(2*h) ≤
      boltzmannEntropy μ ν-boltzmannEntropy μ η-(K/2)*(wassersteinSq η ν).toReal+
      (1000*(A+1)*Real.exp ((12*B+4)*R)) *
        (((2*(1+1/(t/2)))^2*‖f‖*h)+(h⁻¹+2)*‖ρ-heatSobolev μ hX.quadratic (t+h) (add_pos ht hh) f‖) := by
  let μ := hausdorff n X
  let η := radialHeatMeasure μ hX.quadratic p R (t+h) f
  let ρ := radialHeatSobolev μ hX.quadratic p (zero_lt_one.trans_le hR) (add_pos ht hh) f C
  have hd := radialHeatMeasure_data μ hX.quadratic p hA hB hvol f C hf0 hfC hfi hfm
    (zero_lt_one.trans_le hR) (add_pos ht hh) hm
  let : IsProbabilityMeasure η := hd.1
  have hv := radialHeatSobolev_data μ hX.quadratic p hA hB hvol f C hf0 hfC hfi hfm
    (zero_lt_one.trans_le hR) (add_pos ht hh) hm
  have hη := radialHeatSobolev_measure μ hX.quadratic p (zero_lt_one.trans_le hR) (add_pos ht hh) f C hf0 hfC
  have hν' : ν ≤ ENNReal.ofReal (2*C) • μ := hν.trans (by gcongr ; nlinarith [C.coe_nonneg])
  obtain ⟨u,φ,ψ,hφ,hψ,hφb,hψb,hφS,hψS,hφs,hψs,hu,had,hdual,hE⟩ :=
    hX.quantitative_H1_energy_subgradient K n hn η ν ENNReal.ofReal_ne_top hd.2.1 hν'
      p (by positivity : 0 ≤ 2*R) hd.2.2 hνS ρ (2*C) hv.1 hv.2.1 hv.2.2.2 hη
  have hνac : ν ≪ μ := (Measure.absolutelyContinuous_of_le hν).trans Measure.smul_absolutelyContinuous
  have hm2 := heatAt_finiteSecondMoment μ hX.quadratic p hA hB hvol f hf0 hfs ht.le
  let : IsProbabilityMeasure (heatMeasure μ hX.quadratic t f) := by
    apply realDensity_probability μ (heatAt_integrable μ hX.quadratic t f hfi)
      ((Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hX.quadratic t f hf0))
    exact (heatAt_integral_eq_of_exponential_volume μ hX.quadratic p hA hB hvol f hf0 hfi ht.le).trans hfm
  have hs := heat_cutoff_dual_secant μ hX.quadratic hX.cd f hf0 ν hνac
    (finiteSecondMoment_of_ae_dist_le ν p hνS) ht hh hm2 ρ u η (hv.1.mono fun _ hx => hx.1)
    hη hφ.continuous hψ.continuous hφs hψs hu had hdual hE
  have hun : ‖u‖ ≤ 1000*(A+1)*Real.exp ((12*B+4)*R) := by
    have hb := SobolevSpace.linearRadiusPotential_norm_le μ hX.quadratic p hA hB hvol
      (by linarith : 1 ≤ 2*R) u hφ hφb hφS hu
    convert hb using 1
    congr 1
    congr 1
    ring
  change _ ≤ _+_ at hs ⊢
  calc
    _ ≤ _ := hs
    _ = (boltzmannEntropy μ ν-boltzmannEntropy μ η-(K/2)*(wassersteinSq η ν).toReal)+
        ‖u‖*(((2*(1+1/(t/2)))^2*‖f‖*h)+(h⁻¹+2)*‖ρ-heatSobolev μ hX.quadratic (t+h) (add_pos ht hh) f‖) := by ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right hun
      positivity


end

 
section

 

open Set Filter MeasureTheory Metric Bornology TopologicalSpace
open scoped Topology ENNReal NNReal

 

theorem metricAC_uniformContinuousOn {Y : Type*} [PseudoMetricSpace Y]
    {f : ℝ → Y} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    UniformContinuousOn f (uIcc a b) := by
  simp only [UniformContinuousOn, Filter.tendsto_iff_comap,
    AbsolutelyContinuousOnInterval.uniformity_eq_comap_totalLengthFilter]
  simp only [AbsolutelyContinuousOnInterval, Filter.tendsto_iff_comap] at hf
  convert! Filter.comap_mono hf
  · simp only [comap_inf, comap_principal]
    congr
    ext p
    simp only [AbsolutelyContinuousOnInterval.disjWithin, Finset.mem_range,
      preimage_ofPred_eq, Nat.lt_one_iff, forall_eq, mem_ofPred_eq, mem_prod]
    simp
  · simp [AbsolutelyContinuousOnInterval.totalLengthFilter, comap_comap, Function.comp_def]

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X]

theorem NoncollapsedRCD.compact_heat_entropy_continuousAt
    (K : ℝ) (n : ℕ) [IsFiniteMeasure (hausdorff n X)]
    (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s => boltzmannEntropy (hausdorff n X)
      (heatMeasure (hausdorff n X) hX.quadratic s f)) t := by
  let μ := hausdorff n X
  obtain ⟨R, hR, hRb⟩ := (isBounded_univ.mpr (inferInstance : BoundedSpace X)).subset_closedBall_lt (0 : ℝ) p
  have hfs : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ R :=
    ae_of_all _ fun x _ => by simpa [dist_comm] using hRb (mem_univ x)
  obtain ⟨A, B, hA, hB, hvol⟩ := hX.exponential_volume K n hn p
  have hac := heatAt_entropy_absolutelyContinuous_nonneg μ hX.quadratic p hA hB hvol
    f hf0 ((Lp.memLp f).integrable (by norm_num)) hfs (a := 0) (b := t+1) le_rfl (by linarith)
  have hc : ContinuousOn (fun s => boltzmannEntropy μ (heatMeasure μ hX.quadratic s f)) (Icc 0 (t+1)) := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ t+1 by linarith),
      boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0] using hac.continuousOn
  exact hc.continuousAt (Icc_mem_nhds ht (by linarith))

theorem NoncollapsedRCD.compact_heat_probability_continuousAt
    (K : ℝ) (n : ℕ) [IsFiniteMeasure (hausdorff n X)]
    (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f)
    (hfs : ∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (hfm : ∫ x, f x ∂hausdorff n X = 1)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C)
    {t : ℝ} (ht : 0 < t) :
    letI := ACWassersteinProbability.metric (hausdorff n X) K n hX.cd
    ContinuousAt (hX.heatProbability K n hn p f hf0 hfs hfm) t := by
  let := ACWassersteinProbability.metric (hausdorff n X) K n hX.cd
  have hac := hX.heat_probability_absolutelyContinuous K n hn p f hf0 hfs hfm C hfC (t+1)
    (by linarith)
  have hcc := (metricAC_uniformContinuousOn hac).continuousOn
  exact hcc.continuousAt (by
    rw [uIcc_of_le (show (0 : ℝ) ≤ t+1 by linarith)]
    exact Icc_mem_nhds ht (by linarith))

theorem NoncollapsedRCD.compact_heat_wassersteinSq_continuousAt
    (K : ℝ) (n : ℕ) [IsFiniteMeasure (hausdorff n X)]
    (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f)
    (hfm : ∫ x, f x ∂hausdorff n X = 1)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ hausdorff n X)
    {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s => (wassersteinSq
      (heatMeasure (hausdorff n X) hX.quadratic s f) ν).toReal) t := by
  let μ := hausdorff n X
  let := ACWassersteinProbability.metric μ K n hX.cd
  obtain ⟨R, hR, hRb⟩ := (isBounded_univ.mpr (inferInstance : BoundedSpace X)).subset_closedBall_lt (0 : ℝ) p
  have hfs : ∃ r : ℝ, ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r :=
    ⟨R, ae_of_all _ fun x _ => by simpa [dist_comm] using hRb (mem_univ x)⟩
  let v : ACWassersteinProbability μ := ⟨ν, inferInstance, hν,
    finiteSecondMoment_of_integrable_dist ν p (((continuous_const.dist continuous_id).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))⟩
  let ρ := hX.heatProbability K n hn p f hf0 hfs hfm
  have hc : ContinuousAt ρ t :=
    hX.compact_heat_probability_continuousAt K n hn p f hf0 hfs hfm C hfC ht
  have hd : ContinuousAt (fun s => dist (ρ s) v ^ 2) t :=
    (hc.dist continuousAt_const).pow 2
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  change (wassersteinSq (heatMeasure μ hX.quadratic s f) ν).toReal =
    ((wassersteinEDist (ρ s).val v.val).toReal)^2
  dsimp only [ρ, v, NoncollapsedRCD.heatProbability]
  rw [max_eq_left hs.le, wassersteinEDist, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt ENNReal.toReal_nonneg]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.heat_entropy_continuousAt
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f)
    (hfs : ∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s => boltzmannEntropy (hausdorff n X)
      (heatMeasure (hausdorff n X) hX.quadratic s f)) t := by
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hfi := lp_integrable_of_bounded_support μ f p hfr
  have hac := heatAt_entropy_absolutelyContinuous_nonneg μ hX.quadratic p hA hB hvol
    f hf0 hfi hfr (a := 0) (b := t+1) le_rfl (by linarith)
  have hc : ContinuousOn (fun s => boltzmannEntropy μ (heatMeasure μ hX.quadratic s f)) (Icc 0 (t+1)) := by
    simpa only [uIcc_of_le (show (0:ℝ) ≤ t+1 by linarith),
      boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0] using hac.continuousOn
  exact hc.continuousAt (Icc_mem_nhds ht (by linarith))

theorem NoncollapsedRCD.heat_probability_continuousAt
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f)
    (hfs : ∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C)
    {t : ℝ} (ht : 0 < t) :
    letI := ACWassersteinProbability.metric (hausdorff n X) K n hX.cd
    ContinuousAt (hX.heatProbability K n hn p f hf0 hfs hfm) t := by
  let : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let := ACWassersteinProbability.metric (hausdorff n X) K n hX.cd
  have hac := hX.heat_probability_absolutelyContinuous K n hn p f hf0 hfs hfm C hfC (t+1) (by linarith)
  have hcc := (metricAC_uniformContinuousOn hac).continuousOn
  exact hcc.continuousAt (by
    rw [uIcc_of_le (show (0:ℝ) ≤ t+1 by linarith)]
    exact Icc_mem_nhds ht (by linarith))

theorem NoncollapsedRCD.heat_wassersteinSq_continuousAt
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f)
    (hfs : ∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ hausdorff n X)
    (hν2 : FiniteSecondMoment ν) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s => (wassersteinSq
      (heatMeasure (hausdorff n X) hX.quadratic s f) ν).toReal) t := by
  let μ := hausdorff n X
  let := ACWassersteinProbability.metric μ K n hX.cd
  let v : ACWassersteinProbability μ := ⟨ν,inferInstance,hν,hν2⟩
  let ρ := hX.heatProbability K n hn p f hf0 hfs hfm
  have hc : ContinuousAt ρ t := hX.heat_probability_continuousAt K n hn p f hf0 hfs hfm C hfC ht
  have hd : ContinuousAt (fun s => dist (ρ s) v^2) t := (hc.dist continuousAt_const).pow 2
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  change (wassersteinSq (heatMeasure μ hX.quadratic s f) ν).toReal =
    ((wassersteinEDist (ρ s).val v.val).toReal)^2
  dsimp only [ρ,v,NoncollapsedRCD.heatProbability]
  rw [max_eq_left hs.le,wassersteinEDist,←ENNReal.toReal_rpow,←Real.sqrt_eq_rpow,
    Real.sq_sqrt ENNReal.toReal_nonneg]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology

theorem sq_dist_difference_le {Y : Type*} [PseudoMetricSpace Y] (x y z : Y) :
    |dist x z^2-dist y z^2| ≤ dist x y*(2*dist y z+dist x y) := by
  have ha := abs_dist_sub_le x y z
  have hb := dist_triangle x y z
  have he : dist x z^2-dist y z^2 = (dist x z-dist y z)*(dist x z+dist y z) := by ring
  rw [he,abs_mul,abs_of_nonneg (add_nonneg dist_nonneg dist_nonneg)]
  exact (mul_le_mul_of_nonneg_right ha (add_nonneg dist_nonneg dist_nonneg)).trans
    (mul_le_mul_of_nonneg_left (by linarith) dist_nonneg)

theorem sq_dist_difference_exponential {Y : Type*} [PseudoMetricSpace Y] (x y z : Y)
    {D L a R : ℝ} (hD : 0 ≤ D) (_ : 0 ≤ L) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hxy : dist x y^2 ≤ D*Real.exp (-(2*a)*R)) (hyz : dist y z ≤ L) :
    |dist x z^2-dist y z^2| ≤ Real.sqrt D*(2*L+Real.sqrt D)*Real.exp (-a*R) := by
  have he : Real.exp (-(2*a)*R) = (Real.exp (-a*R))^2 := by
    rw [←Real.exp_nat_mul]; congr 1; ring
  have hs : dist x y ≤ Real.sqrt D*Real.exp (-a*R) := by
    apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hD,←he]
    exact hxy
  have hex : Real.exp (-a*R) ≤ 1 := by
    rw [←Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hs' : dist x y ≤ Real.sqrt D := hs.trans (by nlinarith [Real.sqrt_nonneg D])
  calc
    _ ≤ dist x y*(2*dist y z+dist x y) := sq_dist_difference_le x y z
    _ ≤ (Real.sqrt D*Real.exp (-a*R))*(2*L+Real.sqrt D) :=
      mul_le_mul hs (by linarith) (by positivity) (by positivity)
    _ = _ := by ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem ACWassersteinProbability.dist_sq (μ : Measure X) {K : ℝ} {n : ℕ} (hcd : FullCD μ K n)
    (ν η : ACWassersteinProbability μ) :
    letI := ACWassersteinProbability.metric μ K n hcd
    dist ν η^2 = (wassersteinSq ν.val η.val).toReal := by
  change ((wassersteinEDist ν.val η.val).toReal)^2 = _
  rw [wassersteinEDist,←ENNReal.toReal_rpow,←Real.sqrt_eq_rpow,Real.sq_sqrt ENNReal.toReal_nonneg]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.radial_heat_cost_exponential
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → (hausdorff n X).real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfi : Integrable f (hausdorff n X)) (hfm : ∫x, f x ∂hausdorff n X = 1)
    {r : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ hausdorff n X)
    (hν2 : FiniteSecondMoment ν) {a t T : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s, t ≤ s → s ≤ T → ∀ R, 1 ≤ R →
      (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt (hausdorff n X) hX.quadratic s f x ∂hausdorff n X →
      |(wassersteinSq (radialHeatMeasure (hausdorff n X) hX.quadratic p R s f) ν).toReal-
        (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic s f) ν).toReal| ≤ D*Real.exp (-a*R) := by
  let μ := hausdorff n X
  let := ACWassersteinProbability.metric μ K n hX.cd
  let v : ACWassersteinProbability μ := ⟨ν,inferInstance,hν,hν2⟩
  let ρ := hX.heatProbability K n hn p f hf0 ⟨r,hfs⟩ hfm
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hc : ContinuousOn (fun s => dist (ρ s) v) (Icc t T) := by
    intro s hs
    have hh : ContinuousAt ρ s := hX.heat_probability_continuousAt K n hn p f hf0 ⟨r,hfs⟩ hfm C hfabs
      (ht.trans_le hs.1)
    have hd : ContinuousAt (fun q => dist (ρ q) v) s := hh.dist continuousAt_const
    exact hd.continuousWithinAt
  obtain ⟨L,hL⟩ := isCompact_Icc.bddAbove_image hc
  obtain ⟨D,hD,hcut⟩ := radialHeatMeasure_transport_exponential μ hX.quadratic p hA hB hvol
    f hf0 hfi hfm hfs (a := 2*a) (T := T) (by positivity)
  refine ⟨Real.sqrt D*(2*(max L 0)+Real.sqrt D),by positivity,?_⟩
  intro s hs hT R hR hm
  have hsp : 0 < s := ht.trans_le hs
  have hd := radialHeatMeasure_data μ hX.quadratic p hA hB hvol f C hf0 hfC hfi hfm
    (zero_lt_one.trans_le hR) hsp hm
  let : IsProbabilityMeasure (radialHeatMeasure μ hX.quadratic p R s f) := hd.1
  let η : ACWassersteinProbability μ := ⟨radialHeatMeasure μ hX.quadratic p R s f,hd.1,
    withDensity_absolutelyContinuous _ _,finiteSecondMoment_of_ae_dist_le _ p hd.2.2⟩
  have hρ : (ρ s).val = heatMeasure μ hX.quadratic s f := by
    dsimp only [ρ,NoncollapsedRCD.heatProbability]
    rw [max_eq_left hsp.le]
  have hxy : dist η (ρ s)^2 ≤ D*Real.exp (-(2*a)*R) := by
    rw [ACWassersteinProbability.dist_sq μ hX.cd,hρ]
    exact hcut s hsp.le hT R (zero_lt_one.trans_le hR) hm
  have hyz : dist (ρ s) v ≤ max L 0 :=
    (hL (mem_image_of_mem _ (show s ∈ Icc t T from ⟨hs,hT⟩))).trans (le_max_left _ _)
  have he := sq_dist_difference_exponential η (ρ s) v hD (le_max_right L 0) ha
    (zero_le_one.trans hR) hxy hyz
  rw [ACWassersteinProbability.dist_sq μ hX.cd,ACWassersteinProbability.dist_sq μ hX.cd,hρ] at he
  exact he


end

 
section

 
open Set Filter MeasureTheory
open scoped Topology

theorem integral_bound_of_right_secants {D G : ℝ → ℝ} {e : ℝ → ℝ → ℝ}
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hD : ContinuousOn D (Icc a b)) (hG : ContinuousOn G (Ioi 0))
    (he : ∀ t ∈ Ico a b, Tendsto (e t) (𝓝[>] 0) (𝓝 0))
    (hsec : ∀ t ∈ Ico a b, ∀ h, 0 < h →
      (D (t+h) - D t)/h ≤ G (t+h) + e t h) :
    D b - D a ≤ ∫ t in a..b, G t := by
  let B : ℝ → ℝ := fun t => D a + ∫ s in a..t, G s
  have hi {t : ℝ} (ht : a ≤ t) : IntervalIntegrable G volume a t :=
    ContinuousOn.intervalIntegrable_of_Icc ht (hG.mono fun x hx => lt_of_lt_of_le ha hx.1)
  have hd {t : ℝ} (ht : a ≤ t) : HasDerivAt B (G t) t := by
    have ht0 : t ∈ Ioi (0 : ℝ) := lt_of_lt_of_le ha ht
    exact (intervalIntegral.integral_hasDerivAt_right (hi ht)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hG t ht0)
      (hG.continuousAt (Ioi_mem_nhds ht0))).const_add (D a)
  have hb : ContinuousOn B (Icc a b) := fun t ht => (hd ht.1).continuousAt.continuousWithinAt
  have hba : D a ≤ B a := by simp [B]
  have hb' : ∀ t ∈ Ico a b, HasDerivWithinAt B (G t) (Ici t) t :=
    fun t ht => (hd ht.1).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico a b, ∀ r, G t < r → ∃ᶠ z in 𝓝[>] t, slope D t z < r := by
    intro t ht r hr
    have hsub : Tendsto (fun z : ℝ => z-t) (𝓝[>] t) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa using ((tendsto_id : Tendsto (fun z : ℝ => z) (𝓝 t) (𝓝 t)).mono_left nhdsWithin_le_nhds).sub_const t
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact sub_pos.mpr (show t < z from hz)
    have hc : Tendsto (fun z => G z + e t (z-t)) (𝓝[>] t) (𝓝 (G t)) := by
      simpa using ((hG.continuousAt (Ioi_mem_nhds (lt_of_lt_of_le ha ht.1))).tendsto.mono_left
        nhdsWithin_le_nhds).add ((he t ht).comp hsub)
    have hlt := hc.eventually (Iio_mem_nhds hr)
    apply Filter.Eventually.frequently
    filter_upwards [hlt, self_mem_nhdsWithin] with z hz hzt
    have hs := hsec t ht (z-t) (sub_pos.mpr hzt)
    rw [add_sub_cancel] at hs
    simpa only [slope_def_field] using hs.trans_lt hz
  have hf := image_le_of_liminf_slope_right_le_deriv_boundary hD hba hb hb' hbound
    (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
  change D b ≤ D a + ∫ s in a..b, G s at hf
  linarith only [hf]



 
theorem integral_bound_of_frequent_right_slopes {D G : ℝ → ℝ}
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hD : ContinuousOn D (Icc a b)) (hG : ContinuousOn G (Ioi 0))
    (hsec : ∀ t ∈ Ico a b, ∀ r, G t < r → ∃ᶠ z in 𝓝[>] t, slope D t z < r) :
    D b-D a ≤ ∫t in a..b, G t := by
  let B : ℝ → ℝ := fun t => D a+∫s in a..t, G s
  have hi {t : ℝ} (ht : a ≤ t) : IntervalIntegrable G volume a t :=
    ContinuousOn.intervalIntegrable_of_Icc ht (hG.mono fun x hx => lt_of_lt_of_le ha hx.1)
  have hd {t : ℝ} (ht : a ≤ t) : HasDerivAt B (G t) t := by
    have ht0 : t ∈ Ioi (0:ℝ) := lt_of_lt_of_le ha ht
    exact (intervalIntegral.integral_hasDerivAt_right (hi ht)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hG t ht0)
      (hG.continuousAt (Ioi_mem_nhds ht0))).const_add (D a)
  have hb : ContinuousOn B (Icc a b) := fun t ht => (hd ht.1).continuousAt.continuousWithinAt
  have hba : D a ≤ B a := by simp [B]
  have hb' : ∀ t ∈ Ico a b, HasDerivWithinAt B (G t) (Ici t) t :=
    fun t ht => (hd ht.1).hasDerivWithinAt
  have hf := image_le_of_liminf_slope_right_le_deriv_boundary hD hba hb hb' hsec
    (show b ∈ Icc a b from ⟨hab,le_rfl⟩)
  change D b ≤ D a+∫s in a..b, G s at hf
  linarith only [hf]

theorem exp_neg_mul_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => Real.exp (-c*R)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc))

theorem frequent_right_slope_of_exponential_secants {D G : ℝ → ℝ} {e : ℝ → ℝ}
    {t c : ℝ} (hc : 0 < c) (hG : ContinuousAt G t)
    (he : Tendsto e atTop (𝓝 0))
    (hsec : ∀ᶠ R : ℝ in atTop,
      (D (t+Real.exp (-c*R))-D t)/Real.exp (-c*R) ≤ G (t+Real.exp (-c*R))+e R) :
    ∀ r, G t < r → ∃ᶠ z in 𝓝[>] t, slope D t z < r := by
  intro r hr
  have hh := exp_neg_mul_tendsto_zero hc
  have ht : Tendsto (fun R : ℝ => t+Real.exp (-c*R)) atTop (𝓝 t) := by simpa using hh.const_add t
  have ht' : Tendsto (fun R : ℝ => t+Real.exp (-c*R)) atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall fun R => by exact lt_add_of_pos_right t (Real.exp_pos _)⟩
  have hlim : Tendsto (fun R : ℝ => G (t+Real.exp (-c*R))+e R) atTop (𝓝 (G t)) := by
    simpa using (hG.tendsto.comp ht).add he
  apply ht'.frequently
  apply Filter.Eventually.frequently
  filter_upwards [hsec,hlim.eventually (Iio_mem_nhds hr)] with R hs hl
  simpa only [slope_def_field,add_sub_cancel_left] using hs.trans_lt hl



 
theorem cutoff_secant_transfer {x y z ec et ev K h J L E : ℝ} (hh : 0 < h)
    (hx : |x-y| ≤ L) (he : |ec-et| ≤ J)
    (hs : (x-z)/(2*h) ≤ ev-ec-(K/2)*x+E) :
    (y-z)/(2*h) ≤ ev-et-(K/2)*y+J+(|K|/2)*L+L/(2*h)+E := by
  have hxl : y-x ≤ L := by linarith [(abs_le.mp hx).1]
  have hel : et-ec ≤ J := by linarith [(abs_le.mp he).1]
  have hk : (K/2)*(y-x) ≤ (|K|/2)*L := by
    calc
      _ ≤ |(K/2)*(y-x)| := le_abs_self _
      _ = (|K|/2)*|x-y| := by rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2),abs_sub_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
  have hd := div_le_div_of_nonneg_right hxl (by positivity : 0 ≤ 2*h)
  have hid : (y-z)/(2*h) = (x-z)/(2*h)+(y-x)/(2*h) := by ring
  rw [hid]
  linarith only [hs,hel,hk,hd]

theorem diagonal_polynomial_exponential_error {b : ℝ} (hb : 0 ≤ b)
    (J L K N A H : ℝ) :
    Tendsto (fun R : ℝ =>
      J*Real.exp (-(2*b+4)*R)+(|K|/2)*L*Real.exp (-(2*b+4)*R)+
      L*Real.exp (-(2*b+4)*R)/(2*Real.exp (-(b+1)*R))+
      (N*Real.exp (b*R))*(A*Real.exp (-(b+1)*R)+
        ((Real.exp (-(b+1)*R))⁻¹+2)*(H*Real.exp (-(2*b+4)*R)))) atTop (𝓝 0) := by
  have he (R : ℝ) :
      J*Real.exp (-(2*b+4)*R)+(|K|/2)*L*Real.exp (-(2*b+4)*R)+
      L*Real.exp (-(2*b+4)*R)/(2*Real.exp (-(b+1)*R))+
      (N*Real.exp (b*R))*(A*Real.exp (-(b+1)*R)+
        ((Real.exp (-(b+1)*R))⁻¹+2)*(H*Real.exp (-(2*b+4)*R))) =
      (J+(|K|/2)*L)*Real.exp (-(2*b+4)*R)+(L/2)*Real.exp (-(b+3)*R)+
      N*A*Real.exp (-1*R)+N*H*Real.exp (-3*R)+2*N*H*Real.exp (-(b+4)*R) := by
    have h1 : Real.exp (-(2*b+4)*R)/Real.exp (-(b+1)*R) = Real.exp (-(b+3)*R) := by
      rw [←Real.exp_sub]; congr 1; ring
    have h2 : Real.exp (b*R)*Real.exp (-(b+1)*R) = Real.exp (-1*R) := by
      rw [←Real.exp_add]; congr 1; ring
    have h3 : Real.exp (b*R)*Real.exp (-(2*b+4)*R)/Real.exp (-(b+1)*R) = Real.exp (-3*R) := by
      rw [←Real.exp_add,←Real.exp_sub]; congr 1; ring
    have h4 : Real.exp (b*R)*Real.exp (-(2*b+4)*R) = Real.exp (-(b+4)*R) := by
      rw [←Real.exp_add]; congr 1; ring
    calc
      _ = (J+(|K|/2)*L)*Real.exp (-(2*b+4)*R)+
          (L/2)*(Real.exp (-(2*b+4)*R)/Real.exp (-(b+1)*R))+
          N*A*(Real.exp (b*R)*Real.exp (-(b+1)*R))+
          N*H*(Real.exp (b*R)*Real.exp (-(2*b+4)*R)/Real.exp (-(b+1)*R))+
          2*N*H*(Real.exp (b*R)*Real.exp (-(2*b+4)*R)) := by ring
      _ = _ := by rw [h1,h2,h3,h4]
  simp_rw [he]
  simpa using ((((exp_neg_mul_tendsto_zero (by linarith : 0 < 2*b+4)).const_mul (J+(|K|/2)*L)).add
    ((exp_neg_mul_tendsto_zero (by linarith : 0 < b+3)).const_mul (L/2))).add
    ((exp_neg_mul_tendsto_zero (by norm_num : (0:ℝ) < 1)).const_mul (N*A))).add
    ((exp_neg_mul_tendsto_zero (by norm_num : (0:ℝ) < 3)).const_mul (N*H)) |>.add
    ((exp_neg_mul_tendsto_zero (by linarith : 0 < b+4)).const_mul (2*N*H))

theorem frequent_slope_of_expanding_cutoffs {D E : ℝ → ℝ} {Q F : ℝ → ℝ}
    {t b ev K J L N A H : ℝ} (hb : 0 ≤ b)
    (hc : ContinuousAt (fun s => ev-E s-(K/2)*D s) t)
    (herr : ∀ᶠ R : ℝ in atTop,
      |Q R-D (t+Real.exp (-(b+1)*R))| ≤ L*Real.exp (-(2*b+4)*R) ∧
      |F R-E (t+Real.exp (-(b+1)*R))| ≤ J*Real.exp (-(2*b+4)*R) ∧
      (Q R-D t)/(2*Real.exp (-(b+1)*R)) ≤
        ev-F R-(K/2)*Q R+(N*Real.exp (b*R))*(A*Real.exp (-(b+1)*R)+
        ((Real.exp (-(b+1)*R))⁻¹+2)*(H*Real.exp (-(2*b+4)*R)))) :
    ∀ r, ev-E t-(K/2)*D t < r →
      ∃ᶠ z in 𝓝[>] t, slope (fun s => D s/2) t z < r := by
  apply frequent_right_slope_of_exponential_secants (c := b+1) (by linarith) hc
    (diagonal_polynomial_exponential_error hb J L K N A H)
  filter_upwards [herr] with R hR
  have hs := cutoff_secant_transfer (Real.exp_pos (-(b+1)*R)) hR.1 hR.2.1 hR.2.2
  convert hs using 1 <;> ring


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.bounded_heat_frequent_EVI_slope
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {r : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≤ ENNReal.ofReal C • hausdorff n X)
    {rν : ℝ} (hνS : ∀ᵐ x ∂ν, dist x p ≤ rν) {t : ℝ} (ht : 0 < t) :
    ∀ z, boltzmannEntropy (hausdorff n X) ν-
      boltzmannEntropy (hausdorff n X) (heatMeasure (hausdorff n X) hX.quadratic t f)-
      (K/2)*(wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic t f) ν).toReal < z →
      ∃ᶠ s in 𝓝[>] t, slope (fun q =>
        (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic q f) ν).toReal/2) t s < z := by
  let μ := hausdorff n X
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hfi := lp_integrable_of_bounded_support μ f p hfs
  have hνac : ν ≪ μ := (Measure.absolutelyContinuous_of_le hν).trans Measure.smul_absolutelyContinuous
  have hν2 := finiteSecondMoment_of_ae_dist_le ν p hνS
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  let b := 12*B+4
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let a := 2*b+4
  have ha : 0 ≤ a := by dsimp [a]; positivity
  obtain ⟨H,R₀,hH,hR₀,hNorm⟩ := heat_normalized_cutoff_exponential μ hX.quadratic p hA hB hvol
    f C hf0 hfC hfi hfm hfs (a := a) (T := t+1) ha ht
  obtain ⟨J,hJ,hEnt⟩ := radialHeatMeasure_entropy_exponential μ hX.quadratic p hA hB hvol
    f hf0 hfi hfm hfs (a := a) (T := t+1) ha
  obtain ⟨L,hL,hCost⟩ := hX.radial_heat_cost_exponential K n hn p hA hB hvol f C hf0 hfC hfi hfm hfs
    ν hνac hν2 (a := a) (T := t+1) ha ht
  let D : ℝ → ℝ := fun s => (wassersteinSq (heatMeasure μ hX.quadratic s f) ν).toReal
  let E : ℝ → ℝ := fun s => boltzmannEntropy μ (heatMeasure μ hX.quadratic s f)
  let Q : ℝ → ℝ := fun R => (wassersteinSq (radialHeatMeasure μ hX.quadratic p R
    (t+Real.exp (-(b+1)*R)) f) ν).toReal
  let F : ℝ → ℝ := fun R => boltzmannEntropy μ (radialHeatMeasure μ hX.quadratic p R
    (t+Real.exp (-(b+1)*R)) f)
  have hc : ContinuousAt (fun s => boltzmannEntropy μ ν-E s-(K/2)*D s) t :=
    (continuousAt_const.sub (hX.heat_entropy_continuousAt K n hn p f hf0 ⟨r,hfs⟩ ht)).sub
      ((hX.heat_wassersteinSq_continuousAt K n hn p f hf0 ⟨r,hfs⟩ hfm C hfabs ν hνac hν2 ht).const_mul (K/2))
  apply frequent_slope_of_expanding_cutoffs (D := D) (E := E) (Q := Q) (F := F)
    (J := J) (L := L) (N := 1000*(A+1)) (A := (2*(1+1/(t/2)))^2*‖f‖) (H := H) hb hc
  have htime : ∀ᶠ R : ℝ in atTop, Real.exp (-(b+1)*R) ≤ 1 :=
    (exp_neg_mul_tendsto_zero (by linarith : 0 < b+1)).eventually_le_const (by norm_num)
  filter_upwards [eventually_ge_atTop (max R₀ (max 1 rν)),htime] with R hR htime
  have hRR : R₀ ≤ R := (le_max_left _ _).trans hR
  have hR1 : 1 ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRν : rν ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hRp : 0 < R := zero_lt_one.trans_le hR1
  let h := Real.exp (-(b+1)*R)
  have hh : 0 < h := Real.exp_pos _
  have hs : t ≤ t+h := le_add_of_nonneg_right hh.le
  have hst : t+h ≤ t+1 := by dsimp only [h]; linarith only [htime]
  have hn := hNorm (t+h) hs hst R hRp hRR
  refine ⟨hCost (t+h) hs hst R hR1 hn.1,hEnt (t+h) (add_pos ht hh).le hst R hRp hn.1,?_⟩
  have hv : ∀ᵐ x ∂ν, dist x p ≤ 2*R := hνS.mono fun x hx => hx.trans (by linarith)
  have hsec := hX.cutoff_heat_secant K n ‹2 ≤ n› p hA hB hvol f C hf0 hfC hfi hfm hfs ν hν
    hR1 ht hh hv hn.1
  have hnorm : ‖radialHeatSobolev μ hX.quadratic p hRp (add_pos ht hh) f C-
      heatSobolev μ hX.quadratic (t+h) (add_pos ht hh) f‖ ≤ H*Real.exp (-(2*b+4)*R) := by
    simpa only [radialHeatSobolev,norm_sub_rev,a] using hn.2
  apply hsec.trans
  apply add_le_add le_rfl
  change (1000*(A+1)*Real.exp (b*R))*_ ≤ (1000*(A+1)*Real.exp (b*R))*_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left hnorm (by positivity)


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.bounded_heat_EVI
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {r : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≤ ENNReal.ofReal C • hausdorff n X)
    {rν : ℝ} (hνS : ∀ᵐ x ∂ν, dist x p ≤ rν) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    letI : SeparableSpace X := hX.separable
    letI : ProperSpace X := hX.proper K n hn
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ((wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic b f) ν).toReal-
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic a f) ν).toReal)/2 ≤
      ∫t in a..b, (boltzmannEntropy (hausdorff n X) ν-
        boltzmannEntropy (hausdorff n X) (heatMeasure (hausdorff n X) hX.quadratic t f)-
        (K/2)*(wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic t f) ν).toReal) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let D : ℝ → ℝ := fun s => (wassersteinSq (heatMeasure μ hX.quadratic s f) ν).toReal/2
  let G : ℝ → ℝ := fun s => boltzmannEntropy μ ν-boltzmannEntropy μ (heatMeasure μ hX.quadratic s f)-K*D s
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hνac : ν ≪ μ := (Measure.absolutelyContinuous_of_le hν).trans Measure.smul_absolutelyContinuous
  have hν2 := finiteSecondMoment_of_ae_dist_le ν p hνS
  have hDc {t : ℝ} (ht : 0 < t) : ContinuousAt D t :=
    (hX.heat_wassersteinSq_continuousAt K n hn p f hf0 ⟨r,hfs⟩ hfm C hfabs ν hνac hν2 ht).div_const 2
  have hGc : ContinuousOn G (Ioi 0) := by
    intro t ht
    have hc : ContinuousAt G t :=
      (continuousAt_const.sub (hX.heat_entropy_continuousAt K n hn p f hf0 ⟨r,hfs⟩ ht)).sub ((hDc ht).const_mul K)
    exact hc.continuousWithinAt
  have hs := integral_bound_of_frequent_right_slopes (D := D) (G := G) ha hab
    (fun t ht => (hDc (ha.trans_le ht.1)).continuousWithinAt) hGc (by
      intro t ht z hz
      apply hX.bounded_heat_frequent_EVI_slope K n hn p f C hf0 hfC hfm hfs ν hν hνS (ha.trans_le ht.1) z
      convert hz using 1
      dsimp only [G,D]
      ring)
  dsimp only [D,G] at hs
  convert hs using 1
  · ring
  · congr 1
    funext t
    ring


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology

theorem integrated_evi_error_transfer {D Q P : ℝ → ℝ} {E F K a b J L : ℝ}
    (hab : a ≤ b)
    (hi : IntervalIntegrable (fun t => E-P t-(K/2)*D t) volume a b)
    (hi' : IntervalIntegrable (fun t => F-P t-(K/2)*Q t) volume a b)
    (hD : ∀ t ∈ Icc a b, |Q t-D t| ≤ L) (hE : |F-E| ≤ J)
    (hvi : (Q b-Q a)/2 ≤ ∫t in a..b, F-P t-(K/2)*Q t) :
    (D b-D a)/2 ≤ (∫t in a..b, E-P t-(K/2)*D t)+
      L+(b-a)*(J+(|K|/2)*L) := by
  have hp (t : ℝ) (ht : t ∈ Icc a b) :
      F-P t-(K/2)*Q t ≤ E-P t-(K/2)*D t+(J+(|K|/2)*L) := by
    have hx : (K/2)*(D t-Q t) ≤ (|K|/2)*L := by
      calc
        _ ≤ |(K/2)*(D t-Q t)| := le_abs_self _
        _ = (|K|/2)*|Q t-D t| := by
          rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2),abs_sub_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hD t ht) (by positivity)
    linarith only [hx,(abs_le.mp hE).2]
  have hint := intervalIntegral.integral_mono_on hab hi' (hi.add intervalIntegrable_const) hp
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,intervalIntegral.integral_const,smul_eq_mul] at hint
  have hd1 := (abs_le.mp (hD a ⟨le_rfl,hab⟩)).2
  have hd2 := (abs_le.mp (hD b ⟨hab,le_rfl⟩)).1
  linarith only [hvi,hint,hd1,hd2]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.heat_competitor_cutoff_cost
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → (hausdorff n X).real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {rf : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ rf)
    (hg0 : 0 ≤ g) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hgi : Integrable g (hausdorff n X)) (hgm : ∫x, g x ∂hausdorff n X = 1)
    {rg : ℝ} (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ rg)
    {s a b : ℝ} (hs : 0 < s) (ha : 0 < a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R, 1 ≤ R →
      (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt (hausdorff n X) hX.quadratic s g x ∂hausdorff n X →
      ∀ t ∈ Icc a b,
      |(wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic t f)
          (radialHeatMeasure (hausdorff n X) hX.quadratic p R s g)).toReal-
        (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic t f)
          (heatMeasure (hausdorff n X) hX.quadratic s g)).toReal| ≤ D*Real.exp (-R) := by
  let μ := hausdorff n X
  let := ACWassersteinProbability.metric μ K n hX.cd
  let ρ := hX.heatProbability K n hn p f hf0 ⟨rf,hfs⟩ hfm
  let v := hX.heatProbability K n hn p g hg0 ⟨rg,hgs⟩ hgm s
  have hv : v.val = heatMeasure μ hX.quadratic s g := by
    dsimp only [v,NoncollapsedRCD.heatProbability]
    rw [max_eq_left hs.le]
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hc : ContinuousOn (fun t => dist v (ρ t)) (Icc a b) := by
    intro t ht
    have hh : ContinuousAt ρ t := hX.heat_probability_continuousAt K n hn p f hf0 ⟨rf,hfs⟩ hfm C hfabs
      (ha.trans_le ht.1)
    have hd : ContinuousAt (fun q => dist v (ρ q)) t := continuousAt_const.dist hh
    exact hd.continuousWithinAt
  obtain ⟨L,hL⟩ := isCompact_Icc.bddAbove_image hc
  obtain ⟨D,hD,hcut⟩ := radialHeatMeasure_transport_exponential μ hX.quadratic p hA hB hvol
    g hg0 hgi hgm hgs (a := 2) (T := s) (by norm_num)
  refine ⟨Real.sqrt D*(2*(max L 0)+Real.sqrt D),by positivity,?_⟩
  intro R hR hm t ht
  have hd := radialHeatMeasure_data μ hX.quadratic p hA hB hvol g C hg0 hgC hgi hgm
    (zero_lt_one.trans_le hR) hs hm
  let : IsProbabilityMeasure (radialHeatMeasure μ hX.quadratic p R s g) := hd.1
  let η : ACWassersteinProbability μ := ⟨radialHeatMeasure μ hX.quadratic p R s g,hd.1,
    withDensity_absolutelyContinuous _ _,finiteSecondMoment_of_ae_dist_le _ p hd.2.2⟩
  have hρ : (ρ t).val = heatMeasure μ hX.quadratic t f := by
    dsimp only [ρ,NoncollapsedRCD.heatProbability]
    rw [max_eq_left (ha.trans_le ht.1).le]
  have hxy : dist η v^2 ≤ D*Real.exp (-(2*(1:ℝ))*R) := by
    rw [ACWassersteinProbability.dist_sq μ hX.cd,hv]
    simpa only [mul_one] using hcut s hs.le le_rfl R (zero_lt_one.trans_le hR) hm
  have hyz : dist v (ρ t) ≤ max L 0 :=
    (hL (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have he := sq_dist_difference_exponential η v (ρ t) hD (le_max_right L 0)
    (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hR) hxy hyz
  rw [dist_comm η (ρ t),dist_comm v (ρ t),ACWassersteinProbability.dist_sq μ hX.cd,
    ACWassersteinProbability.dist_sq μ hX.cd,hρ,hv] at he
  simpa only [neg_mul,one_mul] using he


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.heat_competitor_EVI
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {rf : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ rf)
    (hg0 : 0 ≤ g) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hgm : ∫x, g x ∂hausdorff n X = 1)
    {rg : ℝ} (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ rg)
    {s a b : ℝ} (hs : 0 < s) (ha : 0 < a) (hab : a ≤ b) :
    letI : SeparableSpace X := hX.separable
    letI : ProperSpace X := hX.proper K n hn
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ((wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic b f)
        (heatMeasure (hausdorff n X) hX.quadratic s g)).toReal-
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic a f)
        (heatMeasure (hausdorff n X) hX.quadratic s g)).toReal)/2 ≤
      ∫t in a..b, (boltzmannEntropy (hausdorff n X) (heatMeasure (hausdorff n X) hX.quadratic s g)-
        boltzmannEntropy (hausdorff n X) (heatMeasure (hausdorff n X) hX.quadratic t f)-
        (K/2)*(wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic t f)
          (heatMeasure (hausdorff n X) hX.quadratic s g)).toReal) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hgi := lp_integrable_of_bounded_support μ g p hgs
  have hdg := hX.heat_law K n hn p g hg0 ⟨rg,hgs⟩ hgm s hs.le
  let ν := heatMeasure μ hX.quadratic s g
  let : IsProbabilityMeasure ν := hdg.1
  let D : ℝ → ℝ := fun t => (wassersteinSq (heatMeasure μ hX.quadratic t f) ν).toReal
  let P : ℝ → ℝ := fun t => boltzmannEntropy μ (heatMeasure μ hX.quadratic t f)
  let E := boltzmannEntropy μ ν
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hcD {t : ℝ} (ht : 0 < t) : ContinuousAt D t :=
    hX.heat_wassersteinSq_continuousAt K n hn p f hf0 ⟨rf,hfs⟩ hfm C hfabs ν hdg.2.1 hdg.2.2.1 ht
  have hcP {t : ℝ} (ht : 0 < t) : ContinuousAt P t :=
    hX.heat_entropy_continuousAt K n hn p f hf0 ⟨rf,hfs⟩ ht
  have hi : IntervalIntegrable (fun t => E-P t-(K/2)*D t) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (fun t ht =>
      ((continuousAt_const.sub (hcP (ha.trans_le ht.1))).sub
        ((hcD (ha.trans_le ht.1)).const_mul (K/2))).continuousWithinAt)
  obtain ⟨H,R₀,hH,hR₀,hNorm⟩ := heat_normalized_cutoff_exponential μ hX.quadratic p hA hB hvol
    g C hg0 hgC hgi hgm hgs (a := 1) (T := s) (by norm_num) hs
  obtain ⟨J,hJ,hEnt⟩ := radialHeatMeasure_entropy_exponential μ hX.quadratic p hA hB hvol
    g hg0 hgi hgm hgs (a := 1) (T := s) (by norm_num)
  obtain ⟨L,hL,hCost⟩ := hX.heat_competitor_cutoff_cost K n hn p hA hB hvol
    f g C hf0 hfC hfm hfs hg0 hgC hgi hgm hgs (b := b) hs ha
  have he : ∀ᶠ R : ℝ in atTop,
      (D b-D a)/2 ≤ (∫t in a..b, E-P t-(K/2)*D t)+
        (L+(b-a)*(J+(|K|/2)*L))*Real.exp (-R) := by
    filter_upwards [eventually_ge_atTop R₀] with R hR
    have hR1 := hR₀.trans hR
    have hRp := zero_lt_one.trans_le hR1
    have hm := (hNorm s le_rfl le_rfl R hRp hR).1
    let η := radialHeatMeasure μ hX.quadratic p R s g
    have hd := radialHeatMeasure_data μ hX.quadratic p hA hB hvol g C hg0 hgC hgi hgm hRp hs hm
    let : IsProbabilityMeasure η := hd.1
    have hηac : η ≪ μ := withDensity_absolutelyContinuous _ _
    have hη2 := finiteSecondMoment_of_ae_dist_le η p hd.2.2
    let Q : ℝ → ℝ := fun t => (wassersteinSq (heatMeasure μ hX.quadratic t f) η).toReal
    have hi' : IntervalIntegrable (fun t => boltzmannEntropy μ η-P t-(K/2)*Q t) volume a b :=
      ContinuousOn.intervalIntegrable_of_Icc hab (fun t ht =>
        ((continuousAt_const.sub (hcP (ha.trans_le ht.1))).sub
          ((hX.heat_wassersteinSq_continuousAt K n hn p f hf0 ⟨rf,hfs⟩ hfm C hfabs η hηac hη2
            (ha.trans_le ht.1)).const_mul (K/2))).continuousWithinAt)
    have hf2C : ∀ᵐ x ∂μ, f x ≤ (2*C:ℝ≥0) := hfC.mono fun x hx => by
      exact hx.trans (by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; nlinarith [C.property])
    have hvi := hX.bounded_heat_EVI K n hn p f (2*C) hf0 hf2C hfm hfs η
      (by simpa only [NNReal.coe_mul,NNReal.coe_ofNat] using hd.2.1) hd.2.2 ha hab
    have herr := integrated_evi_error_transfer (D := D) (Q := Q) (P := P) (E := E)
      (F := boltzmannEntropy μ η) (K := K) hab hi hi'
      (hCost R hR1 hm) (by simpa only [neg_mul,one_mul] using hEnt s hs.le le_rfl R hRp hm) hvi
    convert herr using 1 ; ring
  have hlim : Tendsto (fun R : ℝ => (∫t in a..b, E-P t-(K/2)*D t)+
      (L+(b-a)*(J+(|K|/2)*L))*Real.exp (-R)) atTop
      (𝓝 (∫t in a..b, E-P t-(K/2)*D t)) := by
    have hh := (exp_neg_mul_tendsto_zero (by norm_num : (0:ℝ) < 1)).const_mul
      (L+(b-a)*(J+(|K|/2)*L))
    simpa only [neg_mul,one_mul,mul_zero,add_zero] using hh.const_add (∫t in a..b, E-P t-(K/2)*D t)
  exact ge_of_tendsto hlim he


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology

theorem two_flow_evi_frequent_slope {D : ℝ → ℝ → ℝ} {P Q : ℝ → ℝ} {K t : ℝ}
    (ht : 0 < t)
    (hD : ∀ a b : ℝ, 0 < a → 0 < b → ContinuousAt (Function.uncurry D) (a,b))
    (hP : ∀ a : ℝ, 0 < a → ContinuousAt P a)
    (hQ : ∀ a : ℝ, 0 < a → ContinuousAt Q a)
    (hI : ∀ a b s : ℝ, 0 < a → a ≤ b → 0 < s →
      (D b s-D a s)/2 ≤ ∫q in a..b, Q s-P q-(K/2)*D q s)
    (hJ : ∀ a b s : ℝ, 0 < a → a ≤ b → 0 < s →
      (D s b-D s a)/2 ≤ ∫q in a..b, P s-Q q-(K/2)*D s q) :
    ∀ r, -2*K*D t t < r → ∃ᶠ z in 𝓝[>] t,
      slope (fun q => D q q) t z < r := by
  intro r hr
  let ε := (r+2*K*D t t)/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  let H : ℝ × ℝ → ℝ := fun z => Q z.2-P z.1-(K/2)*D z.1 z.2+
    (P t-Q z.1-(K/2)*D t z.1)
  have hDc : ContinuousAt (fun z : ℝ × ℝ => D t z.1) (t,t) :=
    (hD t t ht ht).comp (x := (t,t)) (f := fun z : ℝ × ℝ => (t,z.1)) (continuousAt_const.prodMk continuousAt_fst)
  have hH : ContinuousAt H (t,t) :=
    (((hQ t ht).comp continuousAt_snd).sub ((hP t ht).comp continuousAt_fst)).sub
      ((hD t t ht ht).const_mul (K/2)) |>.add
        ((continuousAt_const.sub ((hQ t ht).comp continuousAt_fst)).sub (hDc.const_mul (K/2)))
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousAt_iff.mp hH ε hε
  have he : ∀ᶠ z in 𝓝[>] t, slope (fun q => D q q) t z < r := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show t < t+δ by linarith)),
      self_mem_nhdsWithin] with z hz hz'
    change z < t+δ at hz
    have htz : t < z := hz'
    have hz0 : 0 < z := ht.trans htz
    have hbound : ∀ q ∈ Icc t z, H (q,z) ≤ -K*D t t+ε := by
      intro q hq
      have hd : dist (q,z) (t,t) < δ := by
        rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hq.1),
          abs_of_pos (sub_pos.mpr htz)]
        exact max_lt_iff.mpr ⟨by linarith [hq.2],by linarith⟩
      have hh := hnear hd
      rw [Real.dist_eq] at hh
      have htt : H (t,t) = -K*D t t := by dsimp [H]; ring
      rw [htt] at hh
      linarith [(abs_lt.mp hh).2]
    have hi : IntervalIntegrable (fun q => Q z-P q-(K/2)*D q z) volume t z :=
      ContinuousOn.intervalIntegrable_of_Icc htz.le (fun q hq =>
        ((continuousAt_const.sub (hP q (ht.trans_le hq.1))).sub
          (((hD q z (ht.trans_le hq.1) hz0).comp (f := fun w : ℝ => (w,z))
            (continuousAt_id.prodMk continuousAt_const)).const_mul (K/2))).continuousWithinAt)
    have hj : IntervalIntegrable (fun q => P t-Q q-(K/2)*D t q) volume t z :=
      ContinuousOn.intervalIntegrable_of_Icc htz.le (fun q hq =>
        ((continuousAt_const.sub (hQ q (ht.trans_le hq.1))).sub
          (((hD t q ht (ht.trans_le hq.1)).comp (f := fun w : ℝ => (t,w))
            (continuousAt_const.prodMk continuousAt_id)).const_mul (K/2))).continuousWithinAt)
    have hB := intervalIntegral.integral_mono_on htz.le (hi.add hj) intervalIntegrable_const hbound
    rw [intervalIntegral.integral_const,smul_eq_mul] at hB
    rw [intervalIntegral.integral_add hi hj] at hB
    have hi' := hI t z z ht htz.le hz0
    have hj' := hJ t z t ht htz.le ht
    have hsec : (D z z-D t t)/(z-t) ≤ 2*(-K*D t t+ε) := by
      apply (div_le_iff₀ (sub_pos.mpr htz)).mpr
      nlinarith only [hi',hj',hB]
    rw [slope_def_field]
    exact hsec.trans_lt (by dsimp [ε]; linarith)
  exact he.frequently

theorem two_flow_evi_contraction {D : ℝ → ℝ → ℝ} {P Q : ℝ → ℝ} {K a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hD : ∀ a b : ℝ, 0 < a → 0 < b → ContinuousAt (Function.uncurry D) (a,b))
    (hP : ∀ a : ℝ, 0 < a → ContinuousAt P a)
    (hQ : ∀ a : ℝ, 0 < a → ContinuousAt Q a)
    (hI : ∀ a b s : ℝ, 0 < a → a ≤ b → 0 < s →
      (D b s-D a s)/2 ≤ ∫q in a..b, Q s-P q-(K/2)*D q s)
    (hJ : ∀ a b s : ℝ, 0 < a → a ≤ b → 0 < s →
      (D s b-D s a)/2 ≤ ∫q in a..b, P s-Q q-(K/2)*D s q) :
    D b b ≤ D a a*Real.exp (-2*K*(b-a)) := by
  have hc : ContinuousOn (fun t => D t t) (Icc a b) := fun t ht =>
    ((hD t t (ha.trans_le ht.1) (ha.trans_le ht.1)).comp (f := fun w : ℝ => (w,w))
      (continuousAt_id.prodMk continuousAt_id)).continuousWithinAt
  have hgr := le_gronwallBound_of_liminf_deriv_right_le (f' := fun t => -2*K*D t t)
    (K := -2*K) (ε := 0) hc (by
      intro t ht r hr
      have hh := two_flow_evi_frequent_slope (ha.trans_le ht.1) hD hP hQ hI hJ r hr
      simpa only [slope_def_field,div_eq_mul_inv,mul_comm] using hh)
    le_rfl (by intro t ht; simp only [add_zero]; exact le_rfl) b ⟨hab,le_rfl⟩
  simpa only [gronwallBound_ε0] using hgr


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem wassersteinSq_symm [SeparableSpace X] (ν η : Measure X) :
    wassersteinSq ν η = wassersteinSq η ν := by
  apply ENNReal.rpow_left_injective (by norm_num : (1/(2:ℝ)) ≠ 0)
  exact wassersteinEDist_symm ν η

theorem NoncollapsedRCD.heat_two_cost_continuousAt
    (K : ℝ) (n : ℕ) [ProperSpace X] [SeparableSpace X]
    [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {rf : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ rf)
    (hg0 : 0 ≤ g) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hgm : ∫x, g x ∂hausdorff n X = 1)
    {rg : ℝ} (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ rg)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousAt (fun z : ℝ × ℝ => (wassersteinSq
      (heatMeasure (hausdorff n X) hX.quadratic z.1 f)
      (heatMeasure (hausdorff n X) hX.quadratic z.2 g)).toReal) (a,b) := by
  let μ := hausdorff n X
  let := ACWassersteinProbability.metric μ K n hX.cd
  let ρ := hX.heatProbability K n hn p f hf0 ⟨rf,hfs⟩ hfm
  let σ := hX.heatProbability K n hn p g hg0 ⟨rg,hgs⟩ hgm
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hgabs : ∀ᵐ x ∂μ, |g x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hg0,hgC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hρ : ContinuousAt ρ a := hX.heat_probability_continuousAt K n hn p f hf0 ⟨rf,hfs⟩ hfm C hfabs ha
  have hσ : ContinuousAt σ b := hX.heat_probability_continuousAt K n hn p g hg0 ⟨rg,hgs⟩ hgm C hgabs hb
  have hc : ContinuousAt (fun z : ℝ × ℝ => dist (ρ z.1) (σ z.2)^2) (a,b) :=
    ((hρ.comp (x := (a,b)) (f := Prod.fst) continuousAt_fst).dist
      (hσ.comp (x := (a,b)) (f := Prod.snd) continuousAt_snd)).pow 2
  apply hc.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioi.prod isOpen_Ioi).mem_nhds (show (a,b) ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) from ⟨ha,hb⟩)] with z hz
  rw [ACWassersteinProbability.dist_sq μ hX.cd]
  dsimp only [ρ,σ,NoncollapsedRCD.heatProbability]
  rw [max_eq_left hz.1.le,max_eq_left hz.2.le]

theorem NoncollapsedRCD.heat_wasserstein_contraction_positive
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {rf : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ rf)
    (hg0 : 0 ≤ g) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hgm : ∫x, g x ∂hausdorff n X = 1)
    {rg : ℝ} (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ rg)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    letI : SeparableSpace X := hX.separable
    letI : ProperSpace X := hX.proper K n hn
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic b f)
        (heatMeasure (hausdorff n X) hX.quadratic b g)).toReal ≤
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic a f)
        (heatMeasure (hausdorff n X) hX.quadratic a g)).toReal*Real.exp (-2*K*(b-a)) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let D : ℝ → ℝ → ℝ := fun a b => (wassersteinSq (heatMeasure μ hX.quadratic a f)
    (heatMeasure μ hX.quadratic b g)).toReal
  let P : ℝ → ℝ := fun t => boltzmannEntropy μ (heatMeasure μ hX.quadratic t f)
  let Q : ℝ → ℝ := fun t => boltzmannEntropy μ (heatMeasure μ hX.quadratic t g)
  apply two_flow_evi_contraction (D := D) (P := P) (Q := Q) ha hab
  · intro u v hu hv
    exact hX.heat_two_cost_continuousAt K n hn p f g C hf0 hfC hfm hfs hg0 hgC hgm hgs hu hv
  · intro t ht
    exact hX.heat_entropy_continuousAt K n hn p f hf0 ⟨rf,hfs⟩ ht
  · intro t ht
    exact hX.heat_entropy_continuousAt K n hn p g hg0 ⟨rg,hgs⟩ ht
  · intro u v s hu huv hs
    exact hX.heat_competitor_EVI K n hn p f g C hf0 hfC hfm hfs hg0 hgC hgm hgs hs hu huv
  · intro u v s hu huv hs
    have hh := hX.heat_competitor_EVI K n hn p g f C hg0 hgC hgm hgs hf0 hfC hfm hfs hs hu huv
    dsimp only [D,P,Q]
    simpa only [wassersteinSq_symm (heatMeasure μ hX.quadratic s f)] using hh



 
theorem NoncollapsedRCD.heat_wasserstein_contraction
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {rf : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ rf)
    (hg0 : 0 ≤ g) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hgm : ∫x, g x ∂hausdorff n X = 1)
    {rg : ℝ} (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ rg)
    {b : ℝ} (hb : 0 ≤ b) :
    letI : SeparableSpace X := hX.separable
    letI : ProperSpace X := hX.proper K n hn
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic b f)
        (heatMeasure (hausdorff n X) hX.quadratic b g)).toReal ≤
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic 0 f)
        (heatMeasure (hausdorff n X) hX.quadratic 0 g)).toReal*Real.exp (-2*K*b) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  rcases hb.eq_or_lt with hb|hb
  · subst b
    simp only [mul_zero,Real.exp_zero,mul_one,le_refl]
  let := ACWassersteinProbability.metric μ K n hX.cd
  let ρ := hX.heatProbability K n hn p f hf0 ⟨rf,hfs⟩ hfm
  let σ := hX.heatProbability K n hn p g hg0 ⟨rg,hgs⟩ hgm
  let D : ℝ → ℝ := fun t => dist (ρ t) (σ t)^2
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hgabs : ∀ᵐ x ∂μ, |g x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hg0,hgC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hρ : ContinuousOn ρ (Icc 0 b) := by
    simpa only [uIcc_of_le hb.le] using (metricAC_uniformContinuousOn
      (hX.heat_probability_absolutelyContinuous K n hn p f hf0 ⟨rf,hfs⟩ hfm C hfabs b hb.le)).continuousOn
  have hσ : ContinuousOn σ (Icc 0 b) := by
    simpa only [uIcc_of_le hb.le] using (metricAC_uniformContinuousOn
      (hX.heat_probability_absolutelyContinuous K n hn p g hg0 ⟨rg,hgs⟩ hgm C hgabs b hb.le)).continuousOn
  have hcI : ContinuousWithinAt D (Icc 0 b) 0 :=
    ((hρ 0 ⟨le_rfl,hb.le⟩).dist (hσ 0 ⟨le_rfl,hb.le⟩)).pow 2
  have hc : ContinuousWithinAt D (Ioi 0) 0 :=
    (hcI.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hb)).mono Ioi_subset_Ici_self
  have heq (t : ℝ) (ht : 0 ≤ t) : D t =
      (wassersteinSq (heatMeasure μ hX.quadratic t f) (heatMeasure μ hX.quadratic t g)).toReal := by
    rw [show D t = dist (ρ t) (σ t)^2 from rfl,ACWassersteinProbability.dist_sq μ hX.cd]
    dsimp only [ρ,σ,NoncollapsedRCD.heatProbability]
    rw [max_eq_left ht]
  have he : ∀ᶠ a in 𝓝[>] (0:ℝ), D b ≤ D a*Real.exp (-2*K*(b-a)) := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hb)] with a ha ha'
    rw [heq b hb.le,heq a (show 0 < a from ha).le]
    exact hX.heat_wasserstein_contraction_positive K n hn p f g C hf0 hfC hfm hfs hg0 hgC hgm hgs ha (le_of_lt ha')
  have hex : Continuous (fun a : ℝ => Real.exp (-2*K*(b-a))) := by fun_prop
  have hlim : Tendsto (fun a : ℝ => D a*Real.exp (-2*K*(b-a))) (𝓝[>] 0)
      (𝓝 (D 0*Real.exp (-2*K*b))) := by
    simpa only [sub_zero] using hc.tendsto.mul hex.continuousAt.continuousWithinAt.tendsto
  have hh := ge_of_tendsto hlim he
  rwa [heq b hb.le,heq 0 le_rfl] at hh



 
noncomputable def uniformDensityLp (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hAt : μ A ≠ ∞) : Lp ℝ 2 μ :=
  (μ A).toReal⁻¹ • indicatorConstLp 2 hA hAt 1

omit [MetricSpace X] [BorelSpace X] in
theorem uniformDensityLp_ae (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hAt : μ A ≠ ∞) :
    uniformDensityLp μ A hA hAt =ᵐ[μ] A.indicator (fun _ => (μ A).toReal⁻¹) := by
  filter_upwards [Lp.coeFn_smul (μ A).toReal⁻¹ (indicatorConstLp 2 hA hAt (1:ℝ)),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hAt) (c := (1:ℝ))] with x he hi
  change (uniformDensityLp μ A hA hAt) x = (μ A).toReal⁻¹ * (indicatorConstLp 2 hA hAt (1:ℝ)) x at he
  rw [he,hi]
  by_cases hx : x ∈ A <;> simp [hx]

omit [MetricSpace X] [BorelSpace X] in
theorem uniformDensityLp_nonneg (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hAt : μ A ≠ ∞) : 0 ≤ uniformDensityLp μ A hA hAt := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [uniformDensityLp_ae μ A hA hAt] with x hx
  rw [hx]
  exact indicator_nonneg (fun _ _ => inv_nonneg.mpr ENNReal.toReal_nonneg) x

omit [MetricSpace X] [BorelSpace X] in
theorem uniformDensityLp_bound (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hAt : μ A ≠ ∞) :
    ∀ᵐ x ∂μ, uniformDensityLp μ A hA hAt x ≤ (μ A).toReal⁻¹ := by
  filter_upwards [uniformDensityLp_ae μ A hA hAt] with x hx
  rw [hx]
  by_cases h : x ∈ A <;> simp [h,ENNReal.toReal_nonneg]

omit [MetricSpace X] [BorelSpace X] in
theorem uniformDensityLp_integral (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (hA0 : μ A ≠ 0) :
    (∫x, uniformDensityLp μ A hA hAt x ∂μ) = 1 := by
  rw [integral_congr_ae (uniformDensityLp_ae μ A hA hAt),integral_indicator hA,
    integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ]
  exact mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hA0,hAt⟩)

variable [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem uniformDensityLp_heat_zero (A : Set X)
    (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (hA0 : μ A ≠ 0) :
    heatMeasure μ hQ 0 (uniformDensityLp μ A hA hAt) = uniformOn μ A := by
  simp only [heatMeasure,heatAt_zero,one_apply_eq_self]
  have he : (fun x => ENNReal.ofReal ((uniformDensityLp μ A hA hAt) x)) =ᵐ[μ]
      A.indicator (fun _ => (μ A)⁻¹) := by
    filter_upwards [uniformDensityLp_ae μ A hA hAt] with x hx
    rw [hx]
    by_cases h : x ∈ A
    · simp only [indicator_of_mem h,ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hA0 hAt),
        ENNReal.ofReal_toReal hAt]
    · simp [h]
  rw [withDensity_congr_ae he,withDensity_indicator hA,withDensity_const]
  rfl

theorem heat_uniformDensityLp_pair (A : Set X)
    (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (f : Lp ℝ 2 μ) (t : ℝ)
    {φ : X → ℝ} (hφ : φ =ᵐ[μ] f) :
    (∫x, φ x ∂heatMeasure μ hQ t (uniformDensityLp μ A hA hAt)) =
      ⨍x in A, heatAt μ hQ t f x ∂μ := by
  rw [integral_heatMeasure μ hQ _ (uniformDensityLp_nonneg μ A hA hAt)]
  have he : (∫x, φ x*heatAt μ hQ t (uniformDensityLp μ A hA hAt) x ∂μ) =
      inner ℝ f (heatAt μ hQ t (uniformDensityLp μ A hA hAt)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφ] with x hx
    simp only [hx,Real.inner_apply]
  rw [he,←heatAt_inner μ hQ t,real_inner_comm]
  simp only [uniformDensityLp,inner_smul_left,conj_trivial,L2.inner_indicatorConstLp_one,
    average,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,Measure.restrict_apply_univ]


end

 
section
open MeasureTheory Set
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem square_integral_le_integral_square {f : X → ℝ} (hf : MemLp f 2 μ) :
    (∫x, f x ∂μ)^2 ≤ ∫x, (f x)^2 ∂μ := by
  let m := ∫x, f x ∂μ
  have hi := hf.integrable (by norm_num)
  have hv : 0 ≤ ∫x, (f x-m)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have he : (∫x, (f x-m)^2 ∂μ) = (∫x, (f x)^2 ∂μ)-m^2 := by
    simp_rw [sub_sq]
    rw [integral_add (f := fun x => f x^2-2*f x*m) (g := fun _ => m^2) (hf.integrable_sq.sub ((hi.const_mul 2).mul_const m)) (integrable_const _),
      integral_sub (f := fun x => f x^2) (g := fun x => 2*f x*m) hf.integrable_sq ((hi.const_mul 2).mul_const m),integral_mul_const,integral_const_mul]
    simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
    dsimp [m]
    ring
  rw [he] at hv
  linarith


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X]

theorem transportCost_real_integral {π : Measure (X×X)} (hc : transportCost π ≠ ∞) :
    Integrable (fun xy : X×X => dist xy.1 xy.2^2) π ∧
      (transportCost π).toReal = ∫xy : X×X, dist xy.1 xy.2^2 ∂π := by
  have hm : AEStronglyMeasurable (fun xy : X×X => dist xy.1 xy.2^2) π := by fun_prop
  have hn : ∀ᵐ xy : X×X ∂π, 0 ≤ dist xy.1 xy.2^2 := Eventually.of_forall fun _ => sq_nonneg _
  have hi : Integrable (fun xy : X×X => dist xy.1 xy.2^2) π := by
    apply (lintegral_ofReal_ne_top_iff_integrable hm hn).mp
    simpa only [transportCost,ENNReal.ofReal_pow dist_nonneg] using hc
  refine ⟨hi,?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi hn
  simp only [ENNReal.ofReal_pow dist_nonneg] at he
  change ENNReal.ofReal _ = transportCost π at he
  rw [←he,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]

theorem optimal_transport_lipschitz_mean {ν σ : Measure X}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (hν : FiniteSecondMoment ν) (hσ : FiniteSecondMoment σ)
    {π : Measure (X×X)} (hπ : IsOptimalCoupling ν σ π)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (M : ℝ) (hM : ∀ x, |φ x| ≤ M) :
    ((∫x, φ x ∂ν)-(∫x, φ x ∂σ))^2 ≤ (L:ℝ)^2*(wassersteinSq ν σ).toReal := by
  let := coupling_probability_of_fst hπ.1
  have hc := finite_second_moment_cost hν hσ hπ.1 hπ.2.1
  obtain ⟨hi,he⟩ := transportCost_real_integral hc
  have hp (j : X×X → X) (hj : Measurable j) : MemLp (fun xy => φ (j xy)) 2 π := by
    apply (memLp_const M).mono' (hφ.continuous.measurable.comp hj).aestronglyMeasurable
    exact Eventually.of_forall fun xy => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hM (j xy)
  have h0 := hp Prod.fst measurable_fst
  have h1 := hp Prod.snd measurable_snd
  have hd := h0.sub h1
  have hav := square_integral_le_integral_square hd
  have hbound : (∫xy : X×X, (φ xy.1-φ xy.2)^2 ∂π) ≤
      (L:ℝ)^2*(∫xy : X×X, dist xy.1 xy.2^2 ∂π) := by
    rw [←integral_const_mul]
    apply integral_mono hd.integrable_sq (hi.const_mul _)
    intro xy
    have hh := hφ.dist_le_mul xy.1 xy.2
    rw [Real.dist_eq] at hh
    have hh' := pow_le_pow_left₀ (abs_nonneg _) hh 2
    simpa only [sq_abs,mul_pow,Pi.sub_apply] using hh'
  have h0e : (∫xy : X×X, φ xy.1 ∂π) = ∫x, φ x ∂ν := by
    rw [←hπ.1]
    exact (integral_map measurable_fst.aemeasurable hφ.continuous.aestronglyMeasurable).symm
  have h1e : (∫xy : X×X, φ xy.2 ∂π) = ∫x, φ x ∂σ := by
    rw [←hπ.2.1]
    exact (integral_map measurable_snd.aemeasurable hφ.continuous.aestronglyMeasurable).symm
  have hh := hav.trans hbound
  change (∫xy : X×X, φ xy.1-φ xy.2 ∂π)^2 ≤ _ at hh
  rw [integral_sub (h0.integrable (by norm_num)) (h1.integrable (by norm_num)),h0e,h1e,←he,
    ←wassersteinSq_eq_cost hπ] at hh
  exact hh


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X]

omit [BorelSpace X] in
theorem wassersteinSq_ball_bound {ν σ : Measure X}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (x y : X) {r : ℝ} (_ : 0 ≤ r)
    (hν : ∀ᵐ z ∂ν, dist z x ≤ r) (hσ : ∀ᵐ z ∂σ, dist z y ≤ r) :
    (wassersteinSq ν σ).toReal ≤ (dist x y+2*r)^2 := by
  have h0 : (ν.prod σ).map Prod.fst = ν := by simp
  have h1 : (ν.prod σ).map Prod.snd = σ := by simp
  have hd : ∀ᵐ z : X×X ∂ν.prod σ, dist z.1 z.2 ≤ dist x y+2*r := by
    have ha : ∀ᵐ z : X×X ∂ν.prod σ, dist z.1 x ≤ r := by
      apply ae_of_ae_map measurable_fst.aemeasurable (p := fun z => dist z x ≤ r)
      rwa [h0]
    have hb : ∀ᵐ z : X×X ∂ν.prod σ, dist z.2 y ≤ r := by
      apply ae_of_ae_map measurable_snd.aemeasurable (p := fun z => dist z y ≤ r)
      rwa [h1]
    filter_upwards [ha,hb] with z ha hb
    have hh := dist_triangle4 z.1 x y z.2
    rw [dist_comm y z.2] at hh
    linarith
  have hc : transportCost (ν.prod σ) ≤ ENNReal.ofReal ((dist x y+2*r)^2) := by
    calc
      transportCost (ν.prod σ) ≤ ∫⁻z : X×X, ENNReal.ofReal ((dist x y+2*r)^2) ∂ν.prod σ := by
        apply lintegral_mono_ae
        filter_upwards [hd] with z hz
        rw [←ENNReal.ofReal_pow dist_nonneg]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ dist_nonneg hz 2)
      _ = _ := by simp
  have hw := (wassersteinSq_le_cost h0 h1).trans hc
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hw).trans_eq
    (ENNReal.toReal_ofReal (sq_nonneg _))


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {μ : Measure X} [IsLocallyFiniteMeasure μ]
  [IsUnifLocDoublingMeasure μ]

theorem exists_lipschitz_of_average_bound (u : X → ℝ) (hu : LocallyIntegrable u μ)
    (L : ℝ≥0) (h : ∀ x y : X, ∀ r : ℝ, 0 < r →
      |(⨍z in closedBall x r, u z ∂μ) - (⨍z in closedBall y r, u z ∂μ)| ≤
        L * (dist x y + 2*r)) :
    ∃ v : X → ℝ, LipschitzWith L v ∧ u =ᵐ[μ] v := by
  let S := {x : X | Tendsto (fun r : ℝ => ⨍z in closedBall x r, u z ∂μ)
    (𝓝[>] 0) (𝓝 (u x))}
  have hS : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ hu (1:ℝ)] with x hx
    exact hx (fun _ : ℝ => x) id tendsto_id (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_closedBall,dist_self,one_mul]
      exact le_of_lt hr)
  have hl : LipschitzOnWith L u S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hc : Tendsto (fun r : ℝ => L*(dist x y+2*r)) (𝓝[>] 0)
        (𝓝 (L*dist x y)) := by
      have hh : Continuous (fun r : ℝ => (L:ℝ)*(dist x y+2*r)) := by fun_prop
      simpa using (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have hb : ∀ᶠ r in 𝓝[>] (0:ℝ),
        |(⨍z in closedBall x r, u z ∂μ) - (⨍z in closedBall y r, u z ∂μ)| ≤
          L*(dist x y+2*r) := by
      filter_upwards [self_mem_nhdsWithin] with r hr using h x y r hr
    simpa only [Real.dist_eq] using le_of_tendsto_of_tendsto ((hx.sub hy).abs) hc hb
  obtain ⟨v,hv,he⟩ := hl.extend_real
  refine ⟨v,hv,?_⟩
  filter_upwards [hS] with x hx
  exact he hx


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.heat_lipschitz
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (f : Lp ℝ 2 (hausdorff n X)) {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (hf : φ =ᵐ[hausdorff n X] f)
    (M : ℝ) (hM : ∀ x, |φ x| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∃ v : X → ℝ, LipschitzWith (L*⟨Real.exp (-K*t),(Real.exp_pos _).le⟩) v ∧
      (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] v := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsUnifLocDoublingMeasure μ := hX.locDoubling K n hn
  let L' : ℝ≥0 := L*⟨Real.exp (-K*t),(Real.exp_pos _).le⟩
  apply exists_lipschitz_of_average_bound (heatAt μ hX.quadratic t f)
    ((Lp.memLp _).locallyIntegrable (by norm_num)) L'
  intro x y r hr
  let A := closedBall x r
  let B := closedBall y r
  have hA0 : μ A ≠ 0 := ne_of_gt ((hX.fullSupport x r hr).trans_le (measure_mono ball_subset_closedBall))
  have hB0 : μ B ≠ 0 := ne_of_gt ((hX.fullSupport y r hr).trans_le (measure_mono ball_subset_closedBall))
  have hAt : μ A ≠ ∞ := ne_of_lt (hX.finiteOnBounded A isBounded_closedBall)
  have hBt : μ B ≠ ∞ := ne_of_lt (hX.finiteOnBounded B isBounded_closedBall)
  let a := uniformDensityLp μ A measurableSet_closedBall hAt
  let b := uniformDensityLp μ B measurableSet_closedBall hBt
  have ha0 : 0 ≤ a := uniformDensityLp_nonneg μ A measurableSet_closedBall hAt
  have hb0 : 0 ≤ b := uniformDensityLp_nonneg μ B measurableSet_closedBall hBt
  have ham : ∫z, a z ∂μ = 1 := uniformDensityLp_integral μ A measurableSet_closedBall hAt hA0
  have hbm : ∫z, b z ∂μ = 1 := uniformDensityLp_integral μ B measurableSet_closedBall hBt hB0
  have has : ∀ᵐ z ∂μ, a z ≠ 0 → dist x z ≤ r := by
    filter_upwards [uniformDensityLp_ae μ A measurableSet_closedBall hAt] with z hz hne
    have hh : z ∈ A := by by_contra hh; exact hne (hz.trans (indicator_of_notMem hh _))
    simpa only [A,mem_closedBall,dist_comm] using hh
  have hbs : ∀ᵐ z ∂μ, b z ≠ 0 → dist x z ≤ dist x y+r := by
    filter_upwards [uniformDensityLp_ae μ B measurableSet_closedBall hBt] with z hz hne
    have hh : z ∈ B := by by_contra hh; exact hne (hz.trans (indicator_of_notMem hh _))
    have hh' : dist y z ≤ r := by simpa only [B,mem_closedBall,dist_comm] using hh
    exact (dist_triangle x y z).trans (add_le_add_right hh' _)
  let C : ℝ≥0 := ⟨max (μ A).toReal⁻¹ (μ B).toReal⁻¹,
    (inv_nonneg.mpr ENNReal.toReal_nonneg).trans (le_max_left _ _)⟩
  have haC : ∀ᵐ z ∂μ, a z ≤ C :=
    (uniformDensityLp_bound μ A measurableSet_closedBall hAt).mono fun z hz => hz.trans (le_max_left _ _)
  have hbC : ∀ᵐ z ∂μ, b z ≤ C :=
    (uniformDensityLp_bound μ B measurableSet_closedBall hBt).mono fun z hz => hz.trans (le_max_right _ _)
  let ν := heatMeasure μ hX.quadratic t a
  let σ := heatMeasure μ hX.quadratic t b
  obtain ⟨hνp,hνa,hνm,_⟩ := hX.heat_law K n hn x a ha0 ⟨r,has⟩ ham t ht
  obtain ⟨hσp,hσa,hσm,_⟩ := hX.heat_law K n hn x b hb0 ⟨dist x y+r,hbs⟩ hbm t ht
  let : IsProbabilityMeasure ν := hνp
  let : IsProbabilityMeasure σ := hσp
  obtain ⟨plan,_,_,hopt,_⟩ := hX.cd ν σ hνp hσp hνa hσa hνm hσm
  have hm := optimal_transport_lipschitz_mean hνm hσm hopt hφ M hM
  have hc := hX.heat_wasserstein_contraction K n hn x a b C ha0 haC ham has hb0 hbC hbm hbs ht
  rw [uniformDensityLp_heat_zero μ hX.quadratic A measurableSet_closedBall hAt hA0,
    uniformDensityLp_heat_zero μ hX.quadratic B measurableSet_closedBall hBt hB0] at hc
  let : IsProbabilityMeasure (uniformOn μ A) := uniformOn_probability μ A hA0 hAt
  let : IsProbabilityMeasure (uniformOn μ B) := uniformOn_probability μ B hB0 hBt
  have hw := wassersteinSq_ball_bound x y hr.le
    (uniformOn_ae_mem μ A measurableSet_closedBall) (uniformOn_ae_mem μ B measurableSet_closedBall)
  have hsq : ((∫z, φ z ∂ν)-(∫z, φ z ∂σ))^2 ≤
      ((L':ℝ)*(dist x y+2*r))^2 := by
    calc _ ≤ (L:ℝ)^2*(wassersteinSq ν σ).toReal := hm
      _ ≤ (L:ℝ)^2*((wassersteinSq (uniformOn μ A) (uniformOn μ B)).toReal*Real.exp (-2*K*t)) :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      _ ≤ (L:ℝ)^2*((dist x y+2*r)^2*Real.exp (-2*K*t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le) (sq_nonneg _)
      _ = _ := by
        have he : Real.exp (-2*K*t) = Real.exp (-K*t)^2 := by
          rw [←Real.exp_nat_mul]; congr 1; ring
        change (L:ℝ)^2*((dist x y+2*r)^2*Real.exp (-2*K*t)) =
          ((L:ℝ)*Real.exp (-K*t)*(dist x y+2*r))^2
        rw [he]; ring
  have hh : |(∫z, φ z ∂ν)-(∫z, φ z ∂σ)| ≤ (L':ℝ)*(dist x y+2*r) := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg L'.coe_nonneg (by positivity))).mp
    simpa only [sq_abs] using hsq
  rw [heat_uniformDensityLp_pair μ hX.quadratic A measurableSet_closedBall hAt f t hf,
    heat_uniformDensityLp_pair μ hX.quadratic B measurableSet_closedBall hBt f t hf] at hh
  exact hh


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X]

theorem optimal_transport_quadratic_dual {ν σ : Measure X}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (hν : FiniteSecondMoment ν) (hσ : FiniteSecondMoment σ)
    {π : Measure (X×X)} (hπ : IsOptimalCoupling ν σ π)
    {φ ψ : X → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (M N : ℝ) (hM : ∀ x, |φ x| ≤ M) (hN : ∀ x, |ψ x| ≤ N)
    {c : ℝ} (hc : ∀ x y, ψ x-φ y ≤ c*dist x y^2) :
    (∫x, ψ x ∂ν)-(∫x, φ x ∂σ) ≤ c*(wassersteinSq ν σ).toReal := by
  let := coupling_probability_of_fst hπ.1
  obtain ⟨hi,he⟩ := transportCost_real_integral
    (finite_second_moment_cost hν hσ hπ.1 hπ.2.1)
  have h0 : Integrable (fun xy : X×X => ψ xy.1) π := by
    have hm : MemLp (fun xy : X×X => ψ xy.1) 1 π :=
      (memLp_const N).mono' (hψ.comp measurable_fst).aestronglyMeasurable
        (Eventually.of_forall fun xy => by simpa only [Real.norm_eq_abs] using hN xy.1)
    exact memLp_one_iff_integrable.mp hm
  have h1 : Integrable (fun xy : X×X => φ xy.2) π := by
    have hm : MemLp (fun xy : X×X => φ xy.2) 1 π :=
      (memLp_const M).mono' (hφ.comp measurable_snd).aestronglyMeasurable
        (Eventually.of_forall fun xy => by simpa only [Real.norm_eq_abs] using hM xy.2)
    exact memLp_one_iff_integrable.mp hm
  have hh : (∫xy : X×X, ψ xy.1-φ xy.2 ∂π) ≤ c*(∫xy : X×X, dist xy.1 xy.2^2 ∂π) := by
    rw [←integral_const_mul]
    apply integral_mono (h0.sub h1) (hi.const_mul _)
    intro xy
    exact hc xy.1 xy.2
  have h0e : (∫xy : X×X, ψ xy.1 ∂π) = ∫x, ψ x ∂ν := by
    rw [←hπ.1]
    exact (integral_map measurable_fst.aemeasurable hψ.aestronglyMeasurable).symm
  have h1e : (∫xy : X×X, φ xy.2 ∂π) = ∫x, φ x ∂σ := by
    rw [←hπ.2.1]
    exact (integral_map measurable_snd.aemeasurable hφ.aestronglyMeasurable).symm
  rw [integral_sub h0 h1,h0e,h1e,←he,←wassersteinSq_eq_cost hπ] at hh
  exact hh


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.heat_average_quadratic_dual
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (f g : Lp ℝ 2 (hausdorff n X)) {φ ψ : X → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hf : φ =ᵐ[hausdorff n X] f) (hg : ψ =ᵐ[hausdorff n X] g)
    (M N : ℝ) (hM : ∀ x, |φ x| ≤ M) (hN : ∀ x, |ψ x| ≤ N)
    {c : ℝ} (hc0 : 0 ≤ c) (hd : ∀ x y, ψ x-φ y ≤ c*dist x y^2)
    {t : ℝ} (ht : 0 ≤ t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ x y : X, ∀ r : ℝ, 0 < r →
      (⨍z in closedBall x r, heatAt (hausdorff n X) hX.quadratic t g z ∂hausdorff n X) -
        (⨍z in closedBall y r, heatAt (hausdorff n X) hX.quadratic t f z ∂hausdorff n X) ≤
      c*Real.exp (-2*K*t)*(dist x y+2*r)^2 := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro x y r hr
  let A := closedBall x r
  let B := closedBall y r
  have hA0 : μ A ≠ 0 := ne_of_gt ((hX.fullSupport x r hr).trans_le (measure_mono ball_subset_closedBall))
  have hB0 : μ B ≠ 0 := ne_of_gt ((hX.fullSupport y r hr).trans_le (measure_mono ball_subset_closedBall))
  have hAt : μ A ≠ ∞ := ne_of_lt (hX.finiteOnBounded A isBounded_closedBall)
  have hBt : μ B ≠ ∞ := ne_of_lt (hX.finiteOnBounded B isBounded_closedBall)
  let a := uniformDensityLp μ A measurableSet_closedBall hAt
  let b := uniformDensityLp μ B measurableSet_closedBall hBt
  have ha0 : 0 ≤ a := uniformDensityLp_nonneg μ A measurableSet_closedBall hAt
  have hb0 : 0 ≤ b := uniformDensityLp_nonneg μ B measurableSet_closedBall hBt
  have ham : ∫z, a z ∂μ = 1 := uniformDensityLp_integral μ A measurableSet_closedBall hAt hA0
  have hbm : ∫z, b z ∂μ = 1 := uniformDensityLp_integral μ B measurableSet_closedBall hBt hB0
  have has : ∀ᵐ z ∂μ, a z ≠ 0 → dist x z ≤ r := by
    filter_upwards [uniformDensityLp_ae μ A measurableSet_closedBall hAt] with z hz hne
    have hh : z ∈ A := by by_contra hh; exact hne (hz.trans (indicator_of_notMem hh _))
    simpa only [A,mem_closedBall,dist_comm] using hh
  have hbs : ∀ᵐ z ∂μ, b z ≠ 0 → dist x z ≤ dist x y+r := by
    filter_upwards [uniformDensityLp_ae μ B measurableSet_closedBall hBt] with z hz hne
    have hh : z ∈ B := by by_contra hh; exact hne (hz.trans (indicator_of_notMem hh _))
    have hh' : dist y z ≤ r := by simpa only [B,mem_closedBall,dist_comm] using hh
    exact (dist_triangle x y z).trans (add_le_add_right hh' _)
  let C : ℝ≥0 := ⟨max (μ A).toReal⁻¹ (μ B).toReal⁻¹,
    (inv_nonneg.mpr ENNReal.toReal_nonneg).trans (le_max_left _ _)⟩
  have haC : ∀ᵐ z ∂μ, a z ≤ C :=
    (uniformDensityLp_bound μ A measurableSet_closedBall hAt).mono fun z hz => hz.trans (le_max_left _ _)
  have hbC : ∀ᵐ z ∂μ, b z ≤ C :=
    (uniformDensityLp_bound μ B measurableSet_closedBall hBt).mono fun z hz => hz.trans (le_max_right _ _)
  let ν := heatMeasure μ hX.quadratic t a
  let σ := heatMeasure μ hX.quadratic t b
  obtain ⟨hνp,hνa,hνm,_⟩ := hX.heat_law K n hn x a ha0 ⟨r,has⟩ ham t ht
  obtain ⟨hσp,hσa,hσm,_⟩ := hX.heat_law K n hn x b hb0 ⟨dist x y+r,hbs⟩ hbm t ht
  let : IsProbabilityMeasure ν := hνp
  let : IsProbabilityMeasure σ := hσp
  obtain ⟨plan,_,_,hopt,_⟩ := hX.cd ν σ hνp hσp hνa hσa hνm hσm
  have hm := optimal_transport_quadratic_dual hνm hσm hopt hφ hψ M N hM hN hd
  have hc := hX.heat_wasserstein_contraction K n hn x a b C ha0 haC ham has hb0 hbC hbm hbs ht
  rw [uniformDensityLp_heat_zero μ hX.quadratic A measurableSet_closedBall hAt hA0,
    uniformDensityLp_heat_zero μ hX.quadratic B measurableSet_closedBall hBt hB0] at hc
  let : IsProbabilityMeasure (uniformOn μ A) := uniformOn_probability μ A hA0 hAt
  let : IsProbabilityMeasure (uniformOn μ B) := uniformOn_probability μ B hB0 hBt
  have hw := wassersteinSq_ball_bound x y hr.le
    (uniformOn_ae_mem μ A measurableSet_closedBall) (uniformOn_ae_mem μ B measurableSet_closedBall)
  have hh : (∫z, ψ z ∂ν)-(∫z, φ z ∂σ) ≤
      c*Real.exp (-2*K*t)*(dist x y+2*r)^2 := by
    calc _ ≤ c*(wassersteinSq ν σ).toReal := hm
      _ ≤ c*((wassersteinSq (uniformOn μ A) (uniformOn μ B)).toReal*Real.exp (-2*K*t)) :=
        mul_le_mul_of_nonneg_left hc hc0
      _ ≤ c*((dist x y+2*r)^2*Real.exp (-2*K*t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le) hc0
      _ = _ := by ring
  rw [heat_uniformDensityLp_pair μ hX.quadratic A measurableSet_closedBall hAt g t hg,
    heat_uniformDensityLp_pair μ hX.quadratic B measurableSet_closedBall hBt f t hf] at hh
  exact hh


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {μ : Measure X} [IsLocallyFiniteMeasure μ]
  [IsUnifLocDoublingMeasure μ] [μ.IsOpenPosMeasure]

theorem quadratic_comparison_of_average_bound
    (u v U V : X → ℝ) (hu : LocallyIntegrable u μ) (hv : LocallyIntegrable v μ)
    (hU : Continuous U) (hV : Continuous V) (heU : u =ᵐ[μ] U) (heV : v =ᵐ[μ] V)
    (c : ℝ) (h : ∀ x y : X, ∀ r : ℝ, 0 < r →
      (⨍z in closedBall x r, u z ∂μ) - (⨍z in closedBall y r, v z ∂μ) ≤
        c*(dist x y + 2*r)^2) :
    ∀ x y, U x-V y ≤ c*dist x y^2 := by
  let S := {x : X | Tendsto (fun r : ℝ => ⨍z in closedBall x r, u z ∂μ)
    (𝓝[>] 0) (𝓝 (U x))}
  let T := {x : X | Tendsto (fun r : ℝ => ⨍z in closedBall x r, v z ∂μ)
    (𝓝[>] 0) (𝓝 (V x))}
  have hS : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ hu (1:ℝ),heU] with x hx he
    change Tendsto _ _ (𝓝 (U x))
    rw [←he]
    exact hx (fun _ : ℝ => x) id tendsto_id (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_closedBall,dist_self,one_mul]
      exact le_of_lt hr)
  have hT : ∀ᵐ x ∂μ, x ∈ T := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ hv (1:ℝ),heV] with x hx he
    change Tendsto _ _ (𝓝 (V x))
    rw [←he]
    exact hx (fun _ : ℝ => x) id tendsto_id (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_closedBall,dist_self,one_mul]
      exact le_of_lt hr)
  have hST : ∀ x ∈ S, ∀ y ∈ T, U x-V y ≤ c*dist x y^2 := by
    intro x hx y hy
    have hc : Tendsto (fun r : ℝ => c*(dist x y+2*r)^2) (𝓝[>] 0)
        (𝓝 (c*dist x y^2)) := by
      have hh : Continuous (fun r : ℝ => c*(dist x y+2*r)^2) := by fun_prop
      simpa using (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have hb : ∀ᶠ r in 𝓝[>] (0:ℝ),
        (⨍z in closedBall x r, u z ∂μ) - (⨍z in closedBall y r, v z ∂μ) ≤
          c*(dist x y+2*r)^2 := by
      filter_upwards [self_mem_nhdsWithin] with r hr using h x y r hr
    exact le_of_tendsto_of_tendsto (hx.sub hy) hc hb
  have hd : Dense (S ×ˢ T) := (Measure.dense_of_ae hS).prod (Measure.dense_of_ae hT)
  have hc : IsClosed {z : X×X | U z.1-V z.2 ≤ c*dist z.1 z.2^2} :=
    isClosed_le ((hU.comp continuous_fst).sub (hV.comp continuous_snd)) (by fun_prop)
  have hs : closure (S ×ˢ T) ⊆ {z : X×X | U z.1-V z.2 ≤ c*dist z.1 z.2^2} :=
    hc.closure_subset_iff.mpr (fun z hz => hST z.1 hz.1 z.2 hz.2)
  intro x y
  exact hs (hd (x,y))


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.openPos (K : ℝ) (n : ℕ) (hX : NoncollapsedRCD K n X) :
    (hausdorff n X).IsOpenPosMeasure := by
  constructor
  intro S hS ⟨x,hx⟩
  obtain ⟨r,hr,hrs⟩ := Metric.isOpen_iff.mp hS x hx
  exact ne_of_gt ((hX.fullSupport x r hr).trans_le (measure_mono hrs))

theorem NoncollapsedRCD.heat_pointwise_quadratic_dual
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (f g : Lp ℝ 2 (hausdorff n X)) {φ ψ : X → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hf : φ =ᵐ[hausdorff n X] f) (hg : ψ =ᵐ[hausdorff n X] g)
    (M N : ℝ) (hM : ∀ x, |φ x| ≤ M) (hN : ∀ x, |ψ x| ≤ N)
    {c : ℝ} (hc0 : 0 ≤ c) (hd : ∀ x y, ψ x-φ y ≤ c*dist x y^2)
    {t : ℝ} (ht : 0 ≤ t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ U V : X → ℝ, Continuous U → Continuous V →
      (heatAt (hausdorff n X) hX.quadratic t g : X → ℝ) =ᵐ[hausdorff n X] U →
      (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V →
      ∀ x y, U x-V y ≤ c*Real.exp (-2*K*t)*dist x y^2 := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsUnifLocDoublingMeasure μ := hX.locDoubling K n hn
  let : μ.IsOpenPosMeasure := hX.openPos K n
  intro U V hU hV heU heV
  exact quadratic_comparison_of_average_bound _ _ U V
    ((Lp.memLp _).locallyIntegrable (by norm_num)) ((Lp.memLp _).locallyIntegrable (by norm_num))
    hU hV heU heV _ (hX.heat_average_quadratic_dual K n hn f g hφ hψ hf hg M N hM hN hc0 hd ht)

theorem NoncollapsedRCD.heat_hopfLax_comparison
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (f g : Lp ℝ 2 (hausdorff n X)) {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) {s : ℝ} (hs : 0 < s)
    (hf : φ =ᵐ[hausdorff n X] f) (hg : hopfLax φ s =ᵐ[hausdorff n X] g)
    (M : ℝ) (hM : ∀ x, |φ x| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∃ U V : X → ℝ,
      LipschitzWith (L*⟨Real.exp (-K*t),(Real.exp_pos _).le⟩) U ∧
      LipschitzWith (L*⟨Real.exp (-K*t),(Real.exp_pos _).le⟩) V ∧
      (heatAt (hausdorff n X) hX.quadratic t g : X → ℝ) =ᵐ[hausdorff n X] U ∧
      (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V ∧
      ∀ x, U x ≤ hopfLax V (s*Real.exp (2*K*t)) x := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hψ := hopfLax_lipschitz hφ hX.geodesic hs
  have hN : ∀ x, |hopfLax φ s x| ≤ M+s*(L:ℝ)^2/2 := by
    intro x
    have hh := hopfLax_bounds hφ hs x
    have hm := abs_le.mp (hM x)
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (L:ℝ)]
  obtain ⟨U,hU,heU⟩ := hX.heat_lipschitz K n hn g hψ hg _ hN ht
  obtain ⟨V,hV,heV⟩ := hX.heat_lipschitz K n hn f hφ hf M hM ht
  refine ⟨U,V,hU,hV,heU,heV,?_⟩
  have hdual := hX.heat_pointwise_quadratic_dual K n hn f g hφ.continuous.measurable
    hψ.continuous.measurable hf hg M _ hM hN (by positivity : 0 ≤ 1/(2*s))
      (fun x y => by
        have h := hopfLax_le_cost hφ hs x y
        simp only [div_eq_mul_inv,one_mul] at h ⊢
        nlinarith [h])
      ht U V hU.continuous hV.continuous heU heV
  intro x
  apply le_csInf ⟨_,mem_range_self x⟩
  rintro _ ⟨y,rfl⟩
  have hh := hdual x y
  have he : 1/(2*s)*Real.exp (-2*K*t) = 1/(2*(s*Real.exp (2*K*t))) := by
    rw [show -2*K*t = -(2*K*t) by ring,Real.exp_neg]
    field_simp
  rw [he] at hh
  change U x ≤ V y+dist x y^2/(2*(s*Real.exp (2*K*t)))
  simp only [div_eq_mul_inv,one_mul] at hh ⊢
  nlinarith [hh]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X]

theorem slopeAtScale_real_bound {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) {r : ℝ} {x y : X} (hy : dist x y < r) :
    |φ x-φ y| ≤ (slopeAtScale φ r x).toReal*dist x y := by
  by_cases he : y=x
  · subst y; simp
  have hd : 0 < dist x y := dist_pos.mpr (Ne.symm he)
  have hi := slopeAtScale_term_le φ hy he
  have hf : slopeAtScale φ r x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (slopeAtScale_le_lipschitz hφ r x)
  have hh := ENNReal.toReal_mono hf hi
  rw [ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) hd.le)] at hh
  have hh' := (div_le_iff₀ hd).mp hh
  simpa only [abs_sub_comm] using hh'

theorem hopfLax_gap_le_scale [ProperSpace X] {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) {r s : ℝ} (hs : 0 < s) (hr : 2*s*(L:ℝ) < r) (x : X) :
    φ x-hopfLax φ s x ≤ s*(slopeAtScale φ r x).toReal^2/2 := by
  obtain ⟨y,hy,hd⟩ := hopfLax_exists_minimizer hφ hs x
  have hg := slopeAtScale_real_bound hφ (hd.trans_lt hr)
  have h0 := (le_abs_self (φ x-φ y)).trans hg
  rw [hy]
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < 2*s)).mp
  have he : (φ x-(φ y+dist x y^2/(2*s)))*(2*s) =
      2*s*(φ x-φ y)-dist x y^2 := by field_simp; ring
  rw [he]
  nlinarith [sq_nonneg (dist x y-s*(slopeAtScale φ r x).toReal)]

theorem slopeAtScale_zero_outside {φ : X → ℝ} (p : X) (R : ℝ)
    (hsupp : ∀ x, R < dist p x → φ x = 0) {r : ℝ} (hr : 0 ≤ r)
    (x : X) (hx : R+r < dist p x) : slopeAtScale φ r x = 0 := by
  apply le_antisymm ?_ bot_le
  apply iSup_le; intro y
  apply iSup_le; intro hy
  apply iSup_le; intro hne
  have hxR : R < dist p x := lt_of_le_of_lt (le_add_of_nonneg_right hr) hx
  have hyR : R < dist p y := by
    have ht := dist_triangle p y x
    rw [dist_comm y x] at ht
    linarith
  rw [hsupp x hxR,hsupp y hyR]
  simp


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

omit [BorelSpace X] in
theorem memLp_of_bounded_ball_support {f : X → ℝ} (hf : Measurable f)
    (p : X) (R M : ℝ) (hs : ∀ x, R < dist p x → f x = 0)
    (hM : ∀ x, |f x| ≤ M) : MemLp f 2 μ := by
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_closedBall p R)
    intro x hx
    exact hs x (by simpa only [mem_closedBall,not_le,dist_comm] using hx)
  exact hc.memLp_of_bound hf.aestronglyMeasurable M
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x)

omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem compact_lipschitz_abs_bound {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (p : X) (R : ℝ)
    (hs : ∀ x, R < dist p x → φ x = 0) (x : X) :
    |φ x| ≤ |φ p|+(L:ℝ)*max R 0 := by
  by_cases hx : R < dist p x
  · rw [hs x hx,abs_zero]; positivity
  · have hd := hφ.dist_le_mul x p
    simp only [Real.dist_eq,dist_comm x p] at hd
    have hm := mul_le_mul_of_nonneg_left (show dist p x ≤ max R 0 from le_max_of_le_left (le_of_not_gt hx)) L.coe_nonneg
    calc
      |φ x| ≤ |φ x-φ p|+|φ p| := by simpa only [sub_add_cancel] using abs_add_le (φ x-φ p) (φ p)
      _ ≤ _ := by linarith

theorem compact_lipschitz_memLp {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (p : X) (R : ℝ)
    (hs : ∀ x, R < dist p x → φ x = 0) : MemLp φ 2 μ :=
  memLp_of_bounded_ball_support μ hφ.continuous.measurable p R _ hs
    (compact_lipschitz_abs_bound hφ p R hs)

theorem hopfLax_compact_memLp (hgeo : IsGeodesicSpace X) {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (p : X) (R : ℝ)
    (hsupp : ∀ x, R < dist p x → φ x = 0) {s : ℝ} (hs : 0 < s) :
    MemLp (hopfLax φ s) 2 μ :=
  compact_lipschitz_memLp μ (hopfLax_lipschitz hφ hgeo hs) p (R+2*s*(L:ℝ))
    (fun _ hx => hopfLax_zero_outside hφ p R hsupp hs hx)

theorem slopeAtScale_sq_memLp {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (p : X) (R : ℝ)
    (hsupp : ∀ x, R < dist p x → φ x = 0) {r : ℝ} (hr : 0 ≤ r) :
    MemLp (fun x => (slopeAtScale φ r x).toReal^2) 2 μ := by
  apply memLp_of_bounded_ball_support μ
    ((slopeAtScale_lowerSemicontinuous hφ.continuous r).measurable.ennreal_toReal.pow_const 2)
      p (R+r) ((L:ℝ)^2)
  · intro x hx
    rw [slopeAtScale_zero_outside p R hsupp hr x hx]; simp
  · intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := ENNReal.toReal_mono (by simp : (L:ℝ≥0∞) ≠ ∞) (slopeAtScale_le_lipschitz hφ r x)
    simp only [ENNReal.coe_toReal] at h
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg h 2


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.heat_slope_quadratic_bound
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    {r s : ℝ} (hs : 0 < s) (hr : 2*s*(L:ℝ) < r)
    (hH : (fun x => (slopeAtScale φ r x).toReal^2) =ᵐ[hausdorff n X] H)
    :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ {t : ℝ}, 0 ≤ t → ∀ V : X → ℝ, Continuous V →
    (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V →
    ∀ᵐ x ∂hausdorff n X, ∀ y,
      V x-V y ≤ s/2*heatAt (hausdorff n X) hX.quadratic t H x+
        Real.exp (-2*K*t)*dist x y^2/(2*s) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro t ht V hV heV
  have hψ := hopfLax_lipschitz hφ hX.geodesic hs
  have hm := hopfLax_compact_memLp μ hX.geodesic hφ p R hsupp hs
  let g : Lp ℝ 2 μ := hm.toLp (hopfLax φ s)
  have hg : hopfLax φ s =ᵐ[μ] g := hm.coeFn_toLp.symm
  let M := |φ p|+(L:ℝ)*max R 0
  have hM : ∀ x, |φ x| ≤ M := compact_lipschitz_abs_bound hφ p R hsupp
  have hN : ∀ x, |hopfLax φ s x| ≤ M+s*(L:ℝ)^2/2 := by
    intro x
    have hh := hopfLax_bounds hφ hs x
    have hhM := abs_le.mp (hM x)
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (L:ℝ)]
  obtain ⟨U,hU,heU⟩ := hX.heat_lipschitz K n hn g hψ hg _ hN ht
  have hdual := hX.heat_pointwise_quadratic_dual K n hn f g hφ.continuous.measurable
    hψ.continuous.measurable hf hg M _ hM hN (by positivity : 0 ≤ 1/(2*s))
      (fun x y => by
        have h := hopfLax_le_cost hφ hs x y
        simp only [div_eq_mul_inv,one_mul] at h ⊢
        nlinarith [h]) ht U V hU.continuous hV heU heV
  have hle : f-g ≤ (s/2) • H := by
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hf,hg,hH,Lp.coeFn_sub f g,Lp.coeFn_smul (s/2) H] with x hf hg hH hfg hsH
    rw [hfg,hsH]
    change f x-g x ≤ s/2*H x
    rw [← hf,← hg,← hH]
    have h := hopfLax_gap_le_scale hφ hs hr x
    nlinarith [h]
  have hheat := heatAt_mono μ hX.quadratic t hle
  rw [map_sub,map_smul] at hheat
  filter_upwards [(Lp.coeFn_le _ _).mpr hheat,
    Lp.coeFn_sub (heatAt μ hX.quadratic t f) (heatAt μ hX.quadratic t g),
    Lp.coeFn_smul (s/2) (heatAt μ hX.quadratic t H),heU,heV] with x hh hfg hsH heU heV
  rw [hfg,hsH] at hh
  change heatAt μ hX.quadratic t f x-heatAt μ hX.quadratic t g x ≤
    s/2*heatAt μ hX.quadratic t H x at hh
  rw [heU,heV] at hh
  intro y
  have hd := hdual x y
  simp only [div_eq_mul_inv,one_mul] at hd ⊢
  nlinarith [hd]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

theorem quadratic_bound_of_rat {a A B d C s : ℝ} (hs : 0 < s) (hsC : s < C)
    (h : ∀ q : ℚ, 0 < (q:ℝ) → (q:ℝ) < C → a ≤ (q:ℝ)*A/2+B*d^2/(2*(q:ℝ))) :
    a ≤ s*A/2+B*d^2/(2*s) := by
  by_contra hh
  have hh' : s*A/2+B*d^2/(2*s) < a := lt_of_not_ge hh
  have hc : ContinuousAt (fun q : ℝ => q*A/2+B*d^2/(2*q)) s := by
    fun_prop (disch := positivity)
  have hi : ∀ᶠ q in 𝓝 s, q ∈ Ioo 0 C := isOpen_Ioo.mem_nhds ⟨hs,hsC⟩
  have he : ∀ᶠ q in 𝓝 s, q ∈ Ioo 0 C ∧ q*A/2+B*d^2/(2*q) < a :=
    hi.and (hc.tendsto.eventually (isOpen_Iio.mem_nhds hh'))
  obtain ⟨v,hv,⟨q,hq⟩⟩ := (mem_closure_iff_nhds.mp (Rat.denseRange_cast s)) _ he
  subst v
  exact (not_lt_of_ge (h q hv.1.1 hv.1.2)) hv.2

variable {X : Type*} [MetricSpace X]

theorem localSlope_sq_le_of_quadratic_bound {V : X → ℝ} (x : X)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (hC : 0 < C)
    (h : ∀ s : ℝ, 0 < s → s < C → ∀ y,
      |V x-V y| ≤ s*A/2+B*dist x y^2/(2*s)) :
    (localSlope V x).toReal^2 ≤ B*A := by
  have hqbound (q : ℝ) (hq : 0 < q) (hAq : A ≤ q) :
      (localSlope V x).toReal^2 ≤ B*q := by
    let c := Real.sqrt (B/q)
    have hc : 0 < c := Real.sqrt_pos.mpr (div_pos hB hq)
    have hc2 : c^2*q=B := by
      rw [show c^2 = B/q from Real.sq_sqrt (div_nonneg hB.le hq.le)]
      field_simp
    have hslope : localSlope V x ≤ ENNReal.ofReal (q*c) := by
      refine (iInf_le_of_le (C/c) (iInf_le_of_le (div_pos hC hc) ?_)).trans le_rfl
      apply iSup_le; intro y
      apply iSup_le; intro hy
      apply iSup_le; intro hne
      have hd : 0 < dist x y := dist_pos.mpr (Ne.symm hne)
      have hCd : c*dist x y < C := by
        have hd' := (lt_div_iff₀ hc).mp hy
        nlinarith [hd']
      have hh := h (c*dist x y) (mul_pos hc hd) hCd y
      have hm := mul_le_mul_of_nonneg_left hAq (show 0 ≤ c*dist x y/2 by positivity)
      have hid : (c*dist x y)*q/2+B*dist x y^2/(2*(c*dist x y)) = q*c*dist x y := by
        rw [← hc2]
        field_simp
        ; ring
      have ht : |V x-V y| ≤ q*c*dist x y := by linarith [hid]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ hd).mpr
      simpa only [abs_sub_comm] using ht
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hslope
    rw [ENNReal.toReal_ofReal (mul_nonneg hq.le hc.le)] at hreal
    have hh := pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 2
    have he : (q*c)^2 = B*q := by rw [← hc2]; ring
    rwa [he] at hh
  apply le_of_forall_pos_le_add
  intro ε hε
  have hq := hqbound (A+ε/B) (by positivity) (le_add_of_nonneg_right (by positivity))
  have he : B*(A+ε/B)=B*A+ε := by field_simp
  rwa [he] at hq


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem slopeAtScale_neg_eq (φ : X → ℝ) (r : ℝ) (x : X) :
    slopeAtScale (-φ) r x = slopeAtScale φ r x := by
  simp only [slopeAtScale,Pi.neg_apply,neg_sub_neg,abs_sub_comm]

theorem NoncollapsedRCD.heat_scaled_gradient_bound
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    {r : ℝ} (hr : 0 < r)
    (hH : (fun x => (slopeAtScale φ r x).toReal^2) =ᵐ[hausdorff n X] H) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ {t : ℝ}, 0 ≤ t → ∀ V : X → ℝ, Continuous V →
    (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V →
    ∀ᵐ x ∂hausdorff n X,
      (localSlope V x).toReal^2 ≤ Real.exp (-2*K*t)*heatAt (hausdorff n X) hX.quadratic t H x := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro t ht V hV heV
  let C := r/(2*((L:ℝ)+1))
  have hC : 0 < C := div_pos hr (by positivity)
  have hsmall {s : ℝ} (hs : 0 < s) (hsC : s < C) : 2*s*(L:ℝ) < r := by
    have hh := (lt_div_iff₀ (show 0 < 2*((L:ℝ)+1) by positivity)).mp hsC
    nlinarith [L.coe_nonneg]
  have hfneg : (-φ) =ᵐ[μ] (-f : Lp ℝ 2 μ) := by
    filter_upwards [hf,Lp.coeFn_neg f] with x hx hy
    simp only [hy,Pi.neg_apply,hx]
  have heVneg : (heatAt μ hX.quadratic t (-f) : X → ℝ) =ᵐ[μ] -V := by
    rw [map_neg]
    filter_upwards [heV,Lp.coeFn_neg (heatAt μ hX.quadratic t f)] with x hx hy
    simpa only [hy,Pi.neg_apply] using congrArg Neg.neg hx
  have hHneg : (fun x => (slopeAtScale (-φ) r x).toReal^2) =ᵐ[μ] H := by
    simpa only [slopeAtScale_neg_eq] using hH
  have hrat (q : ℚ) : ∀ᵐ x ∂μ, 0 < (q:ℝ) → (q:ℝ) < C → ∀ y,
      |V x-V y| ≤ (q:ℝ)/2*heatAt μ hX.quadratic t H x+
        Real.exp (-2*K*t)*dist x y^2/(2*(q:ℝ)) := by
    by_cases hq : 0 < (q:ℝ) ∧ (q:ℝ) < C
    · have hp := hX.heat_slope_quadratic_bound K n hn hφ p R hsupp f H hf hq.1
        (hsmall hq.1 hq.2) hH ht V hV heV
      have hm := hX.heat_slope_quadratic_bound K n hn hφ.neg p R
        (fun x hx => by simp only [Pi.neg_apply,hsupp x hx,neg_zero]) (-f) H hfneg hq.1
        (hsmall hq.1 hq.2) hHneg ht (-V) hV.neg heVneg
      filter_upwards [hp,hm] with x hp hm _ _ y
      apply abs_le.mpr
      constructor
      · have hh := hm y
        simp only [Pi.neg_apply] at hh
        linarith
      · exact hp y
    · exact Eventually.of_forall fun _ hq₀ hqC => False.elim (hq ⟨hq₀,hqC⟩)
  have hH0 : 0 ≤ H := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [hH] with x hx
    rw [← hx]
    exact sq_nonneg _
  have hp := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hX.quadratic t H hH0)
  filter_upwards [ae_all_iff.mpr hrat,hp] with x hx hpos
  apply localSlope_sq_le_of_quadratic_bound x hpos (Real.exp_pos _) hC
  intro s hs hsC y
  apply quadratic_bound_of_rat hs hsC
  intro q hq hqC
  have hh := hx q hq hqC y
  nlinarith [hh]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X]

theorem slopeAtScale_toReal_tendsto {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (x : X) :
    Tendsto (fun j : ℕ => (slopeAtScale φ (1/(j+1:ℝ)) x).toReal) atTop
      (𝓝 (localSlope φ x).toReal) := by
  have ha : Antitone (fun j : ℕ => slopeAtScale φ (1/(j+1:ℝ)) x) := by
    intro i j hij
    apply slopeAtScale_mono
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have ht := tendsto_atTop_iInf ha
  rw [← localSlope_eq_iInf_scale] at ht
  exact (ENNReal.continuousAt_toReal
    (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hφ x))).tendsto.comp ht

theorem localSlope_zero_outside_one {φ : X → ℝ} (p : X) (R : ℝ)
    (hsupp : ∀ x, R < dist p x → φ x = 0) {x : X} (hx : R+1 < dist p x) :
    localSlope φ x = 0 := by
  apply le_antisymm ?_ bot_le
  calc
    localSlope φ x ≤ slopeAtScale φ 1 x := iInf_le_of_le 1 (iInf_le_of_le zero_lt_one le_rfl)
    _ = 0 := slopeAtScale_zero_outside p R hsupp zero_le_one x hx

variable [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem localSlope_sq_compact_memLp {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (p : X) (R : ℝ)
    (hsupp : ∀ x, R < dist p x → φ x = 0) :
    MemLp (fun x => (localSlope φ x).toReal^2) 2 μ := by
  apply memLp_of_bounded_ball_support μ
    ((localSlope_measurable hφ.continuous).ennreal_toReal.pow_const 2) p (R+1) ((L:ℝ)^2)
  · intro x hx
    rw [localSlope_zero_outside_one p R hsupp hx]; simp
  · intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := ENNReal.toReal_mono (by simp : (L:ℝ≥0∞) ≠ ∞) (localSlope_le_of_lipschitz hφ x)
    simp only [ENNReal.coe_toReal] at h
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg h 2

theorem slopeSq_toLp_tendsto {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (p : X) (R : ℝ)
    (hsupp : ∀ x, R < dist p x → φ x = 0) :
    Tendsto (fun j : ℕ =>
      (slopeAtScale_sq_memLp μ hφ p R hsupp (by positivity : 0 ≤ 1/(j+1:ℝ))).toLp
        (fun x => (slopeAtScale φ (1/(j+1:ℝ)) x).toReal^2)) atTop
      (𝓝 ((localSlope_sq_compact_memLp μ hφ p R hsupp).toLp
        (fun x => (localSlope φ x).toReal^2))) := by
  let B := (closedBall p (R+1)).indicator (fun _ : X => 4*(L:ℝ)^4)
  have hB : Integrable B μ :=
    (integrableOn_const (isCompact_closedBall p (R+1)).measure_ne_top).integrable_indicator
      measurableSet_closedBall
  apply L2Differentiation.toLp_tendsto_of_dominated μ _ _ B hB
  · apply Eventually.of_forall
    intro j
    apply Eventually.of_forall
    intro x
    have hr : (1/(j+1:ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (j:ℝ)+1)).mpr
      norm_num
    by_cases hx : x ∈ closedBall p (R+1)
    · rw [show B x = 4*(L:ℝ)^4 from indicator_of_mem hx _]
      have hF0 : 0 ≤ (slopeAtScale φ (1/(j+1:ℝ)) x).toReal^2 := sq_nonneg _
      have hf0 : 0 ≤ (localSlope φ x).toReal^2 := sq_nonneg _
      have hF := ENNReal.toReal_mono (by simp : (L:ℝ≥0∞) ≠ ∞)
        (slopeAtScale_le_lipschitz hφ (1/(j+1:ℝ)) x)
      have hf := ENNReal.toReal_mono (by simp : (L:ℝ≥0∞) ≠ ∞)
        (localSlope_le_of_lipschitz hφ x)
      simp only [ENNReal.coe_toReal] at hF hf
      have hF2 := pow_le_pow_left₀ ENNReal.toReal_nonneg hF 2
      have hf2 := pow_le_pow_left₀ ENNReal.toReal_nonneg hf 2
      have hab : |(slopeAtScale φ (1/(j+1:ℝ)) x).toReal^2-(localSlope φ x).toReal^2| ≤
          2*(L:ℝ)^2 := abs_le.mpr ⟨by nlinarith,by nlinarith⟩
      have hh := pow_le_pow_left₀ (abs_nonneg _) hab 2
      nlinarith only [hh,sq_abs ((slopeAtScale φ (1/(j+1:ℝ)) x).toReal^2-(localSlope φ x).toReal^2)]
    · have hx' : R+1 < dist p x := by simpa only [mem_closedBall,not_le,dist_comm] using hx
      rw [slopeAtScale_zero_outside p R hsupp (by positivity) x (by linarith : R+1/(j+1:ℝ) < dist p x),
        localSlope_zero_outside_one p R hsupp hx']
      simp only [ENNReal.toReal_zero,zero_pow (by norm_num : 2 ≠ 0),sub_self]
      change 0 ≤ B x
      rw [show B x = 0 from indicator_of_notMem hx _]
  · exact Eventually.of_forall fun x => (slopeAtScale_toReal_tendsto hφ x).pow 2


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.heat_local_gradient_bound
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    (hH : (fun x => (localSlope φ x).toReal^2) =ᵐ[hausdorff n X] H) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ {t : ℝ}, 0 ≤ t → ∀ V : X → ℝ, Continuous V →
    (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V →
    ∀ᵐ x ∂hausdorff n X,
      (localSlope V x).toReal^2 ≤ Real.exp (-2*K*t)*heatAt (hausdorff n X) hX.quadratic t H x := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro t ht V hV heV
  let Hj : ℕ → Lp ℝ 2 μ := fun j =>
    (slopeAtScale_sq_memLp μ hφ p R hsupp (by positivity : 0 ≤ 1/(j+1:ℝ))).toLp
      (fun x => (slopeAtScale φ (1/(j+1:ℝ)) x).toReal^2)
  have hHeq : (localSlope_sq_compact_memLp μ hφ p R hsupp).toLp
      (fun x => (localSlope φ x).toReal^2) = H := by
    apply Lp.ext
    exact (localSlope_sq_compact_memLp μ hφ p R hsupp).coeFn_toLp.trans hH
  have hc : Tendsto Hj atTop (𝓝 H) := by
    simpa only [hHeq] using slopeSq_toLp_tendsto μ hφ p R hsupp
  have hheat : Tendsto (fun j => heatAt μ hX.quadratic t (Hj j)) atTop
      (𝓝 (heatAt μ hX.quadratic t H)) := ((heatAt μ hX.quadratic t).continuous.tendsto H).comp hc
  obtain ⟨a,ha,hseq⟩ := (tendstoInMeasure_of_tendsto_Lp hheat).exists_seq_tendsto_ae
  have hb (j : ℕ) : ∀ᵐ x ∂μ,
      (localSlope V x).toReal^2 ≤ Real.exp (-2*K*t)*heatAt μ hX.quadratic t (Hj j) x := by
    apply hX.heat_scaled_gradient_bound K n hn hφ p R hsupp f (Hj j) hf
      (by positivity : 0 < 1/(j+1:ℝ)) _ ht V hV heV
    exact (slopeAtScale_sq_memLp μ hφ p R hsupp (by positivity : 0 ≤ 1/(j+1:ℝ))).coeFn_toLp.symm
  filter_upwards [hseq,ae_all_iff.mpr hb] with x hx hxb
  exact ge_of_tendsto (hx.const_mul (Real.exp (-2*K*t)))
    (Eventually.of_forall fun j => hxb (a j))

theorem NoncollapsedRCD.heat_lipschitz_gradient_compact
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    (hH : (fun x => (localSlope φ x).toReal^2) =ᵐ[hausdorff n X] H) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ {t : ℝ}, 0 ≤ t → ∃ V : X → ℝ,
      LipschitzWith (L*⟨Real.exp (-K*t),(Real.exp_pos _).le⟩) V ∧
      (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V ∧
      ∀ᵐ x ∂hausdorff n X,
      (localSlope V x).toReal^2 ≤ Real.exp (-2*K*t)*heatAt (hausdorff n X) hX.quadratic t H x := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro t ht
  obtain ⟨V,hV,heV⟩ := hX.heat_lipschitz K n hn f hφ hf _
    (compact_lipschitz_abs_bound hφ p R hsupp) ht
  exact ⟨V,hV,heV,hX.heat_local_gradient_bound K n hn hφ p R hsupp f H hf hH ht V hV.continuous heV⟩


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem lp_weighted_square_continuous {w : X → ℝ} (hw : AEStronglyMeasurable w μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) :
    Continuous (fun f : Lp ℝ 2 μ => ∫ x, w x*(f x)^2 ∂μ) := by
  let hm := memLp_top_of_bound hw C hb
  let W := hm.toLp w
  have he (f : Lp ℝ 2 μ) : (∫ x, w x*(f x)^2 ∂μ) = inner ℝ f (lpMultiplier μ W f) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lpMultiplier_coe μ W f,hm.coeFn_toLp] with x hx hw
    change W x = w x at hw
    simp only [Real.inner_apply,hx,hw]
    ring
  simp_rw [he]
  exact continuous_id.inner (lpMultiplier μ W).continuous

variable [MetricSpace X] [BorelSpace X] [ProperSpace X]
  (hQ : QuadraticCheegerEnergy μ)

theorem SobolevSpace.minimalSlope_lipschitz :
    LipschitzWith 1 (SobolevSpace.minimalSlope μ hQ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  apply (SobolevSpace.minimalSlope_sub_norm_le μ hQ f g).trans
  have he := SobolevSpace.minimalSlope_norm_sq μ hQ (f-g)
  have hn := SobolevSpace.norm_sq μ hQ (f-g)
  dsimp [SobolevSpace.normSq] at hn
  nlinarith [norm_nonneg (SobolevSpace.minimalSlope μ hQ (f-g)),norm_nonneg (f-g),
    sq_nonneg ‖SobolevSpace.toLp μ hQ (f-g)‖]

theorem SobolevSpace.minimalSlope_le_localSlope (f : SobolevSpace μ hQ)
    {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (he : SobolevSpace.toLp μ hQ f =ᵐ[μ] g)
    (hm : MemLp (fun x => (localSlope g x).toReal) 2 μ) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ (localSlope g x).toReal := by
  let H := hm.toLp (fun x => (localSlope g x).toReal)
  have hH : IsSlopeMajorant μ g H := by
    filter_upwards [hm.coeFn_toLp] with x hx
    change 0 ≤ H x ∧ localSlope g x ≤ ENNReal.ofReal (H x)
    rw [show H x = (localSlope g x).toReal from hx]
    refine ⟨ENNReal.toReal_nonneg,?_⟩
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hg x))]
  have hrel : IsRelaxedSlope μ (SobolevSpace.toLp μ hQ f) H :=
    ⟨fun _ => SobolevSpace.toLp μ hQ f,fun _ => g,fun _ => H,fun _ => ⟨L,hg⟩,
      fun _ => he,fun _ => hH,tendsto_const_nhds,tendsto_const_nhds⟩
  filter_upwards [(Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_le μ hQ f hrel),hm.coeFn_toLp] with x hx hy
  exact hx.trans_eq hy


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.heat_compact_weighted_gradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (f G w : Lp ℝ 2 (hausdorff n X))
    (hf : φ =ᵐ[hausdorff n X] f) (hG : IsSlopeMajorant (hausdorff n X) φ G)
    (hw : 0 ≤ w) (C : ℝ≥0) (hwC : ∀ᵐ x ∂hausdorff n X, |w x| ≤ C) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ {t : ℝ} (ht : 0 < t),
      (∫ x, w x*(SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht f) x)^2 ∂hausdorff n X) ≤
      Real.exp (-2*K*t)*(∫ x, heatAt (hausdorff n X) hX.quadratic t w x*(G x)^2 ∂hausdorff n X) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro t ht
  obtain ⟨R,hR⟩ := hs.isCompact.isBounded.subset_closedBall p
  have hsupp (x : X) (hx : R < dist p x) : φ x = 0 := by
    by_contra hh
    have h := hR (subset_tsupport φ hh)
    simp only [mem_closedBall,dist_comm] at h
    linarith
  let hm := localSlope_sq_compact_memLp μ hφ p R hsupp
  let H := hm.toLp (fun x => (localSlope φ x).toReal^2)
  have hH : ⇑H =ᵐ[μ] fun x => (localSlope φ x).toReal^2 := hm.coeFn_toLp
  have hHi : Integrable H μ :=
    (localSlope_toReal_memLp μ hφ (slopeEnergy_lt_top_of_lipschitz_hasCompactSupport μ hφ hs).ne).integrable_sq.congr hH.symm
  obtain ⟨V,hV,heV,hgrad⟩ := hX.heat_lipschitz_gradient_compact K n hn hφ p R hsupp f H hf hH.symm ht.le
  have hPH := heatAt_integrable μ hX.quadratic t H hHi
  have hVsq : Integrable (fun x => (localSlope V x).toReal^2) μ := by
    apply (hPH.const_mul (Real.exp (-2*K*t))).mono'
      ((localSlope_measurable hV.continuous).ennreal_toReal.pow_const 2).aestronglyMeasurable
    filter_upwards [hgrad] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ((localSlope V x).toReal))] using hx
  have hVm : MemLp (fun x => (localSlope V x).toReal) 2 μ :=
    (memLp_two_iff_integrable_sq ((localSlope_measurable hV.continuous).ennreal_toReal.aestronglyMeasurable)).mpr hVsq
  let S := SobolevSpace.minimalSlope μ hX.quadratic (heatSobolev μ hX.quadratic t ht f)
  have hSle := SobolevSpace.minimalSlope_le_localSlope μ hX.quadratic
    (heatSobolev μ hX.quadratic t ht f) hV heV hVm
  have hS0 := (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic
    (heatSobolev μ hX.quadratic t ht f))
  have hw0 := (Lp.coeFn_nonneg _).mpr hw
  have hwb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C:ℝ) := by simpa only [Real.norm_eq_abs] using hwC
  have hPwb : ∀ᵐ x ∂μ, ‖heatAt μ hX.quadratic t w x‖ ≤ (C:ℝ) := by
    simpa only [Real.norm_eq_abs] using heatAt_abs_le_const μ hX.quadratic t C w hwC
  have hPw0 := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hX.quadratic t w hw)
  have hpair : (∫ x, w x*heatAt μ hX.quadratic t H x ∂μ) =
      ∫ x, heatAt μ hX.quadratic t w x*(localSlope φ x).toReal^2 ∂μ := by
    have he := heatAt_inner μ hX.quadratic t w H
    simp only [L2.inner_def,Real.inner_apply] at he
    rw [← he]
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    rw [hx]
  calc
    (∫ x, w x*(S x)^2 ∂μ) ≤ ∫ x, w x*(Real.exp (-2*K*t)*heatAt μ hX.quadratic t H x) ∂μ := by
      apply integral_mono_ae ((Lp.memLp S).integrable_sq.bdd_mul (Lp.aestronglyMeasurable w) hwb)
        ((hPH.const_mul _).bdd_mul (Lp.aestronglyMeasurable w) hwb)
      filter_upwards [hw0,hS0,hSle,hgrad] with x hw hs hsle hg
      apply mul_le_mul_of_nonneg_left _ hw
      exact (pow_le_pow_left₀ hs hsle 2).trans hg
    _ = Real.exp (-2*K*t)*(∫ x, heatAt μ hX.quadratic t w x*(localSlope φ x).toReal^2 ∂μ) := by
      simp_rw [mul_left_comm (w _) (Real.exp (-2*K*t))]
      rw [integral_const_mul,hpair]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply integral_mono_ae
        (((localSlope_toReal_memLp μ hφ (slopeEnergy_lt_top_of_lipschitz_hasCompactSupport μ hφ hs).ne).integrable_sq).bdd_mul
          (Lp.aestronglyMeasurable _) hPwb)
        ((Lp.memLp G).integrable_sq.bdd_mul (Lp.aestronglyMeasurable _) hPwb)
      filter_upwards [hPw0,hG] with x hw hG
      apply mul_le_mul_of_nonneg_left _ hw
      apply pow_le_pow_left₀ ENNReal.toReal_nonneg _ 2
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hG.2
      simpa only [ENNReal.toReal_ofReal hG.1] using hh


end

 
section

 

open Set Metric Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X)

theorem IsSlopeMajorant.compact_approximation {g : X → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (u G : Lp ℝ 2 μ) (hu : ⇑u =ᵐ[μ] g)
    (hG : IsSlopeMajorant μ g G) (p : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (v H : Lp ℝ 2 μ) (k : X → ℝ),
      (∃ L : ℝ≥0, LipschitzWith L k) ∧ HasCompactSupport k ∧
      ⇑v =ᵐ[μ] k ∧ IsSlopeMajorant μ k H ∧ dist v u < ε ∧ dist H G < ε := by
  let R : ℕ → ℝ := fun i => (i:ℝ)+1
  have hR (i : ℕ) : 0 < R i := by dsimp [R]; positivity
  have hRL : Tendsto R atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  let θ := fun i => radialCutoff p (R i)
  have hθm (i : ℕ) : Measurable (θ i) := (radialCutoff_lipschitz p (hR i)).continuous.measurable
  have hθb (i : ℕ) (x : X) : |θ i x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_bounds p (R i) x).1]
    exact (radialCutoff_bounds p (R i) x).2
  let Θ := fun i => boundedMultiplier μ (θ i) (hθm i) 1 (hθb i)
  have hΘ (i : ℕ) : ⇑(Θ i) =ᵐ[μ] θ i := boundedMultiplier_coe μ _ _ _ _
  let vs := fun i => lpMultiplier μ (Θ i) u
  let Hs := fun i => lpMultiplier μ (Θ i) G+(R i)⁻¹ • lpAbs μ u
  let ks := fun i x => θ i x*g x
  have hla (i : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (ks i) :=
    lipschitz_mul_compact_cutoff (radialCutoff_lipschitz p (hR i)) hg
      (radialCutoff_hasCompactSupport p (hR i)) (hθb i)
  have hks (i : ℕ) : HasCompactSupport (ks i) :=
    (radialCutoff_hasCompactSupport p (hR i)).mul_right
  have hae (i : ℕ) : ⇑(vs i) =ᵐ[μ] ks i := by
    filter_upwards [lpMultiplier_coe μ (Θ i) u,hu,hΘ i] with x hx he hθ
    exact hx.trans (by rw [he,hθ])
  have hmaj (i : ℕ) : IsSlopeMajorant μ (ks i) (Hs i) := by
    filter_upwards [Lp.coeFn_add (lpMultiplier μ (Θ i) G) ((R i)⁻¹ • lpAbs μ u),
      lpMultiplier_coe μ (Θ i) G,Lp.coeFn_smul ((R i)⁻¹) (lpAbs μ u),
      lpAbs_coe μ u,hu,hG,hΘ i] with x ha hm hs habs hu hG hθ
    have he : Hs i x = θ i x*G x+(R i)⁻¹*|g x| := by
      change (lpMultiplier μ (Θ i) G+(R i)⁻¹ • lpAbs μ u) x = _
      simp only [ha,hm,hs,habs,hu,hθ,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    change 0 ≤ Hs i x ∧ localSlope (ks i) x ≤ ENNReal.ofReal (Hs i x)
    rw [he]
    have hθn := (radialCutoff_bounds p (R i) x).1
    have hc : 0 ≤ (R i)⁻¹ := inv_nonneg.mpr (hR i).le
    refine ⟨add_nonneg (mul_nonneg hθn hG.1) (mul_nonneg hc (abs_nonneg _)),?_⟩
    calc
      _ ≤ ENNReal.ofReal |θ i x| *localSlope g x + ENNReal.ofReal |g x| *localSlope (θ i) x :=
        localSlope_mul_le (radialCutoff_lipschitz p (hR i)).continuous.continuousAt
          (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hg x))
      _ ≤ ENNReal.ofReal (θ i x)*ENNReal.ofReal (G x)+
          ENNReal.ofReal |g x| *ENNReal.ofReal ((R i)⁻¹) := by
        rw [abs_of_nonneg hθn]
        apply add_le_add (mul_le_mul' le_rfl hG.2) (mul_le_mul' le_rfl ?_)
        exact (localSlope_le_of_lipschitz (radialCutoff_lipschitz p (hR i)) x).trans_eq
          (ENNReal.coe_nnreal_eq _)
      _ = _ := by
        rw [← ENNReal.ofReal_mul hθn,← ENNReal.ofReal_mul (abs_nonneg _),
          ← ENNReal.ofReal_add (mul_nonneg hθn hG.1) (mul_nonneg (abs_nonneg _) hc)]
        congr 1
        ring
  have hθL (x : X) : Tendsto (fun i => θ i x) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hRL.eventually (radialCutoff_eventually_one p x)] with i hi
    exact hi.symm
  have hmul (v : Lp ℝ 2 μ) : Tendsto (fun i => lpMultiplier μ (Θ i) v) atTop (𝓝 v) := by
    have hh := lpMultiplier_tendsto_of_ae μ v θ (fun _ => 1) hθm measurable_const 1 hθb
      (fun _ => by norm_num) (Eventually.of_forall hθL)
    have he : lpMultiplier μ (boundedMultiplier μ (fun _ : X => 1) measurable_const 1 (fun _ => by norm_num)) v = v := by
      apply Lp.ext
      filter_upwards [lpMultiplier_coe μ (boundedMultiplier μ (fun _ : X => 1) measurable_const 1 (fun _ => by norm_num)) v,
        boundedMultiplier_coe μ (fun _ : X => 1) measurable_const 1 (fun _ => by norm_num)] with x hx he
      simpa only [he,one_mul] using hx
    simpa only [he] using hh
  have hvL : Tendsto vs atTop (𝓝 u) := hmul u
  have hcL : Tendsto (fun i => (R i)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hRL
  have hHL : Tendsto Hs atTop (𝓝 G) := by
    simpa only [Hs,zero_smul,add_zero] using (hmul G).add (hcL.smul_const (lpAbs μ u))
  obtain ⟨i,hi,hj⟩ := ((hvL.eventually (Metric.ball_mem_nhds u hε)).and
    (hHL.eventually (Metric.ball_mem_nhds G hε))).exists
  exact ⟨vs i,Hs i,ks i,hla i,hks i,hae i,hmaj i,hi,hj⟩

theorem IsRelaxedSlope.compact_recovery {f G : Lp ℝ 2 μ}
    (hG : IsRelaxedSlope μ f G) (p : X) :
    ∃ (us : ℕ → Lp ℝ 2 μ) (gs : ℕ → X → ℝ) (Gs : ℕ → Lp ℝ 2 μ),
      (∀ i, ∃ C : ℝ≥0, LipschitzWith C (gs i)) ∧
      (∀ i, HasCompactSupport (gs i)) ∧ (∀ i, ⇑(us i) =ᵐ[μ] gs i) ∧
      (∀ i, IsSlopeMajorant μ (gs i) (Gs i)) ∧
      Tendsto us atTop (𝓝 f) ∧ Tendsto Gs atTop (𝓝 G) := by
  obtain ⟨us,gs,Gs,hl,ha,hm,hu,hc⟩ := hG
  have he (i : ℕ) := (hm i).compact_approximation μ (hl i).choose_spec (us i) (Gs i) (ha i) p
    (by positivity : 0 < 1/(i+1:ℝ))
  choose vs Hs ks hkl hks hka hkm hv hH using he
  refine ⟨vs,ks,Hs,hkl,hks,hka,hkm,?_,?_⟩
  · apply tendsto_of_tendsto_of_dist hu
    apply squeeze_zero (fun _ => dist_nonneg) (fun i => (show dist (us i) (vs i) ≤ 1/(i+1:ℝ) by simpa only [dist_comm] using (hv i).le))
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · apply tendsto_of_tendsto_of_dist hc
    apply squeeze_zero (fun _ => dist_nonneg) (fun i => (show dist (Gs i) (Hs i) ≤ 1/(i+1:ℝ) by simpa only [dist_comm] using (hH i).le))
    exact tendsto_one_div_add_atTop_nhds_zero_nat


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.heat_weighted_gradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) (f : SobolevSpace (hausdorff n X) hX.quadratic)
    (w : Lp ℝ 2 (hausdorff n X)) (hw : 0 ≤ w) (C : ℝ≥0)
    (hwC : ∀ᵐ x ∂hausdorff n X, |w x| ≤ C) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ {t : ℝ} (ht : 0 < t),
      (∫ x, w x*(SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic f)) x)^2 ∂hausdorff n X) ≤
      Real.exp (-2*K*t)*(∫ x, heatAt (hausdorff n X) hX.quadratic t w x*
        (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic f x)^2 ∂hausdorff n X) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro t ht
  obtain ⟨us,gs,Gs,hl,hs,ha,hm,hu,hG⟩ :=
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic f).compact_recovery μ p
  have hab (i : ℕ) := hX.heat_compact_weighted_gradient K n hn
    (hl i).choose_spec (hs i) p (us i) (Gs i) w (ha i).symm (hm i) hw C hwC ht
  have hsf : Tendsto (fun i => heatSobolev μ hX.quadratic t ht (us i)) atTop
      (𝓝 (heatSobolev μ hX.quadratic t ht (SobolevSpace.toLp μ hX.quadratic f))) :=
    ((heatSobolevMap μ hX.quadratic t ht).continuous.tendsto _).comp hu
  have hsl := ((SobolevSpace.minimalSlope_lipschitz μ hX.quadratic).continuous.tendsto _).comp hsf
  have hwb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C:ℝ) := by simpa only [Real.norm_eq_abs] using hwC
  have hPwb : ∀ᵐ x ∂μ, ‖heatAt μ hX.quadratic t w x‖ ≤ (C:ℝ) := by
    simpa only [Real.norm_eq_abs] using heatAt_abs_le_const μ hX.quadratic t C w hwC
  have hleft := ((lp_weighted_square_continuous μ (Lp.aestronglyMeasurable w) hwb).tendsto _).comp hsl
  have hright := (((lp_weighted_square_continuous μ (Lp.aestronglyMeasurable
    (heatAt μ hX.quadratic t w)) hPwb).tendsto _).comp hG).const_mul (Real.exp (-2*K*t))
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hab)


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

noncomputable def weightedGamma (w : X → ℝ) (f g : SobolevSpace μ hQ) : ℝ :=
  ∫ x, w x*localGamma μ hQ f g x ∂μ

omit [ProperSpace X] in
theorem weightedGamma_comm (w : X → ℝ) (f g : SobolevSpace μ hQ) :
    weightedGamma μ hQ w f g = weightedGamma μ hQ w g f := by
  apply integral_congr_ae
  filter_upwards [localGamma_comm μ hQ f g] with x hx
  rw [hx]

omit [ProperSpace X] in
theorem weightedGamma_self (w : X → ℝ) (f : SobolevSpace μ hQ) :
    weightedGamma μ hQ w f f = ∫ x, w x*(SobolevSpace.minimalSlope μ hQ f x)^2 ∂μ := by
  apply integral_congr_ae
  filter_upwards [localGamma_self μ hQ f] with x hx
  rw [hx]

variable {w : X → ℝ} (hw : AEStronglyMeasurable w μ) {C : ℝ≥0}
  (hb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C:ℝ))

include hw hb in
theorem weightedGamma_add_left (f g h : SobolevSpace μ hQ) :
    weightedGamma μ hQ w (f+g) h = weightedGamma μ hQ w f h+weightedGamma μ hQ w g h := by
  unfold weightedGamma
  rw [← integral_add ((localGamma_memL1 μ hQ f h).bdd_mul hw hb)
    ((localGamma_memL1 μ hQ g h).bdd_mul hw hb)]
  apply integral_congr_ae
  filter_upwards [localGamma_add_left μ hQ f g h] with x hx
  rw [hx,mul_add]

theorem weightedGamma_smul_left (c : ℝ) (f g : SobolevSpace μ hQ) :
    weightedGamma μ hQ w (c • f) g = c*weightedGamma μ hQ w f g := by
  unfold weightedGamma
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [localGamma_smul_left μ hQ c f g] with x hx
  rw [hx]
  ring

omit [ProperSpace X] in
theorem SobolevSpace.minimalSlope_norm_le (f : SobolevSpace μ hQ) :
    ‖SobolevSpace.minimalSlope μ hQ f‖ ≤ ‖f‖ := by
  have he := SobolevSpace.minimalSlope_norm_sq μ hQ f
  have hn := SobolevSpace.norm_sq μ hQ f
  dsimp [SobolevSpace.normSq] at hn
  nlinarith [norm_nonneg (SobolevSpace.minimalSlope μ hQ f),norm_nonneg f,
    sq_nonneg ‖SobolevSpace.toLp μ hQ f‖]

include hb in
theorem weightedGamma_norm_le (f g : SobolevSpace μ hQ) :
    ‖weightedGamma μ hQ w f g‖ ≤ C*‖f‖*‖g‖ := by
  let G := SobolevSpace.minimalSlope μ hQ f
  let H := SobolevSpace.minimalSlope μ hQ g
  have hi : Integrable (fun x => G x*H x) μ := (Lp.memLp G).integrable_mul (Lp.memLp H)
  have he : (∫ x, G x*H x ∂μ) = inner ℝ G H := by
    simp only [L2.inner_def,Real.inner_apply]
  calc
    ‖weightedGamma μ hQ w f g‖ ≤ ∫ x, (C:ℝ)*(G x*H x) ∂μ := by
      apply norm_integral_le_of_norm_le (hi.const_mul _)
      filter_upwards [hb,localGamma_abs_le μ hQ f g] with x hw hG
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hG C.coe_nonneg)
    _ = C*(∫ x, G x*H x ∂μ) := integral_const_mul _ _
    _ ≤ C*(‖G‖*‖H‖) := by
      rw [he]
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) G H)) C.coe_nonneg
    _ ≤ C*‖f‖*‖g‖ := by
      have hf := SobolevSpace.minimalSlope_norm_le μ hQ f
      have hg := SobolevSpace.minimalSlope_norm_le μ hQ g
      calc
        _ ≤ C*(‖f‖*‖g‖) := mul_le_mul_of_nonneg_left
          (mul_le_mul hf hg (norm_nonneg H) (norm_nonneg f)) C.coe_nonneg
        _ = _ := by ring

noncomputable def weightedGammaCLM : SobolevSpace μ hQ →L[ℝ] SobolevSpace μ hQ →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ (weightedGamma μ hQ w)
    (weightedGamma_add_left μ hQ hw hb)
    (fun c f g => weightedGamma_smul_left μ hQ c f g)
    (fun f g h => by
      rw [weightedGamma_comm μ hQ w f (g+h),weightedGamma_add_left μ hQ hw hb,
        weightedGamma_comm μ hQ w g f,weightedGamma_comm μ hQ w h f])
    (fun c f g => by
      rw [weightedGamma_comm μ hQ w f (c • g),weightedGamma_smul_left μ hQ,
        weightedGamma_comm μ hQ w g f]
      rfl)).mkContinuous₂ C (weightedGamma_norm_le μ hQ hb)

include hw hb in
theorem weighted_gradient_hasDerivAt {f : ℝ → SobolevSpace μ hQ}
    {t : ℝ} {v : SobolevSpace μ hQ} (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => ∫ x, w x*(SobolevSpace.minimalSlope μ hQ (f s) x)^2 ∂μ)
      (2*weightedGamma μ hQ w (f t) v) t := by
  have hd := ContinuousLinearMap.hasDerivAt_of_bilinear
    (B := weightedGammaCLM μ hQ hw hb) (fun _ => hf) (fun _ => hf)
  change HasDerivAt (fun s => weightedGamma μ hQ w (f s) (f s))
    (weightedGamma μ hQ w (f t) v+weightedGamma μ hQ w v (f t)) t at hd
  simp only [weightedGamma_self] at hd
  rw [weightedGamma_comm μ hQ w v (f t)] at hd
  convert hd using 1 ; ring


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.heat_weak_bochner
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) (f w : Lp ℝ 2 (hausdorff n X))
    (hw : 0 ≤ w) (C : ℝ≥0) (hwC : ∀ᵐ x ∂hausdorff n X, |w x| ≤ C)
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    let F := heatSobolev μ hX.quadratic t ht f
    let D := heatSobolevMap μ hX.quadratic (t/2) (half_pos ht)
      (-heatGeneratorAt μ hX.quadratic (t-t/2) f)
    ∀ (H : Lp ℝ 2 μ), (fun x => (SobolevSpace.minimalSlope μ hX.quadratic F x)^2) =ᵐ[μ] H →
      K*(∫ x, heatAt μ hX.quadratic s w x*(SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ)
        +weightedGamma μ hX.quadratic (heatAt μ hX.quadratic s w) F D ≤
      (1/2:ℝ)*(∫ x, (-heatGeneratorAt μ hX.quadratic s w) x*H x ∂μ) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let F := heatSobolev μ hX.quadratic t ht f
  let D := heatSobolevMap μ hX.quadratic (t/2) (half_pos ht)
    (-heatGeneratorAt μ hX.quadratic (t-t/2) f)
  dsimp only
  intro H hH
  change (fun x => (SobolevSpace.minimalSlope μ hX.quadratic F x)^2) =ᵐ[μ] H at hH
  let W := heatAt μ hX.quadratic s w
  have hW : 0 ≤ W := heatAt_nonneg μ hX.quadratic s w hw
  have hWC : ∀ᵐ x ∂μ, |W x| ≤ C := heatAt_abs_le_const μ hX.quadratic s C w hwC
  have hWb : ∀ᵐ x ∂μ, ‖W x‖ ≤ (C:ℝ) := by simpa only [Real.norm_eq_abs] using hWC
  let q (r : ℝ) := ∫ x, W x*(SobolevSpace.minimalSlope μ hX.quadratic
    (heatTail μ hX.quadratic (t/2) (half_pos ht) f (t+r)) x)^2 ∂μ
  let b (r : ℝ) := Real.exp (-2*K*r)*inner ℝ (heatAt μ hX.quadratic (s+r) w) H
  have hF : heatTail μ hX.quadratic (t/2) (half_pos ht) f t = F :=
    heatTail_eq μ hX.quadratic (t/2) (half_pos ht) f t (by linarith)
  have hq : HasDerivAt q (2*weightedGamma μ hX.quadratic W F D) 0 := by
    have hd0 : HasDerivAt (heatTail μ hX.quadratic (t/2) (half_pos ht) f) D (t+0) := by
      simpa only [add_zero] using heatTail_hasDerivAt μ hX.quadratic (t/2) (half_pos ht) f t (by linarith)
    have hd := hd0.scomp 0 ((hasDerivAt_id (0:ℝ)).const_add t)
    simp only [one_smul] at hd
    have hh := weighted_gradient_hasDerivAt μ hX.quadratic (Lp.aestronglyMeasurable W) hWb hd
    simpa only [Function.comp_apply,add_zero,hF] using hh
  have hb : HasDerivAt b
      ((-2*K)*inner ℝ W H+inner ℝ (-heatGeneratorAt μ hX.quadratic s w) H) 0 := by
    have hd0 : HasDerivAt (fun r => heatAt μ hX.quadratic r w)
        (-heatGeneratorAt μ hX.quadratic s w) (s+0) := by
      simpa only [add_zero] using heatAt_hasDerivAt μ hX.quadratic s hs w
    have hd := hd0.scomp 0 ((hasDerivAt_id (0:ℝ)).const_add s)
    simp only [one_smul] at hd
    have he := ((hasDerivAt_id (0:ℝ)).const_mul (-2*K)).exp
    convert! he.mul (hd.inner ℝ (hasDerivAt_const (0:ℝ) H)) using 1 ;
      simp only [W,Function.comp_apply,id_eq,mul_zero,Real.exp_zero,one_mul,mul_one,add_zero,inner_zero_right,zero_add]
  have hq0 : q 0 = inner ℝ W H := by
    dsimp only [q]
    rw [add_zero,hF,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    simp only [Real.inner_apply,hx]
  have hb0 : b 0 = inner ℝ W H := by simp only [b,mul_zero,Real.exp_zero,one_mul,add_zero]; rfl
  have hab (r : ℝ) (hr : 0 < r) : q r ≤ b r := by
    have hh := hX.heat_weighted_gradient K n hn p F W hW C hWC hr
    have heF : heatSobolev μ hX.quadratic r hr (SobolevSpace.toLp μ hX.quadratic F) =
        heatTail μ hX.quadratic (t/2) (half_pos ht) f (t+r) := by
      apply Subtype.ext
      change SobolevSpace.toLp μ hX.quadratic (heatSobolev μ hX.quadratic r hr (SobolevSpace.toLp μ hX.quadratic F)) =
        SobolevSpace.toLp μ hX.quadratic (heatTail μ hX.quadratic (t/2) (half_pos ht) f (t+r))
      rw [heatSobolev_toLp,heatTail_toLp μ hX.quadratic (t/2) (half_pos ht) f (t+r) (by linarith)]
      dsimp only [F]
      rw [heatSobolev_toLp,←mul_apply_eq_comp,←heatAt_add μ hX.quadratic r t hr.le ht.le,add_comm r t]
    have heW : heatAt μ hX.quadratic r W = heatAt μ hX.quadratic (s+r) w := by
      dsimp only [W]
      rw [←mul_apply_eq_comp,←heatAt_add μ hX.quadratic r s hr.le hs.le,add_comm r s]
    rw [heF,heW] at hh
    change q r ≤ Real.exp (-2*K*r)*(∫ x, heatAt μ hX.quadratic (s+r) w x*
      (SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ) at hh
    convert hh using 1
    dsimp only [b]
    congr 1
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    simp only [Real.inner_apply,hx]
  have hder : 2*weightedGamma μ hX.quadratic W F D ≤
      (-2*K)*inner ℝ W H+inner ℝ (-heatGeneratorAt μ hX.quadratic s w) H := by
    apply le_of_tendsto_of_tendsto hq.tendsto_slope_zero_right hb.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    simp only [zero_add,smul_eq_mul,hq0,hb0]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hab r hr) _) (inv_nonneg.mpr hr.le)
  have he : (∫ x, W x*(SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ) = inner ℝ W H := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    simp only [Real.inner_apply,hx]
  change K*(∫ x, W x*(SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ)+
    weightedGamma μ hX.quadratic W F D ≤ _
  rw [he]
  have he' : (∫ x, (-heatGeneratorAt μ hX.quadratic s w) x*H x ∂μ) =
      inner ℝ (-heatGeneratorAt μ hX.quadratic s w) H := by simp only [L2.inner_def,Real.inner_apply]
  rw [he']
  linarith



 
theorem NoncollapsedRCD.heat_compact_slope_bdd
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (f : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    (t : ℝ) (ht : 0 < t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ᵐ x ∂hausdorff n X,
      SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht f) x ≤ (L:ℝ)*Real.exp (-K*t) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨R,hR⟩ := hs.isCompact.isBounded.subset_closedBall p
  have hsupp (x : X) (hx : R < dist p x) : φ x = 0 := by
    by_contra hh
    have h := hR (subset_tsupport φ hh)
    simp only [mem_closedBall,dist_comm] at h
    linarith
  let hm := localSlope_sq_compact_memLp μ hφ p R hsupp
  let H := hm.toLp (fun x => (localSlope φ x).toReal^2)
  have hH : ⇑H =ᵐ[μ] fun x => (localSlope φ x).toReal^2 := hm.coeFn_toLp
  have hHi : Integrable H μ :=
    (localSlope_toReal_memLp μ hφ (slopeEnergy_lt_top_of_lipschitz_hasCompactSupport μ hφ hs).ne).integrable_sq.congr hH.symm
  obtain ⟨V,hV,heV,hgrad⟩ := hX.heat_lipschitz_gradient_compact K n hn hφ p R hsupp f H hf hH.symm ht.le
  have hPH := heatAt_integrable μ hX.quadratic t H hHi
  have hVsq : Integrable (fun x => (localSlope V x).toReal^2) μ := by
    apply (hPH.const_mul (Real.exp (-2*K*t))).mono'
      ((localSlope_measurable hV.continuous).ennreal_toReal.pow_const 2).aestronglyMeasurable
    filter_upwards [hgrad] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ((localSlope V x).toReal))] using hx
  have hVm : MemLp (fun x => (localSlope V x).toReal) 2 μ :=
    (memLp_two_iff_integrable_sq ((localSlope_measurable hV.continuous).ennreal_toReal.aestronglyMeasurable)).mpr hVsq
  have hSle := SobolevSpace.minimalSlope_le_localSlope μ hX.quadratic
    (heatSobolev μ hX.quadratic t ht f) hV heV hVm
  filter_upwards [hSle] with x hx
  apply hx.trans
  have hb := ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_of_lipschitz hV x)
  simp only [ENNReal.coe_toReal] at hb
  exact hb

theorem NoncollapsedRCD.heat_compact_gamma_memLp
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (f : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    (t : ℝ) (ht : 0 < t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    MemLp (fun x => (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht f) x)^2) 2 (hausdorff n X) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let G := SobolevSpace.minimalSlope μ hX.quadratic (heatSobolev μ hX.quadratic t ht f)
  have hGb := hX.heat_compact_slope_bdd K n hn hφ hs p f hf t ht
  have hG0 := (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic
      (heatSobolev μ hX.quadratic t ht f))
  have hGi : MemLp (fun x => G x) ∞ μ := by
    apply memLp_top_of_bound (Lp.aestronglyMeasurable G) ((L:ℝ)*Real.exp (-K*t))
    filter_upwards [hGb,hG0] with x hx h0
    change 0 ≤ G x at h0
    rw [Real.norm_eq_abs,abs_of_nonneg h0]
    exact hx
  change MemLp (fun x => (G x)^2) 2 μ
  convert! (Lp.memLp G).mul (r := (2:ℝ≥0∞)) hGi using 1
  ext x
  simp only [pow_two,Pi.mul_apply]



 
theorem heatTail_weak_laplacian [ProperSpace X] [SeparableSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ]
    (hQ : QuadraticCheegerEnergy μ) (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    IsWeakLaplacian μ hQ (heatSobolev μ hQ t ht f)
      (SobolevSpace.toLp μ hQ (heatSobolevMap μ hQ (t/2) (half_pos ht)
        (-heatGeneratorAt μ hQ (t-t/2) f))) := by
  rw [heatTail_deriv_toLp μ hQ (t/2) (half_pos ht) f t (by linarith),
    heatGeneratorAt_of_pos μ hQ t ht]
  exact heatSobolev_weak_laplacian μ hQ t ht f

theorem NoncollapsedRCD.heat_compact_weak_bochner
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (f w : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    (hw : 0 ≤ w) (C : ℝ≥0) (hwC : ∀ᵐ x ∂hausdorff n X, |w x| ≤ C)
    (t s : ℝ) (ht : 0 < t) (hs' : 0 < s) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    let F := heatSobolev μ hX.quadratic t ht f
    let D := heatSobolevMap μ hX.quadratic (t/2) (half_pos ht)
      (-heatGeneratorAt μ hX.quadratic (t-t/2) f)
    IsWeakLaplacian μ hX.quadratic F (SobolevSpace.toLp μ hX.quadratic D) ∧
      K*(∫ x, heatAt μ hX.quadratic s w x*(SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ)
        +weightedGamma μ hX.quadratic (heatAt μ hX.quadratic s w) F D ≤
      (1/2:ℝ)*(∫ x, (-heatGeneratorAt μ hX.quadratic s w) x*
        (SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let F := heatSobolev μ hX.quadratic t ht f
  let hm := hX.heat_compact_gamma_memLp K n hn hφ hs p f hf t ht
  let H := hm.toLp (fun x => (SobolevSpace.minimalSlope μ hX.quadratic F x)^2)
  have hH : (fun x => (SobolevSpace.minimalSlope μ hX.quadratic F x)^2) =ᵐ[μ] H := hm.coeFn_toLp.symm
  refine ⟨heatTail_weak_laplacian μ hX.quadratic t ht f,?_⟩
  have hh := hX.heat_weak_bochner K n hn p f w hw C hwC t s ht hs' H hH
  convert hh using 2
  apply integral_congr_ae
  filter_upwards [hH] with x hx
  rw [hx]


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] [μ.Regular] in
theorem weakLaplacian_resolvent_core (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ u d) :
    SobolevSpace.toLp μ hQ u = resolventLp μ hQ 1 zero_lt_one (SobolevSpace.toLp μ hQ u-d) := by
  have he : u = SobolevSpace.resolventAt μ hQ 1 zero_lt_one (SobolevSpace.toLp μ hQ u-d) := by
    apply SobolevSpace.resolventAt_unique μ hQ zero_lt_one
    intro φ
    rw [hd φ,inner_sub_left,one_mul]
    ring
  exact congrArg (SobolevSpace.toLp μ hQ) he

theorem heat_weakLaplacian_hasDerivAt (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ u d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => heatAt μ hQ s (SobolevSpace.toLp μ hQ u)) (heatAt μ hQ t d) t := by
  have he := weakLaplacian_resolvent_core μ hQ u d hd
  have hh := heatAt_core_hasDerivAt μ hQ t ht (SobolevSpace.toLp μ hQ u-d)
  rw [←he] at hh
  simpa only [sub_sub_cancel_left,map_neg,neg_neg] using hh


end

 
section

 

open Set Filter
open scoped Topology

 theorem abs_at_zero_of_exp_deriv_bound {q dq : ℝ → ℝ} {A a : ℝ}
    (hc : ContinuousOn q (Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt q (dq t) t)
    (ha : 0 < a) (hb : ∀ t, 0 < t → |dq t| ≤ A*Real.exp (-a*t))
    (hlim : Tendsto q atTop (𝓝 0)) : |q 0| ≤ A/a := by
  have hec : Continuous (fun t : ℝ => (A/a)*Real.exp (-a*t)) := by fun_prop
  have hed (t : ℝ) : HasDerivAt (fun t => (A/a)*Real.exp (-a*t))
      (-(A*Real.exp (-a*t))) t := by
    convert! (((hasDerivAt_id t).const_mul (-a)).exp).const_mul (A/a) using 1 ;
      simp only [mul_one,id_eq] ; field_simp
  have hp := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
    (hc.sub hec.continuousOn) (f' := fun t => dq t+A*Real.exp (-a*t))
    (by
      intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici,mem_Ioi] using ht
      convert! ((hd t ht').sub (hed t)).hasDerivWithinAt using 1 ; simp)
    (by
      intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici,mem_Ioi] using ht
      linarith [(abs_le.mp (hb t ht')).1])
  have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0:ℝ))
    (hc.add hec.continuousOn) (f' := fun t => dq t-A*Real.exp (-a*t))
    (by
      intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici,mem_Ioi] using ht
      convert! ((hd t ht').add (hed t)).hasDerivWithinAt using 1)
    (by
      intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici,mem_Ioi] using ht
      linarith [(abs_le.mp (hb t ht')).2])
  have hel : Tendsto (fun t : ℝ => (A/a)*Real.exp (-a*t)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply,id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha))).const_mul (A/a)
  have hp0 : q 0-A/a ≤ 0 := by
    apply ge_of_tendsto (by simpa only [sub_zero] using hlim.sub hel)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    simpa only [Pi.sub_apply,mul_zero,Real.exp_zero,mul_one] using hp (mem_Ici.mpr le_rfl) ht ht
  have hm0 : 0 ≤ q 0+A/a := by
    apply le_of_tendsto (by simpa only [add_zero] using hlim.add hel)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    simpa only [Pi.add_apply,mul_zero,Real.exp_zero,mul_one] using hm (mem_Ici.mpr le_rfl) ht ht
  exact abs_le.mpr ⟨by linarith,by linarith⟩


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem resolvent_pair_bound_of_heat (f a : Lp ℝ 2 μ) (t : ℝ) (ht : 0 < t)
    (K B : ℝ) (hKt : 0 < 1+K*t)
    (hheat : ∀ s, 0 < s → |inner ℝ a (heatAt μ hQ s f)| ≤ B*Real.exp (-K*s)) :
    |inner ℝ a (resolventLp μ hQ t ht f)| ≤ B/(1+K*t) := by
  let u := SobolevSpace.resolventAt μ hQ t ht f
  let g := SobolevSpace.toLp μ hQ u
  let q (s : ℝ) := Real.exp (-s/t)*inner ℝ a (heatAt μ hQ s g)
  let dq (s : ℝ) := -(t⁻¹*Real.exp (-s/t)*inner ℝ a (heatAt μ hQ s f))
  have hα : 0 < 1/t+K := by nlinarith [div_mul_cancel₀ (1:ℝ) ht.ne']
  have hcont : ContinuousOn q (Ici 0) :=
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (-s/t))).mul
      (continuous_const.inner (𝕜 := ℝ) (heatAt_continuous μ hQ g))).continuousOn
  have hder (s : ℝ) (hs : 0 < s) : HasDerivAt q (dq s) s := by
    have hh := heat_weakLaplacian_hasDerivAt μ hQ u (t⁻¹ • (g-f))
      (SobolevSpace.resolventAt_weak_laplacian μ hQ t ht f) hs
    have hi := (hasDerivAt_const s a).inner ℝ hh
    have he := ((hasDerivAt_id s).neg.div_const t).exp
    convert! he.mul hi using 1
    simp only [dq,g,map_smul,map_sub,inner_zero_left,add_zero,inner_sub_right,
      real_inner_smul_right,neg_div,one_div,Pi.neg_apply,id_eq]
    ring
  have hbound (s : ℝ) (hs : 0 < s) : |dq s| ≤ (B/t)*Real.exp (-(1/t+K)*s) := by
    have hp : 0 ≤ t⁻¹*Real.exp (-s/t) := by positivity
    calc
      _ = (t⁻¹*Real.exp (-s/t))*|inner ℝ a (heatAt μ hQ s f)| := by
        simp only [dq,abs_neg,abs_mul,abs_of_pos (inv_pos.mpr ht),abs_of_pos (Real.exp_pos _)]
      _ ≤ (t⁻¹*Real.exp (-s/t))*(B*Real.exp (-K*s)) :=
        mul_le_mul_of_nonneg_left (hheat s hs) hp
      _ = (B/t)*Real.exp (-(1/t+K)*s) := by
        have hex : -(1/t+K)*s = -s/t+(-K*s) := by ring
        rw [hex,Real.exp_add]
        ring
  have hlim : Tendsto q atTop (𝓝 0) := by
    have hex : Tendsto (fun s : ℝ => Real.exp (-s/t)) atTop (𝓝 0) := by
      convert! Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos (inv_pos.mpr ht))) using 1
      ext s
      congr 1
      simp only [id_eq]
      ring
    apply squeeze_zero_norm (a := fun s : ℝ => Real.exp (-s/t)*(‖a‖*‖g‖))
    · intro s
      have hn : ‖heatAt μ hQ s g‖ ≤ ‖g‖ :=
        ((heatAt μ hQ s).le_opNorm g).trans (by simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right (heatAt_norm_le μ hQ s) (norm_nonneg g)))
      have hi := (abs_real_inner_le_norm a (heatAt μ hQ s g)).trans
        (mul_le_mul_of_nonneg_left hn (norm_nonneg a))
      simpa only [q,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using
        mul_le_mul_of_nonneg_left hi (Real.exp_pos (-s/t)).le
    · simpa only [zero_mul] using hex.mul_const (‖a‖*‖g‖)
  have hh := abs_at_zero_of_exp_deriv_bound hcont hder hα hbound hlim
  have hq0 : q 0 = inner ℝ a (resolventLp μ hQ t ht f) := by
    simp only [q,neg_zero,zero_div,Real.exp_zero,one_mul,heatAt_zero,one_apply_eq_self]
    rfl
  have hr : (B/t)/(1/t+K) = B/(1+K*t) := by field_simp
  rw [hq0,hr] at hh
  exact hh


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ]

theorem average_lipschitz_center {v : X → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v) (x : X) {r : ℝ} (_ : 0 ≤ r)
    (h0 : μ (closedBall x r) ≠ 0) :
    |(⨍z in closedBall x r, v z ∂μ)-v x| ≤ L*r := by
  let S := closedBall x r
  have ht : μ S ≠ ∞ := (isCompact_closedBall x r).measure_lt_top.ne
  let : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using ht.lt_top⟩
  have hi : IntegrableOn v S μ := hv.continuous.continuousOn.integrableOn_compact (isCompact_closedBall x r)
  have hb : ‖∫z in S, v z-v x ∂μ‖ ≤ ((L:ℝ)*r)*(μ.restrict S).real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    have hd := hv.dist_le_mul z x
    rw [Real.dist_eq] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (show dist z x ≤ r from hz) L.coe_nonneg)
  rw [integral_sub hi (integrable_const (v x)),integral_const] at hb
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,Real.norm_eq_abs] at hb
  have hm : 0 < (μ S).toReal := ENNReal.toReal_pos h0 ht
  rw [average_eq]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  change |(μ S).toReal⁻¹*(∫z in S, v z ∂μ)-v x| ≤ (L:ℝ)*r
  have he : (μ S).toReal⁻¹*(∫z in S, v z ∂μ)-v x =
      (μ S).toReal⁻¹*((∫z in S,v z ∂μ)-(μ S).toReal*v x) := by field_simp
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr hm)]
  calc _ ≤ (μ S).toReal⁻¹*(((L:ℝ)*r)*(μ S).toReal) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hm.le)
    _ = _ := by field_simp

theorem lipschitz_ball_average_bound {f : Lp ℝ 2 μ} {v : X → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v) (he : (f : X → ℝ) =ᵐ[μ] v)
    (x y : X) {r : ℝ} (hr : 0 ≤ r)
    (hx : μ (closedBall x r) ≠ 0) (hy : μ (closedBall y r) ≠ 0) :
    |(⨍z in closedBall x r, f z ∂μ)-(⨍z in closedBall y r, f z ∂μ)| ≤
      (L:ℝ)*(dist x y+2*r) := by
  rw [average_congr (he.filter_mono ae_restrict_le),average_congr (he.filter_mono ae_restrict_le)]
  have ha := average_lipschitz_center μ hv x hr hx
  have hb := average_lipschitz_center μ hv y hr hy
  have hd := hv.dist_le_mul x y
  rw [Real.dist_eq] at hd
  have htri := abs_add_three ((⨍z in closedBall x r,v z ∂μ)-v x) (v x-v y)
    (v y-(⨍z in closedBall y r,v z ∂μ))
  rw [abs_sub_comm (v y)] at htri
  have heq : ((⨍z in closedBall x r,v z ∂μ)-v x)+(v x-v y)+
      (v y-(⨍z in closedBall y r,v z ∂μ)) =
      (⨍z in closedBall x r,v z ∂μ)-(⨍z in closedBall y r,v z ∂μ) := by ring
  rw [heq] at htri
  nlinarith

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [IsLocallyFiniteMeasure μ] in
theorem uniformDensityLp_inner_average (A : Set X) (hA : MeasurableSet A)
    (hAt : μ A ≠ ∞) (f : Lp ℝ 2 μ) :
    inner ℝ (uniformDensityLp μ A hA hAt) f = ⨍x in A,f x ∂μ := by
  simp only [uniformDensityLp,inner_smul_left,conj_trivial,L2.inner_indicatorConstLp_one,
    average,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,Measure.restrict_apply_univ]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.resolvent_lipschitz
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (f : Lp ℝ 2 (hausdorff n X)) {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (hf : φ =ᵐ[hausdorff n X] f)
    (M : ℝ) (hM : ∀ x, |φ x| ≤ M) {t : ℝ} (ht : 0 < t)
    (hKt : 0 < 1+K*t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∃ v : X → ℝ, LipschitzWith (L/⟨1+K*t,hKt.le⟩) v ∧
      (resolventLp (hausdorff n X) hX.quadratic t ht f : X → ℝ) =ᵐ[hausdorff n X] v := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsUnifLocDoublingMeasure μ := hX.locDoubling K n hn
  let u := resolventLp μ hX.quadratic t ht f
  apply exists_lipschitz_of_average_bound u
    ((Lp.memLp _).locallyIntegrable (by norm_num)) (L/⟨1+K*t,hKt.le⟩)
  intro x y r hr
  let A := closedBall x r
  let B := closedBall y r
  have hA0 : μ A ≠ 0 := ne_of_gt ((hX.fullSupport x r hr).trans_le (measure_mono ball_subset_closedBall))
  have hB0 : μ B ≠ 0 := ne_of_gt ((hX.fullSupport y r hr).trans_le (measure_mono ball_subset_closedBall))
  have hAt : μ A ≠ ∞ := ne_of_lt (hX.finiteOnBounded A isBounded_closedBall)
  have hBt : μ B ≠ ∞ := ne_of_lt (hX.finiteOnBounded B isBounded_closedBall)
  let a := uniformDensityLp μ A measurableSet_closedBall hAt
  let b := uniformDensityLp μ B measurableSet_closedBall hBt
  have hheat (s : ℝ) (hs : 0 < s) :
      |inner ℝ (a-b) (heatAt μ hX.quadratic s f)| ≤
        ((L:ℝ)*(dist x y+2*r))*Real.exp (-K*s) := by
    obtain ⟨v,hv,he⟩ := hX.heat_lipschitz K n hn f hφ hf M hM hs.le
    have hh := lipschitz_ball_average_bound μ hv he x y hr.le hA0 hB0
    rw [inner_sub_left,uniformDensityLp_inner_average,uniformDensityLp_inner_average]
    change |(⨍z in A, heatAt μ hX.quadratic s f z ∂μ)-(⨍z in B, heatAt μ hX.quadratic s f z ∂μ)| ≤
      ((L:ℝ)*Real.exp (-K*s))*(dist x y+2*r) at hh
    convert hh using 1 ; ring
  have hh := resolvent_pair_bound_of_heat μ hX.quadratic f (a-b) t ht K
    ((L:ℝ)*(dist x y+2*r)) hKt hheat
  rw [inner_sub_left,uniformDensityLp_inner_average,uniformDensityLp_inner_average] at hh
  change |(⨍z in A,u z ∂μ)-(⨍z in B,u z ∂μ)| ≤
    ((L:ℝ)/(1+K*t))*(dist x y+2*r)
  convert hh using 1 ; ring


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ]

theorem lipschitz_lp_pointwise_convergence
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → μ (ball x r) ≠ 0)
    (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ) (v : ℕ → X → ℝ) (w : X → ℝ)
    (C : ℝ≥0) (hv : ∀ i, LipschitzWith C (v i)) (hw : LipschitzWith C w)
    (hf : ∀ i, (f i : X → ℝ) =ᵐ[μ] v i) (hg : (g : X → ℝ) =ᵐ[μ] w)
    (hc : Tendsto f atTop (𝓝 g)) (x : X) :
    Tendsto (fun i => v i x) atTop (𝓝 (w x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let r := ε/(8*((C:ℝ)+1))
  have hr : 0 < r := by dsimp [r]; positivity
  let A := closedBall x r
  have hA0 : μ A ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr (hpos x r hr)).trans_le
    (measure_mono ball_subset_closedBall))
  have hAt : μ A ≠ ∞ := (isCompact_closedBall x r).measure_lt_top.ne
  let a := uniformDensityLp μ A measurableSet_closedBall hAt
  have hav (i : ℕ) : |inner ℝ a (f i)-v i x| ≤ (C:ℝ)*r := by
    rw [uniformDensityLp_inner_average]
    rw [average_congr ((hf i).filter_mono ae_restrict_le)]
    exact average_lipschitz_center μ (hv i) x hr.le hA0
  have haw : |inner ℝ a g-w x| ≤ (C:ℝ)*r := by
    rw [uniformDensityLp_inner_average]
    rw [average_congr (hg.filter_mono ae_restrict_le)]
    exact average_lipschitz_center μ hw x hr.le hA0
  have hi : Tendsto (fun i => inner ℝ a (f i)) atTop (𝓝 (inner ℝ a g)) :=
    tendsto_const_nhds.inner (𝕜 := ℝ) hc
  filter_upwards [Metric.tendsto_nhds.mp hi (ε/2) (half_pos hε)] with i hi
  rw [Real.dist_eq] at hi ⊢
  have hh := abs_add_three (v i x-inner ℝ a (f i)) (inner ℝ a (f i)-inner ℝ a g)
    (inner ℝ a g-w x)
  have he : (v i x-inner ℝ a (f i))+(inner ℝ a (f i)-inner ℝ a g)+
      (inner ℝ a g-w x) = v i x-w x := by ring
  rw [he] at hh
  have hav' : |v i x-inner ℝ a (f i)| ≤ (C:ℝ)*r := by
    rw [abs_sub_comm]
    exact hav i
  have hb : (C:ℝ)*r < ε/4 := by
    dsimp [r]
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have heq : (C:ℝ)*(ε/(8*((C:ℝ)+1)))*4 = ε*((C:ℝ)/(2*((C:ℝ)+1))) := by field_simp; ring
    rw [heq]
    apply mul_lt_of_lt_one_right hε
    apply (div_lt_one (by positivity)).mpr
    linarith [C.coe_nonneg]
  linarith

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
theorem lipschitz_pointwise_compact_convergence
    (v : ℕ → X → ℝ) (w : X → ℝ) (C : ℝ≥0)
    (hv : ∀ i, LipschitzWith C (v i)) (hw : LipschitzWith C w)
    (hc : ∀ x, Tendsto (fun i => v i x) atTop (𝓝 (w x)))
    {S : Set X} (hS : IsCompact S) : TendstoUniformlyOn v w atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let r := ε/(8*((C:ℝ)+1))
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨s,_,hs,hcov⟩ := hS.finite_cover_balls hr
  have hev : ∀ᶠ i in atTop, ∀ x ∈ s, dist (v i x) (w x) < ε/2 :=
    hs.eventually_all.mpr (fun x hx => Metric.tendsto_nhds.mp (hc x) (ε/2) (half_pos hε))
  filter_upwards [hev] with i hi x hx
  obtain ⟨y,hys,hxy⟩ := mem_iUnion₂.mp (hcov hx)
  have hd : dist x y < r := hxy
  have h1 := (hv i).dist_le_mul x y
  have h2 := hw.dist_le_mul y x
  rw [dist_comm y x] at h2
  have hb : (C:ℝ)*r < ε/4 := by
    dsimp [r]
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have heq : (C:ℝ)*(ε/(8*((C:ℝ)+1)))*4 = ε*((C:ℝ)/(2*((C:ℝ)+1))) := by field_simp; ring
    rw [heq]
    apply mul_lt_of_lt_one_right hε
    apply (div_lt_one (by positivity)).mpr
    linarith [C.coe_nonneg]
  have hadd := dist_triangle4 (v i x) (v i y) (w y) (w x)
  rw [dist_comm (w x)]
  have hd' := mul_le_mul_of_nonneg_left hd.le C.coe_nonneg
  linarith [hi y hys]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem resolventLp_abs_bound (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) (M : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ M) :
    ∀ᵐ x ∂μ, |resolventLp μ hQ t ht f x| ≤ M := by
  have hp := resolventLp_le_const μ hQ t ht M.coe_nonneg f (hf.mono fun x hx => (abs_le.mp hx).2)
  have hmf : ∀ᵐ x ∂μ, (-f) x ≤ M := by
    filter_upwards [hf,Lp.coeFn_neg f] with x hx he
    rw [he,Pi.neg_apply]
    linarith [(abs_le.mp hx).1]
  have hm := resolventLp_le_const μ hQ t ht M.coe_nonneg (-f) hmf
  rw [map_neg] at hm
  filter_upwards [hp,hm,Lp.coeFn_neg (resolventLp μ hQ t ht f)] with x hp hm he
  rw [he,Pi.neg_apply] at hm
  exact abs_le.mpr ⟨by linarith, hp⟩

theorem NoncollapsedRCD.boundedLaplacian_compact_approximation
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (f : Lp ℝ 2 (hausdorff n X)) {φ : X → ℝ} {L M : ℝ≥0}
    (hφ : LipschitzWith L φ) (hf : φ =ᵐ[hausdorff n X] f)
    (hM : ∀ x, |φ x| ≤ M) {S : Set X} (hS : IsCompact S)
    {ε : ℝ} (hε : 0 < ε) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    ∃ (u : SobolevSpace μ hX.quadratic) (d : Lp ℝ 2 μ) (D : ℝ≥0) (v : X → ℝ),
      IsWeakLaplacian μ hX.quadratic u d ∧ (∀ᵐ x ∂μ, |d x| ≤ D) ∧
      LipschitzWith (2*L) v ∧ (SobolevSpace.toLp μ hX.quadratic u : X → ℝ) =ᵐ[μ] v ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic u x| ≤ M) ∧
      ∀ x ∈ S, |v x-φ x| < ε := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hMf : ∀ᵐ x ∂μ, |f x| ≤ M := hf.mono fun x hx => hx ▸ hM x
  have htime : Tendsto (fun i => 1+K*heatStep i) atTop (𝓝 1) := by
    simpa only [mul_zero,add_zero] using tendsto_const_nhds.add (heatStep_tendsto.const_mul K)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (htime.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1)))
  let t (i : ℕ) := heatStep (i+N)
  have ht (i : ℕ) : 0 < t i := heatStep_pos _
  have hKt (i : ℕ) : 1/2 < 1+K*t i := hN (i+N) (by omega)
  let U (i : ℕ) := SobolevSpace.resolventAt μ hX.quadratic (t i) (ht i) f
  let F (i : ℕ) := resolventLp μ hX.quadratic (t i) (ht i) f
  have hex (i : ℕ) : ∃ v : X → ℝ, LipschitzWith (2*L) v ∧ (F i : X → ℝ) =ᵐ[μ] v := by
    obtain ⟨v,hv,he⟩ := hX.resolvent_lipschitz K n hn f hφ hf M hM (ht i)
      (lt_trans (by norm_num) (hKt i))
    refine ⟨v,hv.weaken ?_,he⟩
    apply NNReal.coe_le_coe.mp
    change (L:ℝ)/(1+K*t i) ≤ 2*(L:ℝ)
    apply (div_le_iff₀ (lt_trans (by norm_num) (hKt i))).mpr
    nlinarith [L.coe_nonneg,hKt i]
  choose v hv he using hex
  have hc : Tendsto F atTop (𝓝 f) := by
    exact (resolvent_heatStep_tendsto μ hX.quadratic f).comp (tendsto_add_atTop_nat N)
  have hl : LipschitzWith (2*L) φ := hφ.weaken (by nlinarith [L.coe_nonneg])
  have hp (x : X) := lipschitz_lp_pointwise_convergence μ
    (fun x r hr => (hX.fullSupport x r hr).ne') F f v φ (2*L) hv hl he hf.symm hc x
  have hu := lipschitz_pointwise_compact_convergence v φ (2*L) hv hl hp hS
  obtain ⟨i,hi⟩ := (Metric.tendstoUniformlyOn_iff.mp hu ε hε).exists
  let d := (t i)⁻¹ • (F i-f)
  let D : ℝ≥0 := ⟨2*(M:ℝ)/(t i),div_nonneg (by positivity) (ht i).le⟩
  refine ⟨U i,d,D,v i,SobolevSpace.resolventAt_weak_laplacian μ hX.quadratic (t i) (ht i) f,?_,hv i,he i,?_,?_⟩
  · filter_upwards [resolventLp_abs_bound μ hX.quadratic (t i) (ht i) f M hMf,hMf,
      Lp.coeFn_smul (t i)⁻¹ (F i-f),Lp.coeFn_sub (F i) f] with x hx hfx hd hsub
    change |d x| ≤ (D:ℝ)
    rw [hd,Pi.smul_apply,smul_eq_mul,hsub,Pi.sub_apply,abs_mul,abs_of_pos (inv_pos.mpr (ht i))]
    change (t i)⁻¹*|F i x-f x| ≤ 2*(M:ℝ)/(t i)
    have hb : |F i x-f x| ≤ 2*(M:ℝ) := (abs_sub _ _).trans (by dsimp [F] at *; linarith)
    calc _ ≤ (t i)⁻¹*(2*(M:ℝ)) := mul_le_mul_of_nonneg_left hb (inv_pos.mpr (ht i)).le
      _ = _ := by ring
  · exact resolventLp_abs_bound μ hX.quadratic (t i) (ht i) f M hMf
  · intro x hx
    simpa only [Real.dist_eq,abs_sub_comm] using hi x hx


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.bounded_strong_recovery (f : SobolevSpace μ hQ) :
    ∃ fs : ℕ → SobolevSpace μ hQ, Tendsto fs atTop (𝓝 f) ∧
      ∀ i, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (fs i) x| ≤ (i:ℝ) := by
  let fs (i : ℕ) := SobolevSpace.compContraction μ hQ
    (clipReal_lipschitz i) (clipReal_zero i) f
  have hid : (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).compLp
      (by rfl) (SobolevSpace.toLp μ hQ f) = SobolevSpace.toLp μ hQ f := by
    apply Lp.ext
    exact (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).coeFn_compLp
      (by rfl) (SobolevSpace.toLp μ hQ f)
  have ht (a : ℝ) : Tendsto (fun i : ℕ => clipReal i a) atTop (𝓝 a) := by
    obtain ⟨N,hN⟩ := exists_nat_gt |a|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with i hi
    exact (clipReal_eq_self (i:ℝ≥0) (hN.le.trans (by exact_mod_cast hi))).symm
  have hl := compLp_tendsto_of_pointwise μ (fun i : ℕ => clipReal_lipschitz i)
    LipschitzWith.id (fun i : ℕ => clipReal_zero i) (by rfl) ht
    (SobolevSpace.toLp μ hQ f)
  rw [hid] at hl
  refine ⟨fs,?_,?_⟩
  · apply SobolevSpace.tendsto_of_toLp_tendsto_energy_le μ hQ hl
    intro ε hε
    exact Eventually.of_forall fun i =>
      (SobolevSpace.energy_compContraction_le μ hQ (clipReal_lipschitz i)
        (clipReal_zero i) f).trans (le_add_of_nonneg_right hε.le)
  · intro i
    filter_upwards [(clipReal_lipschitz (i:ℝ≥0)).coeFn_compLp
      (clipReal_zero i) (SobolevSpace.toLp μ hQ f)] with x hx
    change |((clipReal_lipschitz (i:ℝ≥0)).compLp (clipReal_zero i)
      (SobolevSpace.toLp μ hQ f)) x| ≤ (i:ℝ)
    rw [hx]
    exact clipReal_abs_le _ _


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
 theorem weakLaplacian_of_bounded_tests (f : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (h : ∀ (g : SobolevSpace μ hQ) (C : ℝ≥0),
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ C) →
      energyForm μ hQ f g = -inner ℝ d (SobolevSpace.toLp μ hQ g)) :
    IsWeakLaplacian μ hQ f d := by
  intro g
  obtain ⟨gs,hgs,hb⟩ := SobolevSpace.bounded_strong_recovery μ hQ g
  have he := ((energyForm_continuous μ hQ).tendsto (f,g)).comp
    (tendsto_const_nhds.prodMk_nhds hgs)
  have hi := ((tendsto_const_nhds (x := d)).inner (𝕜 := ℝ) ((SobolevSpace.toLpCLM μ hQ).continuous.tendsto g |>.comp hgs)).neg
  exact tendsto_nhds_unique he (hi.congr (fun i => (h (gs i) i (hb i)).symm))

 theorem weakLaplacian_comp_C2 (f : SobolevSpace μ hQ) (d q : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ f d)
    {φ ψ χ : ℝ → ℝ} {C D : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : LipschitzWith D ψ) (hψ0 : ψ 0 = 0)
    (hχ : Continuous χ) (hdφ : ∀ a, HasDerivAt φ (ψ a) a)
    (hdψ : ∀ a, HasDerivAt ψ (χ a) a)
    (B E : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) (hE : ∀ a, |χ a| ≤ E)
    (hq : ⇑q =ᵐ[μ] fun x => ψ (SobolevSpace.toLp μ hQ f x)*d x+
      χ (SobolevSpace.toLp μ hQ f x)*localGamma μ hQ f f x) :
    IsWeakLaplacian μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) q := by
  apply weakLaplacian_of_bounded_tests μ hQ
  intro g A hg
  let v := SobolevSpace.comp μ hQ hψ hψ0 f
  let F := SobolevSpace.toLp μ hQ f
  let G := SobolevSpace.toLp μ hQ g
  have hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ v x| ≤ B := by
    filter_upwards [SobolevSpace.comp_coe μ hQ hψ hψ0 f] with x hx
    change |SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hψ hψ0 f) x| ≤ B
    rw [hx]
    exact hB _
  have hi : Integrable (fun x => ψ (F x)*localGamma μ hQ f g x) μ :=
    (localGamma_memL1 μ hQ f g).bdd_mul
      (hψ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F))
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB (F x))
  have hj0 : Integrable (fun x => χ (F x)*localGamma μ hQ f f x) μ :=
    (localGamma_memL1 μ hQ f f).bdd_mul
      (hχ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F))
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hE (F x))
  have hj : Integrable (fun x => G x*(χ (F x)*localGamma μ hQ f f x)) μ :=
    hj0.bdd_mul (Lp.aestronglyMeasurable G) (by simpa only [Real.norm_eq_abs] using hg)
  have hdg : Integrable (fun x => ψ (F x)*(d x*G x)) μ :=
    ((Lp.memLp d).integrable_mul (Lp.memLp G)).bdd_mul
      (hψ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F))
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB (F x))
  have hchain : localGamma μ hQ f v =ᵐ[μ] fun x => χ (F x)*localGamma μ hQ f f x := by
    filter_upwards [localGamma_comm μ hQ f v,
      localGamma_comp_C1 μ hQ f f hψ hψ0 hχ hdψ E hE] with x hc hh
    exact hc.trans hh
  have he : energyForm μ hQ f (SobolevSpace.product μ hQ v g B A) =
      (∫ x, ψ (F x)*localGamma μ hQ f g x ∂μ)+
      (∫ x, G x*(χ (F x)*localGamma μ hQ f f x) ∂μ) := by
    rw [←integral_localGamma_eq_energyForm,←integral_add hi hj]
    apply integral_congr_ae
    filter_upwards [localGamma_product_right μ hQ f v g B A hv hg,
      SobolevSpace.comp_coe μ hQ hψ hψ0 f,hchain] with x hp hc hh
    rw [hp,hc,hh]
    rfl
  have heφ : energyForm μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) g =
      ∫ x, ψ (F x)*localGamma μ hQ f g x ∂μ := by
    rw [←integral_localGamma_eq_energyForm]
    exact integral_congr_ae (localGamma_comp_C1 μ hQ f g hφ hφ0 hψ.continuous hdφ B hB)
  have hetest : inner ℝ d (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ v g B A)) =
      ∫ x, ψ (F x)*(d x*G x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ v g B A hv hg,
      SobolevSpace.comp_coe μ hQ hψ hψ0 f] with x hp hc
    dsimp only [v,F,G] at *
    simp only [Real.inner_apply,hp,hc,Function.comp_apply]
    ring
  have heq : inner ℝ q G = (∫ x, ψ (F x)*(d x*G x) ∂μ)+
      (∫ x, G x*(χ (F x)*localGamma μ hQ f f x) ∂μ) := by
    rw [L2.inner_def,←integral_add hdg hj]
    apply integral_congr_ae
    filter_upwards [hq] with x hx
    dsimp only [F,G] at *
    simp only [Real.inner_apply,hx]
    ring
  have ht := hd (SobolevSpace.product μ hQ v g B A)
  rw [he,hetest] at ht
  rw [heφ]
  change _ = -inner ℝ q G
  rw [heq]
  linarith


end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

theorem SobolevSpace.minimalSlope_le_lipschitz (f : SobolevSpace μ hQ)
    {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (he : SobolevSpace.toLp μ hQ f =ᵐ[μ] g) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ L := by
  rcases isEmpty_or_nonempty X with hX|hX
  · exact Eventually.of_forall fun x => isEmptyElim x
  let p : X := Classical.choice hX
  let R (i : ℕ) : ℝ := i+1
  have hR (i : ℕ) : 0 < R i := by dsimp [R]; positivity
  let gs (i : ℕ) (x : X) := radialCutoff p (R i) x*g x
  have hh (i : ℕ) : ∃ C, LipschitzWith C (gs i) :=
    lipschitz_mul_compact_cutoff (radialCutoff_lipschitz p (hR i)) hg
      (radialCutoff_hasCompactSupport p (hR i))
      (fun x => by rw [abs_of_nonneg (radialCutoff_bounds p (R i) x).1]; exact (radialCutoff_bounds p (R i) x).2)
  choose C hC using hh
  have hs (i : ℕ) : HasCompactSupport (gs i) :=
    (radialCutoff_hasCompactSupport p (hR i)).mul_right
  let fs (i : ℕ) := SobolevSpace.ofLipschitzCompact μ hQ (hC i) (hs i)
  have hae (i : ℕ) : ∀ᵐ x ∂μ, dist p x < R i → SobolevSpace.minimalSlope μ hQ f x ≤ L := by
    filter_upwards [SobolevSpace.minimalSlope_eq_on_eq μ hQ f (fs i),he,
      SobolevSpace.ofLipschitzCompact_coe μ hQ (hC i) (hs i),
      SobolevSpace.ofLipschitzCompact_minimalSlope_le_slope μ hQ (hC i) (hs i)] with x heq hfx hfs hsl
    intro hx
    have hgx : gs i x=g x := by simp only [gs,radialCutoff_eq_one p (hR i) hx.le,one_mul]
    have hfg : SobolevSpace.toLp μ hQ f x=SobolevSpace.toLp μ hQ (fs i) x := by
      exact hfx.trans (hgx.symm.trans hfs.symm)
    rw [heq hfg]
    have hlocal : gs i =ᶠ[𝓝 x] g := by
      filter_upwards [(isOpen_lt (continuous_const.dist continuous_id) continuous_const).mem_nhds hx] with y hy
      simp only [gs,radialCutoff_eq_one p (hR i) (show dist p y ≤ R i from hy.le),one_mul]
    have hslope := localSlope_congr_nhds hlocal
    rw [hslope] at hsl
    exact hsl.trans (by
      have hz := ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_of_lipschitz hg x)
      simpa only [ENNReal.coe_toReal] using hz)
  filter_upwards [ae_all_iff.mpr hae] with x hx
  obtain ⟨i,hi⟩ := exists_nat_gt (dist p x)
  exact hx i (by dsimp [R]; linarith)


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

theorem exists_boundedLaplacian_comp_C2 (f : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ f d) {v : X → ℝ} {L D : ℝ≥0}
    (hv : LipschitzWith L v) (hf : SobolevSpace.toLp μ hQ f =ᵐ[μ] v)
    (hD : ∀ᵐ x ∂μ, |d x| ≤ D)
    {φ ψ χ : ℝ → ℝ} {C J : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0=0)
    (hψ : LipschitzWith J ψ) (hψ0 : ψ 0=0)
    (hχ : Continuous χ) (hdφ : ∀ a, HasDerivAt φ (ψ a) a)
    (hdψ : ∀ a, HasDerivAt ψ (χ a) a)
    (B E : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) (hE : ∀ a, |χ a| ≤ E) :
    ∃ q : Lp ℝ 2 μ,
      IsWeakLaplacian μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) q ∧
      (∀ᵐ x ∂μ, |q x| ≤ (B*D+E*L^2:ℝ≥0)) := by
  let F := SobolevSpace.toLp μ hQ f
  let G := SobolevSpace.minimalSlope μ hQ f
  have hG0 : ∀ᵐ x ∂μ, 0 ≤ G x := (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ f)
  have hGL := SobolevSpace.minimalSlope_le_lipschitz μ hQ f hv hf
  have hGs : MemLp (fun x => G x^2) 2 μ := by
    apply (Lp.memLp G).of_le_mul (c := (L:ℝ)) ((Lp.aestronglyMeasurable G).pow 2)
    filter_upwards [hG0,hGL] with x h0 hL
    change |G x^2| ≤ (L:ℝ)*|G x|
    rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg h0]
    change G x ≤ L at hL
    nlinarith
  have hmψ : MemLp (fun x => ψ (F x)) ∞ μ :=
    memLp_top_of_bound (hψ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)) B
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB (F x))
  have hmχ : MemLp (fun x => χ (F x)) ∞ μ :=
    memLp_top_of_bound (hχ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)) E
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hE (F x))
  let Q (x : X) := ψ (F x)*d x+χ (F x)*G x^2
  have hm : MemLp Q 2 μ := by
    simpa only [Q, Pi.add_apply, Pi.mul_apply, mul_comm] using!
      ((Lp.memLp d).mul hmψ).add (hGs.mul hmχ)
  let q := hm.toLp Q
  have heq : ⇑q =ᵐ[μ] Q := hm.coeFn_toLp
  refine ⟨q,weakLaplacian_comp_C2 μ hQ f d q hd hφ hφ0 hψ hψ0 hχ hdφ hdψ B E hB hE ?_,?_⟩
  · filter_upwards [heq,localGamma_self μ hQ f] with x hx hg
    rw [hx,hg]
  · filter_upwards [heq,hD,hG0,hGL] with x hx hd h0 hL
    rw [hx]
    change |ψ (F x)*d x+χ (F x)*G x^2| ≤ (B:ℝ)*D+E*(L:ℝ)^2
    calc
      _ ≤ |ψ (F x)*d x|+|χ (F x)*G x^2| := abs_add_le _ _
      _ ≤ (B:ℝ)*D+E*(L:ℝ)^2 := by
        simp only [abs_mul,abs_pow,abs_of_nonneg h0]
        exact add_le_add (mul_le_mul (hB _) hd (abs_nonneg _) B.coe_nonneg)
          (mul_le_mul (hE _) ((sq_le_sq₀ h0 L.coe_nonneg).mpr hL) (sq_nonneg _) E.coe_nonneg)


end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem weakLaplacian_product_plateau (a b : SobolevSpace μ hQ) (d q : Lp ℝ 2 μ)
    (A B : ℝ≥0) (ha : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ a x| ≤ A)
    (hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ b x| ≤ B)
    (hd : IsWeakLaplacian μ hQ a d)
    (hplateau : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ a x=0 ∨
      SobolevSpace.toLp μ hQ b x=0 ∨ SobolevSpace.toLp μ hQ b x=1)
    (hq : ⇑q =ᵐ[μ] fun x => SobolevSpace.toLp μ hQ b x*d x) :
    IsWeakLaplacian μ hQ (SobolevSpace.product μ hQ a b A B) q := by
  apply weakLaplacian_of_bounded_tests μ hQ
  intro g C hg
  have he : energyForm μ hQ (SobolevSpace.product μ hQ a b A B) g =
      energyForm μ hQ a (SobolevSpace.product μ hQ b g B C) := by
    rw [←integral_localGamma_eq_energyForm,←integral_localGamma_eq_energyForm]
    apply integral_congr_ae
    filter_upwards [localGamma_product_left μ hQ a b g A B ha hb,
      localGamma_product_right μ hQ a b g B C hb hg,
      localGamma_zero_on_level μ hQ a b 0,
      localGamma_zero_on_level μ hQ b a 0,
      localGamma_zero_on_level μ hQ b a 1,
      localGamma_zero_on_level μ hQ b g 0,
      localGamma_zero_on_level μ hQ b g 1,
      localGamma_comm μ hQ a b,hplateau] with x hp hr ha0 hb0 hb1 hg0 hg1 hc hpl
    rw [hp,hr]
    rcases hpl with h|h|h
    · rw [h,ha0 h]; ring
    · rw [hc,hb0 h,hg0 h]; ring
    · rw [hc,hb1 h,hg1 h]; ring
  have hi : inner ℝ d (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ b g B C)) =
      inner ℝ q (SobolevSpace.toLp μ hQ g) := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ b g B C hb hg,hq] with x hp hq
    simp only [Real.inner_apply,hp,hq]
    ring
  rw [he,hd,hi]


end

 
section

 
open Set Filter Metric
open scoped Topology NNReal ENNReal

theorem exists_smooth_scalar_cutoff :
    ∃ (φ ψ χ : ℝ → ℝ) (C D B E : ℝ≥0),
      LipschitzWith C φ ∧ LipschitzWith D ψ ∧ Continuous χ ∧
      (∀ a, HasDerivAt φ (ψ a) a) ∧ (∀ a, HasDerivAt ψ (χ a) a) ∧
      (∀ a, |ψ a| ≤ B) ∧ (∀ a, |χ a| ≤ E) ∧
      φ 0=0 ∧ ψ 0=0 ∧ (∀ a, 0 ≤ φ a ∧ φ a ≤ 1) ∧
      (∀ a, a ≤ 1/4 → φ a=0) ∧ (∀ a, |a-1| ≤ 1/4 → φ a=1) := by
  let f : ContDiffBump (1:ℝ) := ⟨1/4,3/4,by norm_num,by norm_num⟩
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) (f : ℝ → ℝ) := f.contDiff
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (f : ℝ → ℝ)) := (contDiff_infty_iff_deriv.mp hf).2
  have hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (deriv (f : ℝ → ℝ))) := (contDiff_infty_iff_deriv.mp hψ).2
  obtain ⟨B,hB⟩ := f.hasCompactSupport.deriv.exists_bound_of_continuous hψ.continuous
  obtain ⟨E,hE⟩ := f.hasCompactSupport.deriv.deriv.exists_bound_of_continuous hχ.continuous
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hE 0)
  let Bn : ℝ≥0 := ⟨B,hB0⟩
  let En : ℝ≥0 := ⟨E,hE0⟩
  have hl : LipschitzWith Bn (f : ℝ → ℝ) :=
    lipschitzWith_of_nnnorm_deriv_le (hf.differentiable (by simp))
      (fun x => NNReal.coe_le_coe.mp (hB x))
  have hlψ : LipschitzWith En (deriv (f : ℝ → ℝ)) :=
    lipschitzWith_of_nnnorm_deriv_le (hψ.differentiable (by simp))
      (fun x => NNReal.coe_le_coe.mp (hE x))
  have hz (a : ℝ) (ha : a ≤ 1/4) : f a=0 := by
    apply f.zero_of_le_dist
    change (3/4:ℝ) ≤ |a-1|
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hzψ : deriv (f : ℝ → ℝ) 0=0 := by
    have he : (f : ℝ → ℝ) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [gt_mem_nhds (by norm_num : (0:ℝ)<1/4)] with a ha
      exact hz a ha.le
    simpa only [deriv_const] using he.deriv_eq
  refine ⟨f,deriv (f : ℝ → ℝ),deriv (deriv (f : ℝ → ℝ)),Bn,En,Bn,En,
    hl,hlψ,hχ.continuous,?_,?_,?_,?_,hz 0 (by norm_num),hzψ,?_,hz,?_⟩
  · intro a; exact (hf.differentiable (by simp) a).hasDerivAt
  · intro a; exact (hψ.differentiable (by simp) a).hasDerivAt
  · intro a; exact hB a
  · intro a; exact hE a
  · intro a; exact ⟨f.nonneg,f.le_one⟩
  · intro a ha
    exact f.one_of_mem_closedBall ha


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.exists_boundedLaplacian_cutoff
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) {R : ℝ} (hR : 0 < R) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    ∃ (u : SobolevSpace μ hX.quadratic) (q : Lp ℝ 2 μ) (L D : ℝ≥0) (v : X → ℝ),
      IsWeakLaplacian μ hX.quadratic u q ∧ (∀ᵐ x ∂μ, |q x| ≤ D) ∧
      LipschitzWith L v ∧ HasCompactSupport v ∧
      SobolevSpace.toLp μ hX.quadratic u =ᵐ[μ] v ∧
      (∀ x, 0 ≤ v x ∧ v x ≤ 1) ∧
      (∀ x, dist p x ≤ R → v x=1) ∧
      (∀ x, 4*R ≤ dist p x → v x=0) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let hQ := hX.quadratic
  let f := SobolevSpace.toLp μ hQ (radialSobolevCutoff μ hQ p hR)
  have hf : radialCutoff p R =ᵐ[μ] f := (radialSobolevCutoff_coe μ hQ p hR).symm
  have hM (x : X) : |radialCutoff p R x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (radialCutoff_bounds p R x).1]
    exact (radialCutoff_bounds p R x).2
  obtain ⟨u,d,D,v,hud,hd,hv,hu,huM,happrox⟩ := hX.boundedLaplacian_compact_approximation K n hn f
    (radialCutoff_lipschitz p hR) hf hM (isCompact_closedBall p (4*R)) (by norm_num : (0:ℝ)<1/8)
  obtain ⟨φ,ψ,χ,C,J,B,E,hφ,hψ,hχ,hdφ,hdψ,hB,hE,hφ0,hψ0,hφbounds,hφzero,hφone⟩ := exists_smooth_scalar_cutoff
  let a := SobolevSpace.comp μ hQ hφ hφ0 u
  have ha : SobolevSpace.toLp μ hQ a =ᵐ[μ] fun x => φ (v x) := by
    filter_upwards [SobolevSpace.comp_coe μ hQ hφ hφ0 u,hu] with x hx he
    exact hx.trans (congrArg φ he)
  have haB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ a x| ≤ (1:ℝ≥0) := by
    filter_upwards [ha] with x hx
    rw [hx,abs_of_nonneg (hφbounds _).1]
    exact (hφbounds _).2
  obtain ⟨q,hq,hqB⟩ := exists_boundedLaplacian_comp_C2 μ hQ u d hud hv hu hd
    hφ hφ0 hψ hψ0 hχ hdφ hdψ B E hB hE
  let Q : ℝ≥0 := B*D+E*(2*⟨R⁻¹,inv_nonneg.mpr hR.le⟩)^2
  have hR2 : 0 < 2*R := by positivity
  let b := radialSobolevCutoff μ hQ p hR2
  let η := radialCutoff p (2*R)
  have hb : SobolevSpace.toLp μ hQ b =ᵐ[μ] η := radialSobolevCutoff_coe μ hQ p hR2
  have hη (x : X) : 0 ≤ η x ∧ η x ≤ 1 := radialCutoff_bounds p (2*R) x
  have hηabs (x : X) : |η x| ≤ (1:ℝ≥0) := by rw [abs_of_nonneg (hη x).1]; exact (hη x).2
  have hbB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ b x| ≤ (1:ℝ≥0) := hb.mono fun x hx => hx ▸ hηabs x
  have hplateau : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ a x=0 ∨
      SobolevSpace.toLp μ hQ b x=0 ∨ SobolevSpace.toLp μ hQ b x=1 := by
    filter_upwards [ha,hb] with x hx hy
    rw [hx,hy]
    by_cases hi : dist p x ≤ 2*R
    · exact Or.inr (Or.inr (radialCutoff_eq_one p hR2 hi))
    by_cases ho : 4*R ≤ dist p x
    · exact Or.inr (Or.inl (radialCutoff_eq_zero p hR2 (by linarith)))
    left
    have hc := happrox x (show x ∈ closedBall p (4*R) by rw [mem_closedBall,dist_comm]; linarith)
    rw [radialCutoff_eq_zero p hR (by linarith),sub_zero] at hc
    exact hφzero _ (by linarith [le_abs_self (v x)])
  let mult := boundedMultiplier μ η (radialCutoff_lipschitz p hR2).continuous.measurable 1 hηabs
  let dq := lpMultiplier μ mult q
  have hdq : ⇑dq =ᵐ[μ] fun x => η x*q x := by
    filter_upwards [lpMultiplier_coe μ mult q,boundedMultiplier_coe μ η
      (radialCutoff_lipschitz p hR2).continuous.measurable 1 hηabs] with x hx hy
    exact hx.trans (by rw [hy])
  let w := SobolevSpace.product μ hQ a b 1 1
  have hwd : IsWeakLaplacian μ hQ w dq := by
    apply weakLaplacian_product_plateau μ hQ a b q dq 1 1 haB hbB hq hplateau
    filter_upwards [hdq,hb] with x hx hy
    rw [hx,hy]
  let F (x : X) := η x*φ (v x)
  have hwe : SobolevSpace.toLp μ hQ w =ᵐ[μ] F := by
    filter_upwards [SobolevSpace.product_coe μ hQ a b 1 1 haB hbB,ha,hb] with x hx hax hbx
    rw [hx,hax,hbx]
    exact mul_comm _ _
  obtain ⟨LL,hLL⟩ := lipschitz_mul_compact_cutoff (radialCutoff_lipschitz p hR2)
    (hφ.comp hv) (radialCutoff_hasCompactSupport p hR2) hηabs
  refine ⟨w,dq,LL,Q,F,hwd,?_,hLL,(radialCutoff_hasCompactSupport p hR2).mul_right,hwe,?_,?_,?_⟩
  · filter_upwards [hdq,hqB] with x hx hqB
    rw [hx,abs_mul]
    exact (mul_le_mul (hηabs x) hqB (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · intro x
    exact ⟨mul_nonneg (hη x).1 (hφbounds _).1,
      (mul_le_mul (hη x).2 (hφbounds _).2 (hφbounds _).1 zero_le_one).trans_eq (one_mul _)⟩
  · intro x hx
    have hi : η x=1 := radialCutoff_eq_one p hR2 (by linarith)
    have hc := happrox x (show x ∈ closedBall p (4*R) by rw [mem_closedBall,dist_comm]; linarith)
    rw [radialCutoff_eq_one p hR hx] at hc
    exact show η x*φ (v x)=1 from by rw [hi,hφone _ (by linarith),one_mul]
  · intro x hx
    have hi : η x=0 := radialCutoff_eq_zero p hR2 (by linarith)
    exact show η x*φ (v x)=0 from by rw [hi,zero_mul]


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
 theorem uniformDensityLp_norm_sq (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (_ : μ A ≠ 0) :
    ‖uniformDensityLp μ A hA hAt‖^2 = (μ A).toReal⁻¹ := by
  rw [uniformDensityLp,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg),
    norm_indicatorConstLp (by norm_num : (2:ℝ≥0∞)≠0) (by norm_num : (2:ℝ≥0∞)≠∞)]
  simp only [norm_one,ENNReal.toReal_ofNat,one_mul,one_div]
  have he : (μ.real A ^ (2:ℝ)⁻¹)^2 = μ.real A := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (show 0 ≤ μ.real A from ENNReal.toReal_nonneg)]
    norm_num
  rw [mul_pow,he]
  change (μ A).toReal⁻¹^2*(μ A).toReal = (μ A).toReal⁻¹
  field_simp

variable [ProperSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ]

theorem lipschitz_lp_pointwise_error {f g : Lp ℝ 2 μ} {v w : X → ℝ} {C D : ℝ≥0}
    (hv : LipschitzWith C v) (hw : LipschitzWith D w)
    (hf : (f : X → ℝ) =ᵐ[μ] v) (hg : (g : X → ℝ) =ᵐ[μ] w)
    (x : X) {r : ℝ} (hr : 0 ≤ r) (h0 : μ (closedBall x r) ≠ 0) :
    ∃ a : ℝ, 0 ≤ a ∧ a^2 ≤ ‖f-g‖^2/(μ (closedBall x r)).toReal ∧
      |v x-w x| ≤ ((C:ℝ)+D)*r+a := by
  let A := closedBall x r
  have hAt : μ A ≠ ∞ := (isCompact_closedBall x r).measure_lt_top.ne
  let q := uniformDensityLp μ A measurableSet_closedBall hAt
  have hav : |inner ℝ q f-v x| ≤ (C:ℝ)*r := by
    rw [uniformDensityLp_inner_average,average_congr (hf.filter_mono ae_restrict_le)]
    exact average_lipschitz_center μ hv x hr h0
  have haw : |inner ℝ q g-w x| ≤ (D:ℝ)*r := by
    rw [uniformDensityLp_inner_average,average_congr (hg.filter_mono ae_restrict_le)]
    exact average_lipschitz_center μ hw x hr h0
  refine ⟨|inner ℝ q (f-g)|,abs_nonneg _,?_,?_⟩
  · have hi := abs_real_inner_le_norm q (f-g)
    have hh := pow_le_pow_left₀ (abs_nonneg _) hi 2
    rw [mul_pow,uniformDensityLp_norm_sq μ A measurableSet_closedBall hAt h0] at hh
    exact hh.trans_eq (by ring)
  · rw [inner_sub_right]
    have hh := abs_add_three (v x-inner ℝ q f) (inner ℝ q f-inner ℝ q g) (inner ℝ q g-w x)
    have he : (v x-inner ℝ q f)+(inner ℝ q f-inner ℝ q g)+(inner ℝ q g-w x)=v x-w x := by ring
    rw [he] at hh
    have hav' : |v x-inner ℝ q f| ≤ (C:ℝ)*r := by rw [abs_sub_comm]; exact hav
    linarith


end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def cutoffVolumeFloor (K : ℝ) (n : ℕ) (R : ℝ) : ℝ :=
  ((1/672:ℝ)/Real.exp (14*R*Real.sqrt (|K|/((n:ℝ)-1))))^n

theorem cutoffVolumeFloor_pos (K : ℝ) (n : ℕ) (R : ℝ) :
    0 < cutoffVolumeFloor K n R := by unfold cutoffVolumeFloor; positivity

theorem FullCD.cutoff_volume_comparison (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (p x : X) {R : ℝ} (hR : 0 < R) (hx : dist p x ≤ 4*R) :
    cutoffVolumeFloor K n R * μ.real (closedBall p (2*R)) ≤
      μ.real (closedBall x (R/96)) := by
  have hs : closedBall p (2*R) ⊆ ball x (7*R) := by
    intro y hy
    have ht := dist_triangle y p x
    rw [mem_closedBall] at hy
    rw [mem_ball]
    linarith
  have he := hcd.ball_ratio μ K n hpos hfin hn x (R/96) (7*R)
    (by positivity) (by linarith)
  have hq : (R/96)/(7*R) = (1/672:ℝ) := by field_simp; ring
  rw [hq,show 2*(7*R)=14*R by ring] at he
  have hf : distortionFloor K n (14*R) (1/672)^n * μ (closedBall p (2*R)) ≤
      μ (closedBall x (R/96)) :=
    (mul_le_mul' le_rfl (measure_mono hs)).trans (he.trans (measure_mono ball_subset_closedBall))
  have hr := ENNReal.toReal_mono (hfin _ isBounded_closedBall).ne hf
  rw [ENNReal.toReal_mul,ENNReal.toReal_pow] at hr
  unfold distortionFloor at hr
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  exact hr



 
theorem NoncollapsedRCD.quantitative_radial_resolvent
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hKt : 1/2 ≤ 1+K*t) (hsize : t ≤ cutoffVolumeFloor K n R*R^2/1024) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    let L : ℝ≥0 := ⟨R⁻¹,inv_nonneg.mpr hR.le⟩
    ∃ (u : SobolevSpace μ hX.quadratic) (d : Lp ℝ 2 μ) (v : X → ℝ),
      IsWeakLaplacian μ hX.quadratic u d ∧ (∀ᵐ x ∂μ, |d x| ≤ 2/t) ∧
      LipschitzWith (2*L) v ∧ SobolevSpace.toLp μ hX.quadratic u =ᵐ[μ] v ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic u x| ≤ 1) ∧
      ∀ x, dist p x ≤ 4*R → |v x-radialCutoff p R x| < 1/8 := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let hQ := hX.quadratic
  let L : ℝ≥0 := ⟨R⁻¹,inv_nonneg.mpr hR.le⟩
  let f := SobolevSpace.toLp μ hQ (radialSobolevCutoff μ hQ p hR)
  let u := SobolevSpace.resolventAt μ hQ t ht f
  let F := resolventLp μ hQ t ht f
  have hf : radialCutoff p R =ᵐ[μ] f := (radialSobolevCutoff_coe μ hQ p hR).symm
  have hφ := radialCutoff_lipschitz p hR
  have hM (x : X) : |radialCutoff p R x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (radialCutoff_bounds p R x).1]
    exact (radialCutoff_bounds p R x).2
  have hMf : ∀ᵐ x ∂μ, |f x| ≤ (1:ℝ≥0) := hf.mono fun x hx => hx ▸ hM x
  have hKt0 : 0 < 1+K*t := by linarith
  obtain ⟨v,hv,he⟩ := hX.resolvent_lipschitz K n hn f hφ hf 1 hM ht hKt0
  have hv' : LipschitzWith (2*L) v := hv.weaken (by
    apply NNReal.coe_le_coe.mp
    change R⁻¹/(1+K*t) ≤ 2*R⁻¹
    apply (div_le_iff₀ hKt0).mpr
    nlinarith [inv_nonneg.mpr hR.le])
  let d := t⁻¹ • (F-f)
  have hFM : ∀ᵐ x ∂μ, |F x| ≤ (1:ℝ≥0) := resolventLp_abs_bound μ hQ t ht f 1 hMf
  refine ⟨u,d,v,SobolevSpace.resolventAt_weak_laplacian μ hQ t ht f,?_,hv',he,hFM,?_⟩
  · filter_upwards [hFM,hMf,Lp.coeFn_smul t⁻¹ (F-f),Lp.coeFn_sub F f] with x hx hfx hd hsub
    rw [hd,Pi.smul_apply,smul_eq_mul,hsub,Pi.sub_apply,abs_mul,abs_of_pos (inv_pos.mpr ht)]
    change t⁻¹*|F x-f x| ≤ 2/t
    have hb : |F x-f x| ≤ 2 := (abs_sub _ _).trans (by norm_num at hx hfx ⊢; linarith)
    calc _ ≤ t⁻¹*2 := mul_le_mul_of_nonneg_left hb (inv_pos.mpr ht).le
      _ = _ := by ring
  · intro x hx
    have hr : 0 < R/96 := by positivity
    have h0 : μ (closedBall x (R/96)) ≠ 0 := ne_of_gt
      ((hX.fullSupport x (R/96) hr).trans_le (measure_mono ball_subset_closedBall))
    have htop : μ (closedBall x (R/96)) ≠ ∞ := (isCompact_closedBall x (R/96)).measure_lt_top.ne
    have hm : 0 < μ.real (closedBall x (R/96)) := ENNReal.toReal_pos h0 htop
    have hvol := hX.cd.cutoff_volume_comparison μ K n hX.fullSupport hX.finiteOnBounded hn p x hR hx
    have herr := resolventLp_error_energy μ hQ t ht (radialSobolevCutoff μ hQ p hR)
    have hen := radialSobolevCutoff_energy_le μ hQ p hR
    have herror : ‖F-f‖^2 ≤ μ.real (closedBall x (R/96))/1024 := by
      have hR2 : 0 < R^2 := sq_pos_of_pos hR
      have htt : t/R^2 ≤ cutoffVolumeFloor K n R/1024 := by
        apply (div_le_iff₀ hR2).mpr
        nlinarith only [hsize]
      have he2 := mul_le_mul_of_nonneg_left hen (show 0 ≤ 2*t by positivity)
      have heq : 2*t*(μ.real (closedBall p (2*R))/(2*R^2)) =
          (t/R^2)*μ.real (closedBall p (2*R)) := by ring
      rw [heq] at he2
      have hprod := mul_le_mul_of_nonneg_right htt (show 0 ≤ μ.real (closedBall p (2*R)) from ENNReal.toReal_nonneg)
      change ‖F-f‖^2 ≤ _ at herr
      nlinarith only [herr,he2,hprod,hvol]
    obtain ⟨a,ha,ha2,hab⟩ := lipschitz_lp_pointwise_error μ hv' hφ he hf.symm x hr.le h0
    have ha2' : a^2 ≤ (1:ℝ)/1024 := by
      apply ha2.trans
      apply (div_le_iff₀ hm).mpr
      nlinarith only [herror]
    have hal : a ≤ (1:ℝ)/32 := by nlinarith
    change |v x-radialCutoff p R x| ≤ (2*R⁻¹+R⁻¹)*(R/96)+a at hab
    have hrad : (2*R⁻¹+R⁻¹)*(R/96) = (1:ℝ)/32 := by field_simp; ring
    rw [hrad] at hab
    linarith


end

 
section

 

open scoped NNReal

noncomputable def cutoffTimeFactor (n : ℕ) (A : ℝ) : ℝ :=
  min (((1/672:ℝ)/Real.exp (14*Real.sqrt A))^n/1024) (1/(2*(A+1)))

theorem cutoffTimeFactor_pos (n : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    0 < cutoffTimeFactor n A := by unfold cutoffTimeFactor; positivity

theorem cutoffVolumeFloor_uniform (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    {R A : ℝ} (_ : 0 < R) (hcurv : |K| *R^2 ≤ A) :
    ((1/672:ℝ)/Real.exp (14*Real.sqrt A))^n ≤ cutoffVolumeFloor K n R := by
  have hn1 : (1:ℝ) ≤ (n:ℝ)-1 := by
    have hh : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hn0 : (0:ℝ) < (n:ℝ)-1 := by linarith
  have hk : 0 ≤ |K|/((n:ℝ)-1) := div_nonneg (abs_nonneg _) hn0.le
  have hs := Real.sq_sqrt hk
  have hdiv : |K|/((n:ℝ)-1) ≤ |K| := div_le_self (abs_nonneg _) hn1
  have hA : 0 ≤ A := (mul_nonneg (abs_nonneg _) (sq_nonneg _)).trans hcurv
  have hsq := Real.sq_sqrt hA
  have hmul := mul_le_mul_of_nonneg_left hdiv (sq_nonneg R)
  have hex : R*Real.sqrt (|K|/((n:ℝ)-1)) ≤ Real.sqrt A := by
    nlinarith [Real.sqrt_nonneg (|K|/((n:ℝ)-1)),Real.sqrt_nonneg A]
  have he : Real.exp (14*R*Real.sqrt (|K|/((n:ℝ)-1))) ≤ Real.exp (14*Real.sqrt A) :=
    Real.exp_le_exp.mpr (by linarith)
  apply pow_le_pow_left₀ (by positivity)
  exact div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) he

theorem cutoffTimeFactor_admissible (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    {R A : ℝ} (hR : 0 < R) (hcurv : |K| *R^2 ≤ A) :
    0 < R^2*cutoffTimeFactor n A ∧
      1/2 ≤ 1+K*(R^2*cutoffTimeFactor n A) ∧
      R^2*cutoffTimeFactor n A ≤ cutoffVolumeFloor K n R*R^2/1024 := by
  have hA : 0 ≤ A := (mul_nonneg (abs_nonneg _) (sq_nonneg _)).trans hcurv
  have ha := cutoffTimeFactor_pos n hA
  have hR2 : 0 < R^2 := sq_pos_of_pos hR
  have hsmall : cutoffTimeFactor n A ≤ 1/(2*(A+1)) := min_le_right _ _
  have haB : cutoffTimeFactor n A*(2*(A+1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hsmall
  have hh := mul_le_mul_of_nonneg_right hcurv ha.le
  have hneg := mul_le_mul_of_nonneg_right (neg_abs_le K) (mul_pos hR2 ha).le
  have hfloor := cutoffVolumeFloor_uniform K n hn hR hcurv
  have hsmall' : cutoffTimeFactor n A ≤ ((1/672:ℝ)/Real.exp (14*Real.sqrt A))^n/1024 := min_le_left _ _
  have hprod := mul_le_mul_of_nonneg_right ((hsmall'.trans
    (div_le_div_of_nonneg_right hfloor (by norm_num)))) hR2.le
  refine ⟨mul_pos hR2 ha,?_,?_⟩
  · nlinarith
  · nlinarith only [hprod]


end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
universe u

theorem exists_uniform_boundedLaplacian_cutoff_constant
    (n : ℕ) (hn : 2 ≤ n) (A : ℝ) (hA : 0 ≤ A) :
    ∃ CC : ℝ≥0, ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
      (K : ℝ) (hX : NoncollapsedRCD K n X) (p : X) {R : ℝ} (hR : 0 < R),
      |K| *R^2 ≤ A →
      letI : ProperSpace X := hX.proper K n hn
      letI : SeparableSpace X := hX.separable
      letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
      let μ := hausdorff n X
      ∃ (u : SobolevSpace μ hX.quadratic) (q : Lp ℝ 2 μ) (v : X → ℝ),
        IsWeakLaplacian μ hX.quadratic u q ∧ (∀ᵐ x ∂μ, |q x| ≤ (CC:ℝ)/R^2) ∧
        LipschitzWith (CC*⟨R⁻¹,inv_nonneg.mpr hR.le⟩) v ∧ HasCompactSupport v ∧
        SobolevSpace.toLp μ hX.quadratic u =ᵐ[μ] v ∧
        (∀ x, 0 ≤ v x ∧ v x ≤ 1) ∧
        (∀ x, dist p x ≤ R → v x=1) ∧
        (∀ x, 4*R ≤ dist p x → v x=0) := by
  obtain ⟨φ,ψ,χ,C,J,B,E,hφ,hψ,hχ,hdφ,hdψ,hB,hE,hφ0,hψ0,hφbounds,hφzero,hφone⟩ := exists_smooth_scalar_cutoff
  let aa : ℝ≥0 := ⟨cutoffTimeFactor n A,(cutoffTimeFactor_pos n hA).le⟩
  let CC : ℝ≥0 := (2*C+1)+(2*B/aa+4*E)
  refine ⟨CC,?_⟩
  intro X _ _ _ K hX p R hR hcurv
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let hQ := hX.quadratic
  have ht := cutoffTimeFactor_admissible K n hn hR hcurv
  obtain ⟨u,d,v,hud,hd,hv,hu,huM,happrox⟩ :=
    hX.quantitative_radial_resolvent K n hn p hR ht.1 ht.2.1 ht.2.2
  let D : ℝ≥0 := ⟨2/(R^2*cutoffTimeFactor n A),div_nonneg (by norm_num) ht.1.le⟩
  have hd' : ∀ᵐ x ∂μ, |d x| ≤ D := hd
  let a := SobolevSpace.comp μ hQ hφ hφ0 u
  have ha : SobolevSpace.toLp μ hQ a =ᵐ[μ] fun x => φ (v x) := by
    filter_upwards [SobolevSpace.comp_coe μ hQ hφ hφ0 u,hu] with x hx he
    exact hx.trans (congrArg φ he)
  have haB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ a x| ≤ (1:ℝ≥0) := by
    filter_upwards [ha] with x hx
    rw [hx,abs_of_nonneg (hφbounds _).1]
    exact (hφbounds _).2
  obtain ⟨q,hq,hqB⟩ := exists_boundedLaplacian_comp_C2 μ hQ u d hud hv hu hd'
    hφ hφ0 hψ hψ0 hχ hdφ hdψ B E hB hE
  let Q : ℝ≥0 := B*D+E*(2*⟨R⁻¹,inv_nonneg.mpr hR.le⟩)^2
  have hR2 : 0 < 2*R := by positivity
  let b := radialSobolevCutoff μ hQ p hR2
  let η := radialCutoff p (2*R)
  have hb : SobolevSpace.toLp μ hQ b =ᵐ[μ] η := radialSobolevCutoff_coe μ hQ p hR2
  have hη (x : X) : 0 ≤ η x ∧ η x ≤ 1 := radialCutoff_bounds p (2*R) x
  have hηabs (x : X) : |η x| ≤ (1:ℝ≥0) := by rw [abs_of_nonneg (hη x).1]; exact (hη x).2
  have hbB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ b x| ≤ (1:ℝ≥0) := hb.mono fun x hx => hx ▸ hηabs x
  have hplateau : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ a x=0 ∨
      SobolevSpace.toLp μ hQ b x=0 ∨ SobolevSpace.toLp μ hQ b x=1 := by
    filter_upwards [ha,hb] with x hx hy
    rw [hx,hy]
    by_cases hi : dist p x ≤ 2*R
    · exact Or.inr (Or.inr (radialCutoff_eq_one p hR2 hi))
    by_cases ho : 4*R ≤ dist p x
    · exact Or.inr (Or.inl (radialCutoff_eq_zero p hR2 (by linarith)))
    left
    have hc := happrox x (by linarith)
    rw [radialCutoff_eq_zero p hR (by linarith),sub_zero] at hc
    exact hφzero _ (by linarith [le_abs_self (v x)])
  let mult := boundedMultiplier μ η (radialCutoff_lipschitz p hR2).continuous.measurable 1 hηabs
  let dq := lpMultiplier μ mult q
  have hdq : ⇑dq =ᵐ[μ] fun x => η x*q x := by
    filter_upwards [lpMultiplier_coe μ mult q,boundedMultiplier_coe μ η
      (radialCutoff_lipschitz p hR2).continuous.measurable 1 hηabs] with x hx hy
    exact hx.trans (by rw [hy])
  let w := SobolevSpace.product μ hQ a b 1 1
  have hwd : IsWeakLaplacian μ hQ w dq := by
    apply weakLaplacian_product_plateau μ hQ a b q dq 1 1 haB hbB hq hplateau
    filter_upwards [hdq,hb] with x hx hy
    rw [hx,hy]
  let F (x : X) := η x*φ (v x)
  have hwe : SobolevSpace.toLp μ hQ w =ᵐ[μ] F := by
    filter_upwards [SobolevSpace.product_coe μ hQ a b 1 1 haB hbB,ha,hb] with x hx hax hbx
    rw [hx,hax,hbx]
    exact mul_comm _ _
  have hLL : LipschitzWith (1*(C*(2*⟨R⁻¹,inv_nonneg.mpr hR.le⟩))+
      1*⟨(2*R)⁻¹,inv_nonneg.mpr hR2.le⟩) F :=
    lipschitzWith_mul_of_support_bound (radialCutoff_lipschitz p hR2) (hφ.comp hv)
      hηabs (fun x _ => by rw [abs_of_nonneg (hφbounds _).1]; exact (hφbounds _).2)
  have hLbound : 1*(C*(2*⟨R⁻¹,inv_nonneg.mpr hR.le⟩))+
      1*⟨(2*R)⁻¹,inv_nonneg.mpr hR2.le⟩ ≤ CC*⟨R⁻¹,inv_nonneg.mpr hR.le⟩ := by
    let rL : ℝ≥0 := ⟨R⁻¹,inv_nonneg.mpr hR.le⟩
    let r2L : ℝ≥0 := ⟨(2*R)⁻¹,inv_nonneg.mpr hR2.le⟩
    have hc : (2*C+1:ℝ≥0) ≤ CC := le_add_of_nonneg_right (by positivity)
    have hi : r2L ≤ rL := by
      apply NNReal.coe_le_coe.mp
      change (2*R)⁻¹ ≤ R⁻¹
      exact inv_anti₀ hR (by linarith)
    change (1:ℝ≥0)*(C*(2*rL))+1*r2L ≤ CC*rL
    simp only [one_mul]
    calc
      C*(2*rL)+r2L ≤ C*(2*rL)+rL := add_le_add le_rfl hi
      _ = (2*C+1)*rL := by ring
      _ ≤ _ := mul_le_mul' hc le_rfl
  have hQbound : (Q:ℝ) ≤ (CC:ℝ)/R^2 := by
    have hc : (2*B/aa+4*E:ℝ≥0) ≤ CC := le_add_of_nonneg_left (by positivity)
    have hc' := NNReal.coe_le_coe.mpr hc
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_div,NNReal.coe_ofNat] at hc'
    have heq : (Q:ℝ) = ((2:ℝ)*B/cutoffTimeFactor n A+4*E)/R^2 := by
      change (B:ℝ)*(2/(R^2*cutoffTimeFactor n A))+(E:ℝ)*(2*R⁻¹)^2 = _
      field_simp [hR.ne',(cutoffTimeFactor_pos n hA).ne']
      ; ring
    rw [heq]
    exact div_le_div_of_nonneg_right hc' (sq_nonneg R)
  refine ⟨w,dq,F,hwd,?_,hLL.weaken hLbound,(radialCutoff_hasCompactSupport p hR2).mul_right,hwe,?_,?_,?_⟩
  · filter_upwards [hdq,hqB] with x hx hqB
    rw [hx,abs_mul]
    exact ((mul_le_mul (hηabs x) hqB (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)).trans hQbound
  · intro x
    exact ⟨mul_nonneg (hη x).1 (hφbounds _).1,
      (mul_le_mul (hη x).2 (hφbounds _).2 (hφbounds _).1 zero_le_one).trans_eq (one_mul _)⟩
  · intro x hx
    have hi : η x=1 := radialCutoff_eq_one p hR2 (by linarith)
    have hc := happrox x (by linarith)
    rw [radialCutoff_eq_one p hR hx] at hc
    exact show η x*φ (v x)=1 from by rw [hi,hφone _ (by linarith),one_mul]
  · intro x hx
    have hi : η x=0 := radialCutoff_eq_zero p hR2 (by linarith)
    exact show η x*φ (v x)=0 from by rw [hi,zero_mul]


end RegularPointCoordinates

end OAI
