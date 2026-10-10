import OAI.Probability.DilutedSpin.CavityBounds

namespace OAI

section
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

namespace DilutedSpinGlass.MeasureMean

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Logarithmic conditional power mean, for an arbitrary Borel probability law. -/
noncomputable def logMean (m : ℝ) (f : Ω → ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (m * f x) ∂μ) / m

theorem bounded_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) : Integrable f μ :=
  (integrable_const B).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))

theorem exp_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) (m : ℝ) : Integrable (fun x => Real.exp (m*f x)) μ := by
  apply bounded_integrable μ (hf.const_mul m).exp
  intro x
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc m*f x ≤ |m*f x| := le_abs_self _
       _ = |m| * |f x| := abs_mul _ _
       _ ≤ |m| * B := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

theorem exp_integral_pos {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) (m : ℝ) : 0 < ∫ x, Real.exp (m*f x) ∂μ :=
  integral_exp_pos (exp_integrable μ hf hb m)

theorem logMean_const {m : ℝ} (hm : m ≠ 0) (a : ℝ) :
    logMean μ m (fun _ => a) = a := by
  simp [logMean, Real.log_exp, hm]

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} {B C : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfb : ∀ x, |f x| ≤ B)
    (hgb : ∀ x, |g x| ≤ C) (hfg : ∀ x, f x ≤ g x) :
    logMean μ m f ≤ logMean μ m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (exp_integral_pos μ hf hfb m)
  exact integral_mono (exp_integrable μ hf hfb m) (exp_integrable μ hg hgb m)
    (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hfg x) hm.le))

theorem logMean_add_const {m : ℝ} (hm : m ≠ 0) {f : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) (a : ℝ) :
    logMean μ m (fun x => f x+a) = logMean μ m f+a := by
  unfold logMean
  simp_rw [mul_add, Real.exp_add]
  rw [integral_mul_const, Real.log_mul (ne_of_gt (exp_integral_pos μ hf hb m))
    (Real.exp_ne_zero _), Real.log_exp]
  field_simp

theorem logMean_stability {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} {B C D : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfb : ∀ x, |f x| ≤ B)
    (hgb : ∀ x, |g x| ≤ C) (hfg : ∀ x, |f x-g x| ≤ D) :
    |logMean μ m f-logMean μ m g| ≤ D := by
  have haddb (g : Ω → ℝ) (C : ℝ) (hg : ∀ x, |g x| ≤ C) (x : Ω) :
      |g x+D| ≤ C+|D| := (abs_add_le _ _).trans (add_le_add (hg x) le_rfl)
  have h1 := logMean_mono μ hm hf (hg.add_const D) hfb (haddb g C hgb)
    (fun x => by have := (abs_le.mp (hfg x)).2; linarith)
  have h2 := logMean_mono μ hm hg (hf.add_const D) hgb (haddb f B hfb)
    (fun x => by have := (abs_le.mp (hfg x)).1; linarith)
  rw [logMean_add_const μ hm.ne' hg hgb] at h1
  rw [logMean_add_const μ hm.ne' hf hfb] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem logMean_bound {m : ℝ} (hm : 0 < m) {f : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) : |logMean μ m f| ≤ B := by
  have h := logMean_stability μ hm hf measurable_const hb
    (fun _ => (by simp : |(0 : ℝ)| ≤ 0)) (by simpa using hb)
  simpa only [logMean_const μ hm.ne', sub_zero] using h

/-- The exact one-level insertion identity, not restricted to finite priors.
The tilted law is Mathlib's normalized exponential tilted measure. -/
theorem insertion {m : ℝ} (_hm : m ≠ 0) {f a : Ω → ℝ} {B C : ℝ}
    (hf : Measurable f) (ha : Measurable a) (hfb : ∀ x, |f x| ≤ B)
    (hab : ∀ x, |a x| ≤ C) :
    logMean μ m (fun x => f x+a x) - logMean μ m f =
      logMean (μ.tilted (fun x => m*f x)) m a := by
  have hfab (x : Ω) : |f x+a x| ≤ B+C :=
    (abs_add_le _ _).trans (add_le_add (hfb x) (hab x))
  unfold logMean
  rw [integral_exp_tilted]
  have heq : (fun x => m*f x) + (fun x => m*a x) = (fun x => m*(f x+a x)) := by
    funext x
    simp [mul_add]
  rw [heq, Real.log_div (ne_of_gt (exp_integral_pos μ (f := fun x => f x+a x) (hf.add ha) hfab m))
    (ne_of_gt (exp_integral_pos μ hf hfb m)), sub_div]

/-- The updated probability kernel is the same whether insertions are made
successively or together. -/
theorem tilt_insertion {m : ℝ} {f a : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hfb : ∀ x, |f x| ≤ B) :
    (μ.tilted (fun x => m*f x)).tilted (fun x => m*a x) =
      μ.tilted (fun x => m*(f x+a x)) := by
  rw [tilted_tilted (exp_integrable μ hf hfb m)]
  congr 1
  funext x
  simp [mul_add]

end DilutedSpinGlass.MeasureMean

namespace DilutedSpinGlass
local instance measureHierarchyContinuousMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space
local instance measureHierarchyContinuousBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem logMean_continuous_bound {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x| ≤ B)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) :
    Continuous (logMean r g m) ∧ ∀ eta, |logMean r g m eta| ≤ B := by
  induction r with
  | zero => exact ⟨hg, hB⟩
  | succ r ih =>
    obtain ⟨hc, hb⟩ := ih (fun i => m i.succ) (fun i => hm i.succ)
    let f := logMean r g (fun i => m i.succ)
    let F : (ι → Hierarchy r) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => Real.exp (m 0 * f x)) (Real.continuous_exp.comp (hc.const_mul (m 0)))
      (Real.exp (|m 0| * B)) (fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        exact (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact hb x))
    have hpos (eta : ι → Hierarchy (r+1)) : 0 < ∫ x, F x ∂(ProbabilityMeasure.pi eta) :=
      MeasureMean.exp_integral_pos (ProbabilityMeasure.pi eta).toMeasure hc.measurable hb (m 0)
    have hcont : Continuous (fun eta : ι → Hierarchy (r+1) => ∫ x, F x ∂(ProbabilityMeasure.pi eta)) :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).comp
        ProbabilityMeasure.continuous_pi
    refine ⟨(hcont.log (fun eta => (hpos eta).ne')).div_const (m 0), ?_⟩
    intro eta
    exact MeasureMean.logMean_bound (ProbabilityMeasure.pi eta).toMeasure (hm 0) hc.measurable hb

 theorem trialLog_continuous_bound {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x| ≤ B)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) :
    Continuous (fun ζ => trialLog r ζ m g) ∧ ∀ ζ, |trialLog r ζ m g| ≤ B := by
  obtain ⟨hc,hb⟩ := logMean_continuous_bound r g hg hB m hm
  let F : (ι → Hierarchy r) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (logMean r g m) hc B (fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hpi : Continuous (fun ζ : Hierarchy (r+1) => ProbabilityMeasure.pi (fun _ : ι => ζ)) :=
    ProbabilityMeasure.continuous_pi.comp (continuous_pi (fun _ => continuous_id))
  refine ⟨(ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).comp hpi, ?_⟩
  intro ζ
  change |∫ x, F x ∂(ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure| ≤ B
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := (ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure)
      (ae_of_all _ (fun x => (show ‖F x‖ ≤ B from by simpa [F] using hb x))))

end DilutedSpinGlass

namespace DilutedSpinGlass
local instance measureHierarchyStabilityMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space
local instance measureHierarchyStabilityBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem logMean_stability {ι : Type} [Fintype ι] (r : ℕ)
    (f g : (ι → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) {B C D : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) (hD : ∀ x, |f x-g x| ≤ D)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (eta : ι → Hierarchy r) :
    |logMean r f m eta-logMean r g m eta| ≤ D := by
  induction r with
  | zero => exact hD eta
  | succ r ih =>
    obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hB (fun i => m i.succ) (fun i => hm i.succ)
    obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hC (fun i => m i.succ) (fun i => hm i.succ)
    exact MeasureMean.logMean_stability (ProbabilityMeasure.pi eta).toMeasure (hm 0)
      hfc.measurable hgc.measurable hfb hgb (ih (fun i => m i.succ) (fun i => hm i.succ))

theorem trialLog_stability {ι : Type} [Fintype ι] (r : ℕ)
    (f g : (ι → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) {B C D : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) (hD : ∀ x, |f x-g x| ≤ D)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m f-trialLog r ζ m g| ≤ D := by
  obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hB m hm
  obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hC m hm
  let μ := (ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure
  have hiF : Integrable (logMean r f m) μ := MeasureMean.bounded_integrable μ hfc.measurable hfb
  have hiG : Integrable (logMean r g m) μ := MeasureMean.bounded_integrable μ hgc.measurable hgb
  change |(∫ eta, logMean r f m eta ∂μ)-(∫ eta, logMean r g m eta ∂μ)| ≤ D
  rw [← integral_sub hiF hiG]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ (fun eta =>
      (show ‖logMean r f m eta - logMean r g m eta‖ ≤ D from by
        simpa only [Real.norm_eq_abs] using logMean_stability r f g hf hg hB hC hD m hm eta)))

 theorem continuous_q (s : Spin) : Continuous (fun x => q x s) := by
  unfold q
  apply (Real.continuous_exp.comp (continuous_id.mul continuous_const)).div
    (continuous_const.mul Real.continuous_cosh)
  intro x
  exact mul_ne_zero (by norm_num) (Real.cosh_pos x).ne'

 theorem continuous_edge {p : ℕ} (theta : Interaction p) : Continuous (edge theta) := by
  unfold edge
  apply continuous_finsetSum
  intro s _
  apply continuous_const.mul
  exact continuous_finsetProd _ (fun l _ => (continuous_q (s l)).comp (continuous_apply l))

 theorem continuous_log_edge {p : ℕ} (theta : Interaction p) :
    Continuous (fun x => Real.log (edge theta x)) :=
  (continuous_edge theta).log (fun x => (edge_pos theta x).ne')

 theorem continuous_message {p : ℕ} (theta : Interaction p) (ε : Spin) :
    Continuous (fun x => message theta x ε) := by
  unfold message
  apply Continuous.log
  · apply continuous_finsetSum
    intro s _
    apply continuous_const.mul
    exact continuous_finsetProd _ (fun l _ => (continuous_q (s l)).comp (continuous_apply l))
  · intro x
    apply ne_of_gt
    apply Finset.sum_pos
    · intro s _
      exact mul_pos (Real.exp_pos _) (Finset.prod_pos (fun l _ => q_pos _ _))
    · exact Finset.univ_nonempty

 theorem continuous_siteLog {p k : ℕ} (theta : Fin k → InteractionSample p) (h : ℝ) :
    Continuous (siteLog theta h) := by
  unfold siteLog
  apply Continuous.log
  · apply Continuous.div_const
    apply continuous_finsetSum
    intro ε _
    apply Real.continuous_exp.comp
    apply continuous_const.add
    apply continuous_finsetSum
    intro j _
    exact (continuous_message (theta j).1 ε).comp
      (continuous_pi (fun l => continuous_apply (j,l)))
  · intro x
    apply ne_of_gt
    exact div_pos (sum_exp_pos _) (by norm_num)

end DilutedSpinGlass

namespace DilutedSpinGlass

theorem weighted_exp_pos {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    0 < ∑ i, w i * Real.exp (f i) :=
  (Real.exp_pos (-‖f‖)).trans_le
    (weighted_exp_bounds w f hw hs (fun i => norm_le_pi_norm f i)).1

/-- Stability before any disorder averaging; no lower bound on the positive
message probabilities or moment condition on the messages occurs. -/
theorem weighted_log_exp_stability {ι : Type*} [Fintype ι] (w f g : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {D : ℝ}
    (hD : ∀ i, |f i-g i| ≤ D) :
    |Real.log (∑ i, w i * Real.exp (f i)) -
      Real.log (∑ i, w i * Real.exp (g i))| ≤ D := by
  have aux (f g : ι → ℝ) (h : ∀ i, f i ≤ g i+D) :
      Real.log (∑ i, w i * Real.exp (f i)) ≤
        Real.log (∑ i, w i * Real.exp (g i)) + D := by
    have hle : (∑ i, w i * Real.exp (f i)) ≤
        (∑ i, w i * Real.exp (g i)) * Real.exp D := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => by
        rw [mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h i)) (hw i))
    have hl := Real.log_le_log (weighted_exp_pos w f hw hs) hle
    rw [Real.log_mul (weighted_exp_pos w g hw hs).ne' (Real.exp_pos D).ne', Real.log_exp] at hl
    exact hl
  have hfg := aux f g (fun i => by have h := (abs_le.mp (hD i)).2; linarith)
  have hgf := aux g f (fun i => by have h := (abs_le.mp (hD i)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem log_edge_stability {p : ℕ} (theta theta' : Interaction p) (x : Fin p → ℝ) :
    |Real.log (edge theta x)-Real.log (edge theta' x)| ≤ ‖theta-theta'‖ := by
  simpa only [edge, mul_comm] using
    weighted_log_exp_stability (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta theta'
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm (theta-theta') s)

theorem message_stability {p : ℕ} (theta theta' : Interaction p)
    (x : Fin (p-1) → ℝ) (ε : Spin) :
    |message theta x ε-message theta' x ε| ≤ ‖theta-theta'‖ := by
  simpa only [message, mul_comm] using
    weighted_log_exp_stability (fun s : Fin (p-1) → Spin => ∏ l, q (x l) (s l))
      (fun s => theta (appendSpin s ε)) (fun s => theta' (appendSpin s ε))
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm (theta-theta') (appendSpin s ε))

theorem siteLog_stability {p k : ℕ} (theta theta' : Fin k → InteractionSample p) (h h' : ℝ)
    (x : (Fin k × Fin (p-1)) → ℝ) :
    |siteLog theta h x - siteLog theta' h' x| ≤
      |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ := by
  have hf : ∀ ε : Spin,
      |(h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε) -
        (h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε)| ≤
        |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ := by
    intro ε
    rw [show (h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε) -
        (h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε) =
        (h-h') * spin ε + ∑ j, (message (theta j).1 (fun l => x (j,l)) ε -
          message (theta' j).1 (fun l => x (j,l)) ε) by rw [Finset.sum_sub_distrib]; ring]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · simp only [abs_mul, abs_spin, mul_one, le_refl]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ => message_stability _ _ _ _))
  have hw : (∑ _ε : Spin, (1/2 : ℝ)) = 1 := by norm_num [Fintype.sum_bool]
  have hb := weighted_log_exp_stability (fun _ε : Spin => (1/2 : ℝ))
    (fun ε => h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε)
    (fun ε => h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε)
    (fun _ => by norm_num) hw hf
  simpa only [siteLog, ← Finset.mul_sum, one_div, div_eq_mul_inv, one_mul, mul_comm] using hb

local instance measureHierarchyTrialMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space
local instance measureHierarchyTrialBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem trial_edge_stability {p : ℕ} (r : ℕ) (theta theta' : Interaction p)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m (fun x => Real.log (edge theta x)) -
      trialLog r ζ m (fun x => Real.log (edge theta' x))| ≤ ‖theta-theta'‖ :=
  trialLog_stability r _ _ (continuous_log_edge theta) (continuous_log_edge theta')
    (log_edge_bound theta) (log_edge_bound theta') (log_edge_stability theta theta') m hm ζ

theorem trial_site_stability {p k : ℕ} (r : ℕ)
    (theta theta' : Fin k → InteractionSample p) (h h' : ℝ)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m (siteLog theta h)-trialLog r ζ m (siteLog theta' h')| ≤
      |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ :=
  trialLog_stability r _ _ (continuous_siteLog theta h) (continuous_siteLog theta' h')
    (siteLog_bound theta h) (siteLog_bound theta' h') (siteLog_stability theta theta' h h') m hm ζ

end DilutedSpinGlass

end

end OAI
