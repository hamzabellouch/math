import Mathlib
import OAI.Probability.SphericalField.Perceptron.TimeLaw
import OAI.Probability.SphericalField.Control.Independence

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma controlCost_clip_le (P : Measure BrownianPath) (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) : controlCost P m (clipControl L v) ≤ controlCost P m v :=
  lintegral_mono fun ω => pathControlCost_clip_le m hL v ω

lemma weightedTime_integrable (m : Trial) {v : Time → ℝ} (hv : Measurable v)
    (hc : (∫⁻ t, ENNReal.ofReal (m t * v t ^ 2) ∂timeLaw) < ∞) :
    Integrable (fun t => m t * v t ^ 2) timeLaw ∧
      Integrable (fun t => m t * v t) timeLaw := by
  have hm : Integrable m timeLaw :=
    (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simpa [abs_of_nonneg (m.nonneg t)] using m.le_one t)
  have hq : Integrable (fun t => m t * v t ^ 2) timeLaw :=
    ⟨(m.measurable.mul (hv.pow_const 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t =>
        mul_nonneg (m.nonneg t) (sq_nonneg _))).mpr hc⟩
  refine ⟨hq, (hq.add hm).mono' (m.measurable.mul hv).aestronglyMeasurable ?_⟩
  apply Filter.Eventually.of_forall
  intro t
  change |m t * v t| ≤ m t * v t ^ 2 + m t
  rw [abs_mul, abs_of_nonneg (m.nonneg t)]
  have h : |v t| ≤ v t ^ 2 + 1 := by nlinarith [sq_nonneg (|v t| - 1), sq_abs (v t)]
  nlinarith [mul_le_mul_of_nonneg_left h (m.nonneg t)]

lemma integral_pathControlCost (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    (∫ ω, (pathControlCost m v ω).toReal ∂P) = (controlCost P m v).toReal :=
  integral_toReal (pathControlCost_aemeasurable P m hv)
    (ae_lt_top' (pathControlCost_aemeasurable P m hv) hc.ne)

lemma clipping_drift_gain (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    {v : Time → BrownianPath → ℝ} (ω : BrownianPath)
    (hv : Measurable (fun t => v t ω)) (hc : pathControlCost m v ω < ∞) :
    L * |controlDrift m v ω - controlDrift m (clipControl L v) ω| ≤
      ((pathControlCost m v ω).toReal - (pathControlCost m (clipControl L v) ω).toReal)/2 := by
  have hw : Measurable (fun t => clipControl L v t ω) := measurable_const.max (measurable_const.min hv)
  have hcv := weightedTime_integrable m hv hc
  have hcw := weightedTime_integrable m hw ((pathControlCost_clip_le m hL v ω).trans_lt hc)
  have hev : (∫ t, m t * v t ω ^ 2 ∂timeLaw) = (pathControlCost m v ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcv.1.aestronglyMeasurable
  have hew : (∫ t, m t * clipControl L v t ω ^ 2 ∂timeLaw) =
      (pathControlCost m (clipControl L v) ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcw.1.aestronglyMeasurable
  unfold controlDrift
  rw [← integral_sub hcv.2 hcw.2]
  calc
    _ ≤ L * ∫ t, |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hL
    _ = ∫ t, L * |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ t, (m t * v t ω ^ 2 - m t * clipControl L v t ω ^ 2)/2 ∂timeLaw := by
      apply integral_mono ((hcv.2.sub hcw.2).abs.const_mul L) ((hcv.1.sub hcw.1).div_const 2)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← mul_sub, abs_mul, abs_of_nonneg (m.nonneg t)]
      have h := mul_le_mul_of_nonneg_left (clip_cost_gain hL (v t ω)) (m.nonneg t)
      dsimp [clipControl]
      nlinarith
    _ = _ := by rw [integral_div, integral_sub hcv.1 hcw.1, hev, hew]

lemma controlPayoff_le_clipControl (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    controlPayoff P f m v ≤ controlPayoff P f m (clipControl L v) := by
  let w := clipControl L v
  have hw : Progressive P w := progressive_clipControl P hv L
  have hcw : controlCost P m w < ∞ := (controlCost_clip_le P m L.coe_nonneg v).trans_lt hc
  have hpv := pathControlCost_aemeasurable P m hv
  have hpw := pathControlCost_aemeasurable P m hw
  have hcvI := integrable_toReal_of_lintegral_ne_top hpv hc.ne
  have hcwI := integrable_toReal_of_lintegral_ne_top hpw hcw.ne
  have hineq : (∫ ω, (f (brownianEval 1 ω + controlDrift m v ω) -
        f (brownianEval 1 ω + controlDrift m w ω)) ∂P) ≤
      (∫ ω, ((pathControlCost m v ω).toReal - (pathControlCost m w ω).toReal)/2 ∂P) := by
    apply integral_mono_ae ((controlReward_integrable P f m hv).sub (controlReward_integrable P f m hw))
      ((hcvI.sub hcwI).div_const 2)
    filter_upwards [ae_lt_top' hpv hc.ne] with ω hω
    have hLip := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
      (brownianEval 1 ω + controlDrift m w ω)
    rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hLip
    exact (le_abs_self _).trans (hLip.trans
      (clipping_drift_gain m L.coe_nonneg ω (progressive_time_measurable P hv ω) hω))
  rw [integral_sub (controlReward_integrable P f m hv) (controlReward_integrable P f m hw),
    integral_div, integral_sub hcvI hcwI, integral_pathControlCost P m hv hc,
    integral_pathControlCost P m hw hcw] at hineq
  unfold controlPayoff
  change _ ≤ _
  dsimp only [controlDrift, w] at hineq
  linarith

lemma controlValue_le_of_bounded_controls (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) (b : ℝ)
    (hb : ∀ v : Time → BrownianPath → ℝ, Progressive P v → controlCost P m v < ∞ →
      (∀ t ω, |v t ω| ≤ L) → controlPayoff P f m v ≤ b) : controlValue P f m ≤ b := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, hv, hc, rfl⟩
  exact (controlPayoff_le_clipControl P f m L hf hv hc).trans
    (hb (clipControl L v) (progressive_clipControl P hv L)
      ((controlCost_clip_le P m L.coe_nonneg v).trans_lt hc)
      (fun t ω => abs_clip_le L.coe_nonneg (v t ω)))

lemma pathControlCost_le_bound (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath) :
    pathControlCost m v ω ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _t : Time, ENNReal.ofReal ((L : ℝ)^2) ∂timeLaw := by
      apply lintegral_mono
      intro t
      apply ENNReal.ofReal_le_ofReal
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      exact (mul_le_mul_of_nonneg_right (m.le_one t) (sq_nonneg _)).trans (by simpa using hx)
    _ = _ := by simp

lemma controlCost_le_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) :
    controlCost P m v ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _ω : BrownianPath, ENNReal.ofReal ((L : ℝ)^2) ∂P :=
      lintegral_mono fun ω => pathControlCost_le_bound m L hv ω
    _ = _ := by simp

lemma trial_abs_sub_integrable (m n : Trial) :
    Integrable (fun t => |m t - n t|) timeLaw := by
  apply (integrable_const (2 : ℝ)).mono'
    ((m.measurable.sub n.measurable).abs.aestronglyMeasurable)
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_abs]
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg (m.nonneg t), abs_of_nonneg (n.nonneg t)]; linarith [m.le_one t,n.le_one t])

lemma bounded_drift_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |controlDrift m v ω - controlDrift n v ω| ≤ (L : ℝ) * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  rw [controlDrift, controlDrift, ← integral_sub hm.2 hn.2]
  calc
    _ ≤ ∫ t, |m t * v t ω - n t * v t ω| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ) * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.2.sub hn.2).abs ((trial_abs_sub_integrable m n).const_mul L)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hv t ω) (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma bounded_pathCost_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ≤
      (L : ℝ)^2 * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  have hem : (pathControlCost m v ω).toReal = ∫ t, m t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hm.1.aestronglyMeasurable).symm
  have hen : (pathControlCost n v ω).toReal = ∫ t, n t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (n.nonneg t) (sq_nonneg _))
      hn.1.aestronglyMeasurable).symm
  rw [hem, hen, ← integral_sub hm.1 hn.1]
  calc
    _ ≤ ∫ t, |m t * v t ω ^ 2 - n t * v t ω ^ 2| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ)^2 * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.1.sub hn.1).abs ((trial_abs_sub_integrable m n).const_mul ((L : ℝ)^2))
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (v t ω))]
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma controlPayoff_trial_diff_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hbound : ∀ t ω, |v t ω| ≤ L) :
    |controlPayoff P f m v - controlPayoff P f n v| ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  let D := ∫ t, |m t-n t| ∂timeLaw
  have hcm : controlCost P m v < ∞ := (controlCost_le_bound P m L hbound).trans_lt (by finiteness)
  have hcn : controlCost P n v < ∞ := (controlCost_le_bound P n L hbound).trans_lt (by finiteness)
  have hm := controlReward_integrable P f m hv
  have hn := controlReward_integrable P f n hv
  have hrew : |(∫ ω, f (brownianEval 1 ω + controlDrift m v ω) ∂P) -
      (∫ ω, f (brownianEval 1 ω + controlDrift n v ω) ∂P)| ≤ (L : ℝ)^2 * D := by
    rw [← integral_sub hm hn]
    calc
      _ ≤ ∫ ω, |f (brownianEval 1 ω + controlDrift m v ω) -
          f (brownianEval 1 ω + controlDrift n v ω)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono (hm.sub hn).abs (integrable_const _)
        intro ω
        have hh := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
          (brownianEval 1 ω + controlDrift n v ω)
        rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hh
        have hb := mul_le_mul_of_nonneg_left
          (bounded_drift_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)) L.coe_nonneg
        exact hh.trans (by dsimp only [D]; nlinarith [hb])
      _ = _ := by simp
  have hcost : |(controlCost P m v).toReal - (controlCost P n v).toReal| ≤ (L : ℝ)^2 * D := by
    rw [← integral_pathControlCost P m hv hcm, ← integral_pathControlCost P n hv hcn,
      ← integral_sub (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne)
        (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)]
    calc
      _ ≤ ∫ ω, |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono
          ((integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne).sub
            (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)).abs
          (integrable_const _)
        intro ω
        exact bounded_pathCost_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)
      _ = _ := by simp
  apply abs_le.mpr
  obtain ⟨hrewlo,hrewhi⟩ := abs_le.mp hrew
  obtain ⟨hcostlo,hcosthi⟩ := abs_le.mp hcost
  dsimp only [controlPayoff, controlDrift] at *
  constructor <;> linarith

end SphericalPerceptron
end
end

end OAI
