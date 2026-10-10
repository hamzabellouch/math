import Mathlib
import OAI.Probability.Perceptron.Variational.BackwardScore
import OAI.Probability.Perceptron.Variational.FieldRounding

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cdfIndicator (a t : Time) : ℝ := if a≤t then 1 else 0

lemma cdfIndicator_integrable (a : Time) : Integrable (cdfIndicator a) timeLaw := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    ((measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const).aestronglyMeasurable)
  exact ae_of_all _ fun _ => by split_ifs <;> norm_num

lemma cdfIndicator_integral (a : Time) : (∫ t, cdfIndicator a t ∂timeLaw)=1-(a:ℝ) := by
  have he := timeTail_atom_integral a 0 1
  rw [show Ici (0:Time)=univ from Ici_bot,Measure.restrict_univ] at he
  change (∫ s, (if a ≤ s then (1:ℝ) else 0) ∂timeLaw)=1*(1-max (a:ℝ) 0) at he
  simpa only [cdfIndicator,one_mul,max_eq_left a.2.1] using he

lemma cdfIndicator_order {a b : Time} (hab : a≤b) (t : Time) : cdfIndicator b t≤cdfIndicator a t := by
  unfold cdfIndicator
  by_cases hb : b≤t
  · rw [ite_eq_left hb,ite_eq_left (hab.trans hb)]
  · rw [ite_eq_right hb]
    split_ifs <;> norm_num

lemma cdfIndicator_abs_integral (a b : Time) :
    (∫ t, |cdfIndicator a t-cdfIndicator b t| ∂timeLaw)=|(a:ℝ)-b| := by
  have hle {a b : Time} (hab : a≤b) :
      (∫ t, |cdfIndicator a t-cdfIndicator b t| ∂timeLaw)=(b:ℝ)-a := by
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (cdfIndicator_order hab _))]
    rw [integral_sub (cdfIndicator_integrable a) (cdfIndicator_integrable b),
      cdfIndicator_integral,cdfIndicator_integral]
    ring
  rcases le_total a b with hab | hba
  · rw [hle hab,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (show (a:ℝ)≤b from hab))]
  · simp_rw [abs_sub_comm (cdfIndicator a _) (cdfIndicator b _)]
    rw [hle hba,abs_of_nonneg (sub_nonneg.mpr (show (b:ℝ)≤a from hba))]

lemma quantileTrial_L1_le (q r : Time→Time) (hq : Measurable q) (hr : Measurable r) :
    (∫ t, |quantileTrial q t-quantileTrial r t| ∂timeLaw)≤
      ∫ u, |(q u:ℝ)-r u| ∂timeLaw := by
  let F := fun p : Time×Time => |cdfIndicator (q p.2) p.1-cdfIndicator (r p.2) p.1|
  have hmq : Measurable (fun p : Time×Time => cdfIndicator (q p.2) p.1) :=
    measurable_const.ite (measurableSet_le (hq.comp measurable_snd) measurable_fst) measurable_const
  have hmr : Measurable (fun p : Time×Time => cdfIndicator (r p.2) p.1) :=
    measurable_const.ite (measurableSet_le (hr.comp measurable_snd) measurable_fst) measurable_const
  have hF : Integrable F (timeLaw.prod timeLaw) := by
    apply Integrable.mono' (integrable_const (1:ℝ)) ((hmq.sub hmr).abs.aestronglyMeasurable)
    exact ae_of_all _ fun p => by dsimp [F,cdfIndicator]; split_ifs <;> norm_num
  have hpoint (t : Time) : |quantileTrial q t-quantileTrial r t|≤∫ u, F (t,u) ∂timeLaw := by
    rw [quantileTrial_eq_integral q hq,quantileTrial_eq_integral r hr]
    have hi (v : Time→Time) (hv : Measurable v) :
        Integrable (fun u => if v u≤t then (1:ℝ) else 0) timeLaw := by
      apply Integrable.mono' (integrable_const (1:ℝ))
        ((measurable_const.ite (measurableSet_le hv measurable_const) measurable_const).aestronglyMeasurable)
      exact ae_of_all _ fun _ => by split_ifs <;> norm_num
    rw [← integral_sub (hi q hq) (hi r hr)]
    simpa only [Real.norm_eq_abs,F,cdfIndicator] using (norm_integral_le_integral_norm
      (fun u : Time => (if q u≤t then (1:ℝ) else 0)-(if r u≤t then (1:ℝ) else 0)))
  calc
    _ ≤ ∫ t, ∫ u, F (t,u) ∂timeLaw ∂timeLaw :=
      integral_mono ((trial_integrable (quantileTrial q)).sub (trial_integrable (quantileTrial r))).abs
        hF.integral_prod_left hpoint
    _ = ∫ u, |(q u:ℝ)-r u| ∂timeLaw := by
      rw [integral_integral_swap hF]
      exact integral_congr_ae (ae_of_all _ fun u => cdfIndicator_abs_integral (q u) (r u))

theorem controlValue_quantile_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (g : Jet3) (q r : Time→Time) (hq : Measurable q) (hr : Measurable r) :
    |controlValue P g.f (quantileTrial q)-controlValue P g.f (quantileTrial r)|≤
      (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*∫ u, |(q u:ℝ)-r u| ∂timeLaw := by
  apply (controlValue_trial_abs_sub_le P g.f _ _ ‖g.d1‖₊ g.lipschitz).trans
  exact mul_le_mul_of_nonneg_left (quantileTrial_L1_le q r hq hr) (by positivity)

end SphericalPerceptronFreeEnergy
end

end OAI
