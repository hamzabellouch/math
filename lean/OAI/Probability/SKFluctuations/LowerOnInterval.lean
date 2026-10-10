import Mathlib
import OAI.Probability.SKFluctuations.StandardCompletedLawIsOpenPos

namespace OAI

/-! Lower On Interval. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.PreKopa.Density
open ProbabilityTheory

theorem lower_on_interval (d : Density) {a b x c : ℝ} (hab : a < b)
    (hx : x ∈ Set.Icc a b) (hc : 0 < c) (ha : c ≤ d.f a) (hb : c ≤ d.f b) :
    c ≤ d.f x := by
  let t : ℝ := (x - a) / (b - a)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])
  have h := (d.lc.concaveOn_log d.pos).2 (Set.mem_univ a) (Set.mem_univ b)
    (show 0 ≤ 1 - t by linarith) ht (by ring : 1 - t + t = 1)
  have heq : (1 - t) * a + t * b = x := by dsimp [t]; field_simp [(sub_pos.mpr hab).ne']; ring
  simp only [smul_eq_mul, heq] at h
  have hra := Real.log_le_log hc ha
  have hrb := Real.log_le_log hc hb
  have hla := mul_le_mul_of_nonneg_left hra (show 0 ≤ 1 - t by linarith)
  have hlb := mul_le_mul_of_nonneg_left hrb ht
  exact (Real.log_le_log_iff hc (d.pos x)).mp (by nlinarith)

theorem point_half_drop (d : Density) (a : ℝ) :
    d.f (a + 4 / d.f a) < d.f a / 2 := by
  have hM := d.pos a
  have hr : 0 < 4 / d.f a := div_pos (by norm_num) hM
  by_contra! h
  have hi : IntegrableOn (fun _ : ℝ => d.f a / 2) (Set.Icc a (a + 4 / d.f a)) :=
    continuous_const.integrableOn_Icc
  have hb := setIntegral_mono_on hi d.integrable.integrableOn measurableSet_Icc
    (fun x hx => d.lower_on_interval (by linarith) hx (by positivity) (by linarith) h)
  rw [setIntegral_const, smul_eq_mul, d.setIntegral_eq_measureReal measurableSet_Icc] at hb
  have hv : volume.real (Set.Icc a (a + 4 / d.f a)) = 4 / d.f a := by
    simp [Measure.real, Real.volume_Icc, hr.le]
  rw [hv] at hb
  have hprob : d.law.real (Set.Icc a (a + 4 / d.f a)) ≤ 1 := measureReal_le_one
  have heq : 4 / d.f a * (d.f a / 2) = 2 := by field_simp; ring
  rw [heq] at hb
  linarith

theorem point_right_tail (d : Density) (a y : ℝ) (hy : 4 / d.f a ≤ y) :
    d.f (a + y) ≤ d.f a * Real.exp (-tailRate * d.f a * y) := by
  have hM := d.pos a
  have hr : 0 < 4 / d.f a := div_pos (by norm_num) hM
  have hb := d.point_half_drop a
  have hlog : Real.log (d.f (a + 4 / d.f a)) ≤ Real.log (d.f a) - Real.log 2 := by
    have h := Real.log_le_log (d.pos _) hb.le
    rwa [Real.log_div hM.ne' (by norm_num)] at h
  have hs := logConcave_secant d.lc d.pos (a := a) (b := a + 4 / d.f a)
    (x := a + y) (by linarith) (by linarith)
  have hratio : (Real.log (d.f (a + 4 / d.f a)) - Real.log (d.f a)) /
      (a + 4 / d.f a - a) ≤ -tailRate * d.f a := by
    rw [div_le_iff₀ (by linarith : 0 < a + 4 / d.f a - a)]
    have heq : -tailRate * d.f a * (a + 4 / d.f a - a) = -Real.log 2 := by
      unfold tailRate
      field_simp
      ring
    rw [heq]
    linarith
  have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ a + y - (a + 4 / d.f a) by linarith)
  have hid : (-tailRate * d.f a) * (4 / d.f a) = -Real.log 2 := by
    unfold tailRate
    field_simp
  have hfinal : Real.log (d.f (a + y)) ≤ Real.log (d.f a) + (-tailRate * d.f a * y) := by
    nlinarith
  have he := Real.exp_le_exp.mpr hfinal
  simpa only [Real.exp_add, Real.exp_log (d.pos _)] using he

end SKFluctuations.PreKopa.Density

namespace SKFluctuations.PreKopa.Density
open ProbabilityTheory

theorem integrableOn_exp_shift {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-c * (x - a))) (Set.Ici b) := by
  have heq : (fun x : ℝ => Real.exp (-c * (x - a))) =
      fun x => Real.exp (c * a) * Real.exp (-c * x) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integrableOn_Ici_iff_integrableOn_Ioi]
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) b).const_mul _

theorem integral_exp_shift {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    (∫ x in Set.Ici b, Real.exp (-c * (x - a))) = Real.exp (-c * (b - a)) / c := by
  have heq : (fun x : ℝ => Real.exp (-c * (x - a))) =
      fun x => Real.exp (c * a) * Real.exp (-c * x) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (neg_neg_of_pos hc), neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring

theorem point_right_survival (d : Density) (a y : ℝ) (hy : 4 / d.f a ≤ y) :
    d.survival (a + y) ≤ (1 / tailRate) * Real.exp (-tailRate * d.f a * y) := by
  have hp := mul_pos tailRate_pos (d.pos a)
  rw [survival, ← d.setIntegral_eq_measureReal measurableSet_Ici]
  have hi := (integrableOn_exp_shift hp a (a + y)).const_mul (d.f a)
  have hbound := setIntegral_mono_on d.integrable.integrableOn hi measurableSet_Ici
    (fun x hx => by
      have h := d.point_right_tail a (x - a) (by change a + y ≤ x at hx; linarith)
      simpa only [add_sub_cancel, neg_mul] using h)
  apply hbound.trans_eq
  rw [integral_const_mul, integral_exp_shift hp, add_sub_cancel_left]
  field_simp [tailRate_pos.ne', (d.pos a).ne']

def pointTailConstant : ℝ := 2 * (Real.exp (4 * tailRate) + 1 / tailRate)

theorem pointTailConstant_pos : 0 < pointTailConstant := by
  unfold pointTailConstant
  exact mul_pos (by norm_num) (add_pos (Real.exp_pos _) (div_pos (by norm_num) tailRate_pos))

theorem point_right_survival_all (d : Density) (a y : ℝ) :
    d.survival (a + y) ≤ (pointTailConstant / 2) * Real.exp (-tailRate * d.f a * y) := by
  by_cases hy : 4 / d.f a ≤ y
  · apply (d.point_right_survival a y hy).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    unfold pointTailConstant
    nlinarith [Real.exp_pos (4 * tailRate)]
  · apply (d.survival_le_one _).trans
    have hm : d.f a * y ≤ 4 := by
      simpa only [mul_comm] using (le_div_iff₀ (d.pos a)).mp (le_of_not_ge hy)
    have hexp : Real.exp (-4 * tailRate) ≤ Real.exp (-tailRate * d.f a * y) :=
      Real.exp_le_exp.mpr (by nlinarith [tailRate_pos])
    have hp : Real.exp (4 * tailRate) ≤ pointTailConstant / 2 := by
      unfold pointTailConstant
      nlinarith [div_pos (by norm_num : (0 : ℝ) < 1) tailRate_pos]
    have hmul := mul_le_mul hexp hp (Real.exp_pos (4 * tailRate)).le
      (Real.exp_pos (-tailRate * d.f a * y)).le
    have heq : Real.exp (-4 * tailRate) * Real.exp (4 * tailRate) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    nlinarith

theorem point_abs_tail (d : Density) (a y : ℝ) :
    d.law.real {x | y ≤ |x - a|} ≤ pointTailConstant * Real.exp (-tailRate * d.f a * y) := by
  have hleft := d.reflect.point_right_survival_all (-a) y
  change d.reflect.survival (-a + y) ≤ pointTailConstant / 2 * Real.exp (-tailRate * d.f (- -a) * y) at hleft
  rw [neg_neg, show -a + y = -(a - y) by ring, reflect_survival] at hleft
  have hright := d.point_right_survival_all a y
  have heq : {x : ℝ | y ≤ |x - a|} = Set.Iic (a - y) ∪ Set.Ici (a + y) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, le_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
  rw [heq]
  have h := measureReal_union_le (μ := d.law) (Set.Iic (a - y)) (Set.Ici (a + y))
  dsimp [survival] at hright
  linarith

end SKFluctuations.PreKopa.Density

namespace SKFluctuations.PreKopa.Density
open ProbabilityTheory

def densityMomentConstant : ℝ := 8 * (1 + pointTailConstant) / tailRate ^ 2

theorem densityMomentConstant_pos : 0 < densityMomentConstant := by
  unfold densityMomentConstant
  exact div_pos (mul_pos (by norm_num) (by linarith [pointTailConstant_pos])) (sq_pos_of_pos tailRate_pos)

theorem point_exponential_bound (d : Density) (a : ℝ) :
    Integrable (fun x => Real.exp ((tailRate * d.f a / 2) * |x - a|)) d.law ∧
    (∫ x, Real.exp ((tailRate * d.f a / 2) * |x - a|) ∂d.law) ≤ 1 + pointTailConstant := by
  apply exponential_integral_of_tail d.law (measurable_id.sub_const a).abs (fun x => abs_nonneg _)
    (div_pos (mul_pos tailRate_pos (d.pos a)) (by norm_num)) pointTailConstant_pos.le
  intro u _
  convert d.point_abs_tail a u using 1
  congr 2
  ring_nf

theorem point_second_moment (d : Density) (a : ℝ) :
    Integrable (fun x => (x - a) ^ 2) d.law ∧
      (∫ x, (x - a) ^ 2 ∂d.law) ≤ densityMomentConstant / d.f a ^ 2 := by
  let c := tailRate * d.f a / 2
  have hc : 0 < c := div_pos (mul_pos tailRate_pos (d.pos a)) (by norm_num)
  let B := 2 / c ^ 2
  have hB : 0 < B := div_pos (by norm_num) (sq_pos_of_pos hc)
  have hp (x : ℝ) : (x - a) ^ 2 ≤ B * Real.exp (c * |x - a|) := by
    have h := Real.pow_div_factorial_le_exp (c * |x - a|) (mul_nonneg hc.le (abs_nonneg _)) 2
    norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat, mul_one, div_le_iff₀ (by norm_num : (0 : ℝ) < 2), mul_pow, sq_abs] at h
    dsimp [B]
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hc)]
    nlinarith
  have hiB : Integrable (fun x => B * Real.exp (c * |x - a|)) d.law :=
    (d.point_exponential_bound a).1.const_mul B
  have hi : Integrable (fun x => (x - a) ^ 2) d.law := hiB.mono' (by fun_prop)
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hp x))
  refine ⟨hi, (integral_mono hi hiB hp).trans ?_⟩
  rw [integral_const_mul]
  apply (mul_le_mul_of_nonneg_left (d.point_exponential_bound a).2 hB.le).trans_eq
  dsimp [B, c, densityMomentConstant]
  field_simp [tailRate_pos.ne', (d.pos a).ne']
  ring

def densityBoundConstant : ℝ := Real.sqrt densityMomentConstant

theorem densityBoundConstant_pos : 0 < densityBoundConstant :=
  Real.sqrt_pos.mpr densityMomentConstant_pos

theorem density_bound (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) (a : ℝ) :
    d.f a ≤ densityBoundConstant / d.sd := by
  have h := variance_le_expectation_sq (X := fun x : ℝ => x - a)
    (μ := d.law) ((measurable_id.sub_const a).aestronglyMeasurable)
  rw [variance_sub_const (X := fun x : ℝ => x) measurable_id.aestronglyMeasurable a] at h
  have hh : d.sd ^ 2 ≤ densityMomentConstant / d.f a ^ 2 := by
    rw [show d.sd ^ 2 = variance (fun x : ℝ => x) d.law from Real.sq_sqrt (variance_nonneg _ _)]
    exact h.trans (d.point_second_moment a).2
  rw [le_div_iff₀ (sq_pos_of_pos (d.pos a))] at hh
  rw [le_div_iff₀ (d.sd_pos h2)]
  have hC : densityBoundConstant ^ 2 = densityMomentConstant := Real.sq_sqrt densityMomentConstant_pos.le
  nlinarith [mul_pos (d.pos a) (d.sd_pos h2), densityBoundConstant_pos]

theorem interval_mass_bound (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law)
    (a : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    d.law.real (Set.Icc (a - r) (a + r)) ≤ 2 * densityBoundConstant * r / d.sd := by
  rw [← d.setIntegral_eq_measureReal measurableSet_Icc]
  have h := setIntegral_mono_on d.integrable.integrableOn
    (show IntegrableOn (fun _ : ℝ => densityBoundConstant / d.sd) (Set.Icc (a - r) (a + r)) from
      continuous_const.integrableOn_Icc) measurableSet_Icc (fun x _ => d.density_bound h2 x)
  apply h.trans_eq
  rw [setIntegral_const, smul_eq_mul]
  have hv : volume.real (Set.Icc (a - r) (a + r)) = 2 * r := by
    rw [Measure.real, Real.volume_Icc, show a + r - (a - r) = 2 * r by ring,
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr)]
  rw [hv]
  ring

end SKFluctuations.PreKopa.Density

namespace SKFluctuations

noncomputable def augmentedProbabilityDensity {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) :
    PreKopa.Density where
  f := augmentedDensity beta n
  pos := augmentedDensity_pos hb n
  lc := logConcave_augmentedDensity beta n
  integrable := integrable_augmentedDensity hb n
  mass := integral_augmentedDensity hb n

theorem law_augmentedProbabilityDensity {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) :
    (augmentedProbabilityDensity hb n).law = augmentedLaw beta n :=
  (augmentedLaw_withDensity beta n).symm

theorem memLp_augmentedLaw (beta : ℝ) (n : ℕ) :
    MemLp (fun x : ℝ => x) 2 (augmentedLaw beta n) := by
  unfold augmentedLaw
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  exact ((memLp_liftedFreeEnergy beta n).comp_fst _).add ((memLp_expMeasure_one 2).comp_snd _)

theorem memLp_augmentedProbabilityDensity {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) :
    MemLp (fun x : ℝ => x) 2 (augmentedProbabilityDensity hb n).law := by
  rw [law_augmentedProbabilityDensity]
  exact memLp_augmentedLaw beta n

def augmentedSD (beta : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (freeEnergyVariance beta n + beta ^ 2 / 2 + 1)

theorem sd_augmentedProbabilityDensity {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) :
    (augmentedProbabilityDensity hb n).sd = augmentedSD beta n := by
  unfold PreKopa.Density.sd augmentedSD
  rw [law_augmentedProbabilityDensity]
  exact congrArg Real.sqrt (variance_augmentedLaw beta n)

theorem augmentedSD_pos (beta : ℝ) (n : ℕ) : 0 < augmentedSD beta n := by
  apply Real.sqrt_pos.mpr
  have hv : 0 ≤ freeEnergyVariance beta n := variance_nonneg _ _
  positivity

theorem mean_augmentedProbabilityDensity {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) :
    (augmentedProbabilityDensity hb n).mean = meanFreeEnergy beta n + 1 := by
  unfold PreKopa.Density.mean
  rw [law_augmentedProbabilityDensity, mean_augmentedLaw]

theorem integrable_exp_augmentedLaw (beta : ℝ) (n : ℕ) {t : ℝ} (ht : t < 1) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (augmentedLaw beta n) := by
  unfold augmentedLaw
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  have hF : Integrable (fun x => Real.exp (t * liftedFreeEnergy beta n x))
      (standardCompletedLaw n) := integrable_exp_liftedFreeEnergy beta t n
  have hE := integrable_exp_expMeasure_one ht
  simpa only [Function.comp_def, mul_add, Real.exp_add] using hF.mul_prod hE

theorem integrable_exp_centered_augmentedLaw (beta : ℝ) (n : ℕ) {t : ℝ} (ht : t < 1) :
    Integrable (fun x : ℝ => Real.exp (t * (x - meanFreeEnergy beta n - 1)))
      (augmentedLaw beta n) := by
  simp_rw [mul_sub, Real.exp_sub]
  exact ((integrable_exp_augmentedLaw beta n ht).div_const _).div_const _

theorem augmented_tail {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) (u : ℝ) :
    (augmentedLaw beta n).real {x | u ≤ |x - (meanFreeEnergy beta n + 1)|} ≤
      PreKopa.Density.tailConstant * Real.exp (-PreKopa.tailRate * u / augmentedSD beta n) := by
  have h := (augmentedProbabilityDensity hb n).abs_tail
    (memLp_augmentedProbabilityDensity hb n) u
  rwa [law_augmentedProbabilityDensity, mean_augmentedProbabilityDensity,
    sd_augmentedProbabilityDensity] at h

theorem augmented_interval_mass {beta : ℝ} (hb : beta ≠ 0) (n : ℕ)
    (a : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (augmentedLaw beta n).real (Set.Icc (a - r) (a + r)) ≤
      2 * PreKopa.Density.densityBoundConstant * r / augmentedSD beta n := by
  have h := (augmentedProbabilityDensity hb n).interval_mass_bound
    (memLp_augmentedProbabilityDensity hb n) a hr
  rwa [law_augmentedProbabilityDensity, sd_augmentedProbabilityDensity] at h

theorem completed_logLaplace_small {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) {t : ℝ}
    (ht1 : t < 1) (htσ : |t| ≤ PreKopa.tailRate / (2 * augmentedSD beta n)) :
    completedCenteredLogLaplace beta t n - t - Real.log (1 - t) ≤
      Real.log (1 + PreKopa.Density.tailConstant) := by
  have h := (augmentedProbabilityDensity hb n).centered_log_mgf_small
    (memLp_augmentedProbabilityDensity hb n) (t := t)
  have hh : |t| ≤ (augmentedProbabilityDensity hb n).smallTilt := by
    rwa [PreKopa.Density.smallTilt, sd_augmentedProbabilityDensity]
  specialize h hh
  rw [PreKopa.Density.mean, law_augmentedProbabilityDensity] at h
  rwa [centeredLogLaplace_augmentedLaw beta n ht1] at h

theorem completed_logLaplace_lower {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    t * PreKopa.Density.positiveThreshold * augmentedSD beta n +
      Real.log PreKopa.Density.positiveMass ≤
      completedCenteredLogLaplace beta t n - t - Real.log (1 - t) := by
  have hi : Integrable (fun x => Real.exp (t * (x - (augmentedProbabilityDensity hb n).mean)))
      (augmentedProbabilityDensity hb n).law := by
    rw [mean_augmentedProbabilityDensity, law_augmentedProbabilityDensity]
    simpa only [sub_add_eq_sub_sub] using integrable_exp_centered_augmentedLaw beta n ht1
  have h := (augmentedProbabilityDensity hb n).centered_log_mgf_lower
    (memLp_augmentedProbabilityDensity hb n) ht hi
  rw [sd_augmentedProbabilityDensity, PreKopa.Density.mean,
    law_augmentedProbabilityDensity, centeredLogLaplace_augmentedLaw beta n ht1] at h
  exact h

end SKFluctuations

namespace SKFluctuations

 
theorem augmentationCorrection_nonneg {t : ℝ} (ht : t < 1) :
    0 ≤ -t - Real.log (1 - t) := by
  have h := Real.log_le_sub_one_of_pos (sub_pos.mpr ht)
  linarith

 
theorem augmentationCorrection_le {t : ℝ} (ht : 0 ≤ t) (ht2 : t ≤ 1 / 2) :
    -t - Real.log (1 - t) ≤ Real.log 2 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2)
    (show (1 : ℝ) / 2 ≤ 1 - t by linarith)
  rw [Real.log_div one_ne_zero (by norm_num), Real.log_one, zero_sub] at h
  linarith

theorem augmentedSD_lower_of_logLaplace {beta : ℝ} (hb : beta ≠ 0) (n : ℕ)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hK : Real.log (1 + PreKopa.Density.tailConstant) < completedCenteredLogLaplace beta t n) :
    PreKopa.tailRate / (2 * t) < augmentedSD beta n := by
  by_contra! h
  have htσ : |t| ≤ PreKopa.tailRate / (2 * augmentedSD beta n) := by
    rw [abs_of_pos ht, le_div_iff₀ (mul_pos (by norm_num) (augmentedSD_pos beta n))]
    rw [le_div_iff₀ (mul_pos (by norm_num) ht)] at h
    nlinarith
  have hh := completed_logLaplace_small hb n ht1 htσ
  have hc := augmentationCorrection_nonneg ht1
  linarith

theorem augmentedSD_upper_of_logLaplace {beta : ℝ} (hb : beta ≠ 0) (n : ℕ)
    {t B : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hK : completedCenteredLogLaplace beta t n ≤ B) :
    augmentedSD beta n ≤ (B + Real.log 2 - Real.log PreKopa.Density.positiveMass) /
      (t * PreKopa.Density.positiveThreshold) := by
  have hh := completed_logLaplace_lower hb n ht.le (by linarith)
  have hc := augmentationCorrection_le ht.le ht2
  rw [le_div_iff₀ (mul_pos ht PreKopa.Density.positiveThreshold_pos)]
  nlinarith

end SKFluctuations

namespace SKFluctuations.PinnedVariance
open MeasureTheory Filter Set
open scoped Topology

variable {Ω : Type*}

def quadraticTilt (A J : Ω → ℝ) (t : ℝ) (x : Ω) : ℝ :=
  Real.exp (t * A x - t ^ 2 / 2 * J x)
def quadraticTilt₁ (A J : Ω → ℝ) (t : ℝ) (x : Ω) : ℝ :=
  (A x - t * J x) * quadraticTilt A J t x
def quadraticTilt₂ (A J : Ω → ℝ) (t : ℝ) (x : Ω) : ℝ :=
  ((A x - t * J x) ^ 2 - J x) * quadraticTilt A J t x

theorem hasDerivAt_quadraticTilt (A J : Ω → ℝ) (t : ℝ) (x : Ω) :
    HasDerivAt (fun s => quadraticTilt A J s x) (quadraticTilt₁ A J t x) t := by
  have h := ((((hasDerivAt_id t).mul_const (A x)).sub
    ((((hasDerivAt_id t).pow 2).div_const 2).mul_const (J x))).exp)
  apply h.congr_deriv
  dsimp [quadraticTilt, quadraticTilt₁]
  ring

theorem hasDerivAt_quadraticTilt₁ (A J : Ω → ℝ) (t : ℝ) (x : Ω) :
    HasDerivAt (fun s => quadraticTilt₁ A J s x) (quadraticTilt₂ A J t x) t := by
  have h := ((hasDerivAt_const t (A x)).sub ((hasDerivAt_id t).mul_const (J x))).mul
    (hasDerivAt_quadraticTilt A J t x)
  apply h.congr_deriv
  dsimp [quadraticTilt₁, quadraticTilt₂]
  ring

theorem quadraticTilt_bounds {A J : Ω → ℝ} {M R t : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hA : ∀ x, |A x| ≤ M) (hJ : ∀ x, |J x| ≤ M) (ht : |t| ≤ R) (x : Ω) :
    ‖quadraticTilt A J t x‖ ≤ Real.exp (R * M + R ^ 2 / 2 * M) ∧
    ‖quadraticTilt₁ A J t x‖ ≤ (M + R * M) * Real.exp (R * M + R ^ 2 / 2 * M) ∧
    ‖quadraticTilt₂ A J t x‖ ≤ ((M + R * M) ^ 2 + M) *
      Real.exp (R * M + R ^ 2 / 2 * M) := by
  have h1 : |A x - t * J x| ≤ M + R * M := by
    calc
      _ ≤ |A x| + |t * J x| := abs_sub _ _
      _ = |A x| + |t| * |J x| := by rw [abs_mul]
      _ ≤ M + R * M := add_le_add (hA x) (mul_le_mul ht (hJ x) (abs_nonneg _) hR)
  have h2 : |(A x - t * J x) ^ 2 - J x| ≤ (M + R * M) ^ 2 + M := by
    calc
      _ ≤ |(A x - t * J x) ^ 2| + |J x| := abs_sub _ _
      _ ≤ (M + R * M) ^ 2 + M := by
        rw [abs_pow]
        exact add_le_add (pow_le_pow_left₀ (abs_nonneg _) h1 2) (hJ x)
  have ht2 : t ^ 2 ≤ R ^ 2 := by nlinarith [abs_le.mp ht]
  have he : t * A x - t ^ 2 / 2 * J x ≤ R * M + R ^ 2 / 2 * M := by
    have ha := mul_le_mul ht (hA x) (abs_nonneg (A x)) hR
    have hj := mul_le_mul ht2 (hJ x) (abs_nonneg (J x)) (sq_nonneg R)
    have hta := le_abs_self (t * A x)
    rw [abs_mul] at hta
    have hjlo := neg_le_abs (J x)
    nlinarith [mul_le_mul_of_nonneg_left hjlo (sq_nonneg t)]
  have h0 : ‖quadraticTilt A J t x‖ ≤ Real.exp (R * M + R ^ 2 / 2 * M) := by
    simpa [quadraticTilt, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr he
  refine ⟨h0, ?_, ?_⟩
  · rw [quadraticTilt₁, norm_mul, Real.norm_eq_abs (A x - t * J x)]
    exact mul_le_mul h1 h0 (norm_nonneg _) (by positivity)
  · rw [quadraticTilt₂, norm_mul, Real.norm_eq_abs ((A x - t * J x) ^ 2 - J x)]
    exact mul_le_mul h2 h0 (norm_nonneg _) (by positivity)

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_quadraticTilt_all {A J : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hA : Measurable A) (hJ : Measurable J) (hAb : ∀ x, |A x| ≤ M)
    (hJb : ∀ x, |J x| ≤ M) (t : ℝ) :
    Integrable (quadraticTilt A J t) μ ∧ Integrable (quadraticTilt₁ A J t) μ ∧
      Integrable (quadraticTilt₂ A J t) μ := by
  have hb := quadraticTilt_bounds hM (abs_nonneg t) hAb hJb le_rfl
  have hm0 : Measurable (quadraticTilt A J t) := by unfold quadraticTilt; fun_prop
  have hm1 : Measurable (quadraticTilt₁ A J t) := by unfold quadraticTilt₁ quadraticTilt; fun_prop
  have hm2 : Measurable (quadraticTilt₂ A J t) := by unfold quadraticTilt₂ quadraticTilt; fun_prop
  exact ⟨(integrable_const _).mono' hm0.aestronglyMeasurable (Eventually.of_forall fun x => (hb x).1),
    (integrable_const _).mono' hm1.aestronglyMeasurable (Eventually.of_forall fun x => (hb x).2.1),
    (integrable_const _).mono' hm2.aestronglyMeasurable (Eventually.of_forall fun x => (hb x).2.2)⟩

theorem hasDerivAt_integral_quadraticTilt {A J : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hA : Measurable A) (hJ : Measurable J) (hAb : ∀ x, |A x| ≤ M)
    (hJb : ∀ x, |J x| ≤ M) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, quadraticTilt A J s x ∂μ)
      (∫ x, quadraticTilt₁ A J t x ∂μ) t := by
  have hR : 0 ≤ |t| + 1 := by positivity
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (t - 1) (t + 1))
    (bound := fun _ => (M + (|t| + 1) * M) * Real.exp ((|t| + 1) * M + (|t| + 1) ^ 2 / 2 * M))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => ?_) (integrable_quadraticTilt_all hM hA hJ hAb hJb t).1
    (by unfold quadraticTilt₁ quadraticTilt; fun_prop)
    (Eventually.of_forall fun x s hs => ?_) (integrable_const _)
    (Eventually.of_forall fun x s _ => hasDerivAt_quadraticTilt A J s x)).2
  · unfold quadraticTilt; fun_prop
  · apply (quadraticTilt_bounds hM hR hAb hJb ?_ x).2.1
    rw [abs_le]
    constructor <;> have ht' := le_abs_self t <;> have ht'' := neg_le_abs t <;> linarith [hs.1, hs.2]

theorem hasDerivAt_integral_quadraticTilt₁ {A J : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hA : Measurable A) (hJ : Measurable J) (hAb : ∀ x, |A x| ≤ M)
    (hJb : ∀ x, |J x| ≤ M) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, quadraticTilt₁ A J s x ∂μ)
      (∫ x, quadraticTilt₂ A J t x ∂μ) t := by
  have hR : 0 ≤ |t| + 1 := by positivity
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (t - 1) (t + 1))
    (bound := fun _ => ((M + (|t| + 1) * M) ^ 2 + M) * Real.exp ((|t| + 1) * M + (|t| + 1) ^ 2 / 2 * M))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => ?_) (integrable_quadraticTilt_all hM hA hJ hAb hJb t).2.1
    (by unfold quadraticTilt₂ quadraticTilt; fun_prop)
    (Eventually.of_forall fun x s hs => ?_) (integrable_const _)
    (Eventually.of_forall fun x s _ => hasDerivAt_quadraticTilt₁ A J s x)).2
  · unfold quadraticTilt₁ quadraticTilt; fun_prop
  · apply (quadraticTilt_bounds hM hR hAb hJb ?_ x).2.2
    rw [abs_le]
    constructor <;> have ht' := le_abs_self t <;> have ht'' := neg_le_abs t <;> linarith [hs.1, hs.2]

theorem hasDerivAt_log_integral_quadraticTilt {A J : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hA : Measurable A) (hJ : Measurable J) (hAb : ∀ x, |A x| ≤ M)
    (hJb : ∀ x, |J x| ≤ M) (t : ℝ) :
    HasDerivAt (fun s => Real.log (∫ x, quadraticTilt A J s x ∂μ))
      ((∫ x, quadraticTilt₁ A J t x ∂μ) / (∫ x, quadraticTilt A J t x ∂μ)) t := by
  apply (hasDerivAt_integral_quadraticTilt hM hA hJ hAb hJb t).log
  exact (integral_exp_pos (integrable_quadraticTilt_all hM hA hJ hAb hJb t).1).ne'

theorem hasDerivAt_logSlope_zero {A J : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hA : Measurable A) (hJ : Measurable J) (hAb : ∀ x, |A x| ≤ M)
    (hJb : ∀ x, |J x| ≤ M) :
    HasDerivAt (fun t => (∫ x, quadraticTilt₁ A J t x ∂μ) /
      (∫ x, quadraticTilt A J t x ∂μ))
      (ProbabilityTheory.variance A μ - ∫ x, J x ∂μ) 0 := by
  have hA₂ : MemLp A 2 μ := MemLp.of_bound hA.aestronglyMeasurable M
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hAb x)
  have hJi : Integrable J μ := (integrable_const M).mono' hJ.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hJb x)
  have h := (hasDerivAt_integral_quadraticTilt₁ hM hA hJ hAb hJb (μ := μ) 0).div
    (hasDerivAt_integral_quadraticTilt hM hA hJ hAb hJb (μ := μ) 0) (by
      simp [quadraticTilt])
  apply h.congr_deriv
  simp [quadraticTilt₂, quadraticTilt₁, quadraticTilt]
  rw [integral_sub hA₂.integrable_sq hJi, ProbabilityTheory.variance_eq_sub hA₂]
  simp only [Pi.pow_apply]
  ring

 

theorem variance_le_of_concave_quadraticTilt {A J : Ω → ℝ} {M r : ℝ} (hM : 0 ≤ M)
    (hr : 0 < r) (hA : Measurable A) (hJ : Measurable J) (hAb : ∀ x, |A x| ≤ M)
    (hJb : ∀ x, |J x| ≤ M)
    (hc : ConcaveOn ℝ (Ioo (-r) r)
      (fun t => Real.log (∫ x, quadraticTilt A J t x ∂μ))) :
    ProbabilityTheory.variance A μ ≤ ∫ x, J x ∂μ := by
  have hd := hasDerivAt_log_integral_quadraticTilt hM hA hJ hAb hJb (μ := μ)
  have he : deriv (fun t => Real.log (∫ x, quadraticTilt A J t x ∂μ)) =
      fun t => (∫ x, quadraticTilt₁ A J t x ∂μ) / (∫ x, quadraticTilt A J t x ∂μ) := by
    funext t
    exact (hd t).deriv
  have hm := hc.antitoneOn_deriv (fun t _ => (hd t).differentiableAt)
  rw [he] at hm
  have hn := hm.derivWithin_nonpos (x := 0)
  rw [derivWithin_of_mem_nhds (Ioo_mem_nhds (neg_neg_of_pos hr) hr),
    (hasDerivAt_logSlope_zero hM hA hJ hAb hJb).deriv] at hn
  linarith

end SKFluctuations.PinnedVariance

namespace SKFluctuations.PreKopa
open MeasureTheory Filter Set
open scoped Topology

 

theorem concaveOn_log_integral_exp_neg {n : ℕ} {D : Set ℝ}
    {V : ℝ × (Fin n → ℝ) → ℝ} (hD : Convex ℝ D)
    (hV : ConvexOn ℝ (D ×ˢ univ) V)
    (hG : ∀ t ∈ D, GaussianDominated (fun x => Real.exp (-V (t, x)))) :
    ConcaveOn ℝ D (fun t => Real.log (∫ x, Real.exp (-V (t, x)))) := by
  have hp (t : ℝ) (ht : t ∈ D) : 0 < ∫ x, Real.exp (-V (t, x)) :=
    integral_strictlyPositive (hG t ht).integrable (fun _ => Real.exp_pos _)
  refine ⟨hD, ?_⟩
  intro t ht u hu a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · simp_all
  obtain rfl | hb' := hb.eq_or_lt
  · simp_all
  have htu := hD ht hu ha hb hab
  have hpl := prekopaLeindler_fin n ha' hb' hab (hG t ht) (hG u hu)
    (hG (a * t + b * u) htu) (fun _ => Real.exp_pos _) (fun _ => Real.exp_pos _)
    (fun _ => Real.exp_nonneg _) (fun x y => ?_)
  · have hlog := Real.log_le_log
      (mul_pos (Real.rpow_pos_of_pos (hp t ht) a) (Real.rpow_pos_of_pos (hp u hu) b)) hpl
    rw [Real.log_mul (Real.rpow_pos_of_pos (hp t ht) a).ne'
      (Real.rpow_pos_of_pos (hp u hu) b).ne', Real.log_rpow (hp t ht),
      Real.log_rpow (hp u hu)] at hlog
    exact hlog
  · rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := hV.2 (x := (t, x)) (y := (u, y)) ⟨ht, mem_univ x⟩ ⟨hu, mem_univ y⟩ ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h
    nlinarith

end SKFluctuations.PreKopa

namespace SKFluctuations.PinnedVariance
open MeasureTheory Filter Set
open scoped Topology
open SKFluctuations.PreKopa

variable {n : ℕ}

def quadraticPotential (U A J : (Fin n → ℝ) → ℝ) (p : ℝ × (Fin n → ℝ)) : ℝ :=
  U p.2 - p.1 * A p.2 + p.1 ^ 2 / 2 * J p.2

theorem gaussianDominated_quadraticPotential {U A J : (Fin n → ℝ) → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (hU : GaussianDominated (fun x => Real.exp (-U x)))
    (hA : Continuous A) (hJ : Continuous J) (hAb : ∀ x, |A x| ≤ M)
    (hJb : ∀ x, |J x| ≤ M) (t : ℝ) :
    GaussianDominated (fun x => Real.exp (-quadraticPotential U A J (t, x))) := by
  have he : (fun x => Real.exp (-quadraticPotential U A J (t, x))) =
      fun x => Real.exp (-U x) * quadraticTilt A J t x := by
    funext x
    rw [quadraticTilt, ← Real.exp_add]
    congr 1
    unfold quadraticPotential
    ring
  rw [he]
  obtain ⟨hc, C, c, hC, hc', hb⟩ := hU
  refine ⟨hc.mul (by unfold quadraticTilt; fun_prop),
    C * Real.exp (|t| * M + |t| ^ 2 / 2 * M), c,
    mul_pos hC (Real.exp_pos _), hc', ?_⟩
  intro x
  rw [norm_mul]
  calc
    _ ≤ (C * gaussianEnvelope c x) * Real.exp (|t| * M + |t| ^ 2 / 2 * M) :=
      mul_le_mul (hb x) (quadraticTilt_bounds hM (abs_nonneg t) hAb hJb le_rfl x).1
        (norm_nonneg _) (le_trans (norm_nonneg _) (hb x))
    _ = _ := by ring

 

theorem variance_le_of_convex_quadraticPotential
    {U A J : (Fin n → ℝ) → ℝ} {M r : ℝ}
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x))))
    (hM : 0 ≤ M) (hr : 0 < r)
    (hU : GaussianDominated (fun x => Real.exp (-U x)))
    (hA : Continuous A) (hJ : Continuous J) (hAb : ∀ x, |A x| ≤ M)
    (hJb : ∀ x, |J x| ≤ M)
    (hV : ConvexOn ℝ (Ioo (-r) r ×ˢ univ) (quadraticPotential U A J)) :
    ProbabilityTheory.variance A μ ≤ ∫ x, J x ∂μ := by
  apply variance_le_of_concave_quadraticTilt hM hr hA.measurable hJ.measurable hAb hJb
  have he (t : ℝ) : (∫ x, quadraticTilt A J t x ∂μ) =
      ∫ x, Real.exp (-quadraticPotential U A J (t, x)) := by
    rw [hμ, integral_withDensity_eq_integral_toReal_smul
      (hU.1.measurable.ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, quadraticTilt, ← Real.exp_add]
    congr 1
    unfold quadraticPotential
    ring
  simp_rw [he]
  exact concaveOn_log_integral_exp_neg (convex_Ioo _ _) hV
    (fun t _ => gaussianDominated_quadraticPotential hM hU hA hJ hAb hJb t)

end SKFluctuations.PinnedVariance

end

end OAI
