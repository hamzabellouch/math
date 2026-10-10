import Mathlib
import OAI.Probability.SKFluctuations.CompletedIndex

namespace OAI

/-! Standard Completed Law Is Open Pos. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations

instance standardCompletedLaw_isOpenPos (n : ℕ) : Measure.IsOpenPosMeasure (standardCompletedLaw n) := by
  have : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)).isOpenPosMeasure
  unfold standardCompletedLaw
  infer_instance

theorem liftedFreeEnergy_surjective {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) :
    Function.Surjective (liftedFreeEnergy beta n) := by
  intro z
  let x : StandardCompletedDisorder n := fun i =>
    match i with
    | none => (z - freeEnergy beta n (fun _ => 0)) / (beta / Real.sqrt 2)
    | some _ => 0
  refine ⟨x, ?_⟩
  change freeEnergy beta n (fun e => x (some e)) + beta / Real.sqrt 2 * x none = z
  dsimp [x]
  rw [mul_div_cancel₀ _ (div_ne_zero hb (by positivity : Real.sqrt 2 ≠ 0))]
  ring

theorem augmentedDensity_pos {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) (z : ℝ) :
    0 < augmentedDensity beta n z := by
  unfold augmentedDensity
  apply mul_pos (Real.exp_pos _)
  have hi : Integrable (fun x => if liftedFreeEnergy beta n x ≤ z
      then Real.exp (liftedFreeEnergy beta n x) else 0) (standardCompletedLaw n) := by
    have h := integrable_exp_liftedFreeEnergy beta 1 n
    simp only [one_mul] at h
    exact h.indicator
      (isClosed_le (continuous_liftedFreeEnergy beta n) continuous_const).measurableSet
  apply (integral_pos_iff_support_of_nonneg (fun x => by split_ifs <;> positivity) hi).mpr
  have ho : IsOpen {x | liftedFreeEnergy beta n x < z} :=
    isOpen_lt (continuous_liftedFreeEnergy beta n) continuous_const
  have hn : ({x | liftedFreeEnergy beta n x < z} : Set (StandardCompletedDisorder n)).Nonempty := by
    obtain ⟨x, hx⟩ := liftedFreeEnergy_surjective hb n (z - 1)
    exact ⟨x, by simp only [Set.mem_ofPred_eq, hx]; linarith⟩
  have hm := ho.measure_pos (standardCompletedLaw n) hn
  apply hm.trans_le
  apply measure_mono
  intro x hx
  change liftedFreeEnergy beta n x < z at hx
  simp only [Function.mem_support, ite_eq_left hx.le]
  exact (Real.exp_pos _).ne'

@[fun_prop] theorem continuous_augmentedDensity {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) :
    Continuous (augmentedDensity beta n) :=
  (logConcave_augmentedDensity beta n).continuous_of_pos (augmentedDensity_pos hb n)

theorem integrable_augmentedDensity {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) :
    Integrable (augmentedDensity beta n) := by
  have hmass : ∫⁻ z, ENNReal.ofReal (augmentedDensity beta n z) = 1 := by
    have h := measure_univ (μ := augmentedLaw beta n)
    rw [augmentedLaw_withDensity, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have hi := integrable_toReal_of_lintegral_ne_top
    ((continuous_augmentedDensity hb n).measurable.ennreal_ofReal.aemeasurable)
    (by rw [hmass]; exact ENNReal.one_ne_top)
  simpa only [ENNReal.toReal_ofReal (augmentedDensity_nonneg beta n _)] using hi

theorem lintegral_augmentedDensity (beta : ℝ) (n : ℕ) :
    ∫⁻ z, ENNReal.ofReal (augmentedDensity beta n z) = 1 := by
  have h := measure_univ (μ := augmentedLaw beta n)
  rw [augmentedLaw_withDensity, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  exact h

theorem integral_augmentedDensity {beta : ℝ} (hb : beta ≠ 0) (n : ℕ) :
    ∫ z, augmentedDensity beta n z = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (augmentedDensity_nonneg beta n))
      (integrable_augmentedDensity hb n).aestronglyMeasurable,
    lintegral_augmentedDensity, ENNReal.toReal_one]

end SKFluctuations

namespace SKFluctuations.PreKopa

 
structure Density where
  f : ℝ → ℝ
  pos : ∀ x, 0 < f x
  lc : LogConcave f
  integrable : Integrable f
  mass : ∫ x, f x = 1

namespace Density

def law (d : Density) : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (d.f x))

@[fun_prop] theorem continuous (d : Density) : Continuous d.f := d.lc.continuous_of_pos d.pos

instance law_probability (d : Density) : IsProbabilityMeasure d.law := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal d.integrable
      (Filter.Eventually.of_forall (fun x => (d.pos x).le)), d.mass]
  norm_num

instance law_openPos (d : Density) : d.law.IsOpenPosMeasure := by
  apply Measure.AbsolutelyContinuous.isOpenPosMeasure (μ := volume)
  apply withDensity_absolutelyContinuous'
  · exact d.continuous.measurable.ennreal_ofReal.aemeasurable
  · exact Filter.Eventually.of_forall (fun x => (ENNReal.ofReal_pos.mpr (d.pos x)).ne')

theorem setIntegral_eq_measureReal (d : Density) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x in s, d.f x = d.law.real s := by
  rw [Measure.real, law, withDensity_apply _ hs]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => (d.pos x).le)) d.integrable.restrict.aestronglyMeasurable

def survival (d : Density) (z : ℝ) : ℝ := d.law.real (Set.Ici z)

theorem survival_eq_integral (d : Density) : d.survival = survivalIntegral d.f := by
  funext z
  exact (d.setIntegral_eq_measureReal measurableSet_Ici).symm

theorem survival_pos (d : Density) (z : ℝ) : 0 < d.survival z := by
  apply ENNReal.toReal_pos (ne_of_gt ?_) (measure_ne_top _ _)
  exact (isOpen_Ioi.measure_pos d.law Set.nonempty_Ioi).trans_le
    (measure_mono Set.Ioi_subset_Ici_self)

theorem survival_le_one (d : Density) (z : ℝ) : d.survival z ≤ 1 := measureReal_le_one

theorem lc_survival (d : Density) : LogConcave d.survival := by
  rw [d.survival_eq_integral]
  exact logConcave_survivalIntegral d.lc d.pos d.integrable

theorem concave_log_survival (d : Density) : ConcaveOn ℝ Set.univ (fun z => Real.log (d.survival z)) :=
  d.lc_survival.concaveOn_log d.survival_pos

end Density

 
theorem logConcave_secant {f : ℝ → ℝ} (hf : LogConcave f) (hp : ∀ x, 0 < f x)
    {a b x : ℝ} (hab : a < b) (hbx : b ≤ x) :
    Real.log (f x) ≤ Real.log (f b) +
      (x - b) * ((Real.log (f b) - Real.log (f a)) / (b - a)) := by
  obtain rfl | hbx' := hbx.eq_or_lt
  · simp
  have h := (hf.concaveOn_log hp).slope_anti_adjacent (Set.mem_univ a) (Set.mem_univ x) hab hbx'
  have h' := (div_le_iff₀ (sub_pos.mpr hbx')).mp h
  nlinarith

def tailRate : ℝ := Real.log 2 / 4

theorem tailRate_pos : 0 < tailRate := div_pos (Real.log_pos (by norm_num)) (by norm_num)

 
theorem survival_tail_from_anchors {f : ℝ → ℝ} (hf : LogConcave f)
    (hp : ∀ z, 0 < f z) (h1 : ∀ z, f z ≤ 1)
    {m sigma : ℝ} (hs : 0 < sigma)
    (ha : 1 / 2 ≤ f (m - 2 * sigma)) (hb : f (m + 2 * sigma) ≤ 1 / 4)
    {u : ℝ} :
    f (m + u) ≤ Real.exp (2 * tailRate - tailRate * u / sigma) := by
  by_cases hsmall : u ≤ 2 * sigma
  · apply (h1 _).trans
    apply Real.one_le_exp_iff.mpr
    have h := (div_le_iff₀ hs).mpr hsmall
    have hh := mul_le_mul_of_nonneg_left h tailRate_pos.le
    rw [← mul_div_assoc] at hh
    linarith
  have hbu : m + 2 * sigma ≤ m + u := by linarith
  have hsec := logConcave_secant hf hp (a := m - 2 * sigma) (b := m + 2 * sigma)
    (x := m + u) (by linarith) hbu
  have hloga : Real.log (1 / 2 : ℝ) ≤ Real.log (f (m - 2 * sigma)) :=
    Real.log_le_log (by norm_num) ha
  have hlogb : Real.log (f (m + 2 * sigma)) ≤ Real.log (1 / 4 : ℝ) :=
    Real.log_le_log (hp _) hb
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero (by norm_num), Real.log_one, zero_sub]
  have hlogquarter : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.log_pow, hloghalf]
    ring
  rw [hloghalf] at hloga
  rw [hlogquarter] at hlogb
  have hdiff : Real.log (f (m + 2 * sigma)) - Real.log (f (m - 2 * sigma)) ≤ -Real.log 2 := by linarith
  have hslope : (Real.log (f (m + 2 * sigma)) - Real.log (f (m - 2 * sigma))) /
      (m + 2 * sigma - (m - 2 * sigma)) ≤ -tailRate / sigma := by
    rw [div_le_div_iff₀ (by linarith : 0 < m + 2 * sigma - (m - 2 * sigma)) hs]
    dsimp [tailRate]
    nlinarith [mul_le_mul_of_nonneg_right hdiff hs.le]
  have hlogb0 : Real.log (f (m + 2 * sigma)) ≤ 0 := Real.log_nonpos (hp _).le (h1 _)
  have hlog : Real.log (f (m + u)) ≤ 2 * tailRate - tailRate * u / sigma := by
    have hmul := mul_le_mul_of_nonneg_left hslope (show 0 ≤ m + u - (m + 2 * sigma) by linarith)
    have heq : (m + u - (m + 2 * sigma)) * (-tailRate / sigma) =
        2 * tailRate - tailRate * u / sigma := by field_simp [hs.ne']; ring
    rw [heq] at hmul
    linarith
  exact (Real.log_le_iff_le_exp (hp _)).mp hlog

end SKFluctuations.PreKopa

namespace SKFluctuations.PreKopa.Density
open ProbabilityTheory

 
def reflect (d : Density) : Density where
  f x := d.f (-x)
  pos x := d.pos (-x)
  lc := by
    constructor
    · intro x; exact (d.pos _).le
    · intro x y a b ha hb hab
      simpa only [neg_add, smul_neg] using d.lc.2 (-x) (-y) a b ha hb hab
  integrable := (Measure.measurePreserving_neg volume).integrable_comp
    d.integrable.aestronglyMeasurable |>.mpr d.integrable
  mass := by rw [integral_neg_eq_self, d.mass]

theorem law_reflect (d : Density) : d.reflect.law = d.law.map (fun x => -x) := by
  ext s hs
  rw [Measure.map_apply (measurable_neg) hs, law, withDensity_apply _ hs,
    law, withDensity_apply _ (measurable_neg hs)]
  rw [← lintegral_indicator hs, ← lintegral_indicator (measurable_neg hs)]
  have heq : (fun x => (s.indicator (fun x => ENNReal.ofReal (d.f (-x)))) (-x)) =
      (fun x => ((fun x : ℝ => -x) ⁻¹' s).indicator (fun x => ENNReal.ofReal (d.f x)) x) := by
    funext x
    by_cases hx : -x ∈ s <;> simp [hx]
  change ∫⁻ x, s.indicator (fun x => ENNReal.ofReal (d.f (-x))) x = _
  rw [← lintegral_neg_eq_self, heq]

theorem variance_pos (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    0 < variance (fun x : ℝ => x) d.law := by
  apply lt_of_le_of_ne (ProbabilityTheory.variance_nonneg _ _)
  intro hz
  have hae := ae_eq_integral_of_variance_eq_zero h2 hz.symm
  have heq : (fun x : ℝ => x) = fun _ => ∫ x, x ∂d.law :=
    (Continuous.ae_eq_iff_eq d.law continuous_id continuous_const).mp hae
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  linarith

def mean (d : Density) : ℝ := ∫ x, x ∂d.law
def sd (d : Density) : ℝ := Real.sqrt (variance (fun x : ℝ => x) d.law)

theorem sd_pos (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) : 0 < d.sd :=
  Real.sqrt_pos.mpr (d.variance_pos h2)

theorem chebyshev_two (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    d.law.real {x | 2 * d.sd ≤ |x - d.mean|} ≤ 1 / 4 := by
  have hp := d.sd_pos h2
  have h := meas_ge_le_variance_div_sq h2 (show 0 < 2 * d.sd by positivity)
  have hv : variance (fun x : ℝ => x) d.law / (2 * d.sd) ^ 2 = 1 / 4 := by
    have heq : d.sd ^ 2 = variance (fun x : ℝ => x) d.law := Real.sq_sqrt (ProbabilityTheory.variance_nonneg _ _)
    rw [← heq]
    field_simp
    nlinarith
  rw [hv] at h
  have h' := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4), mean, Measure.real] using h'

theorem survival_anchors (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    1 / 2 ≤ d.survival (d.mean - 2 * d.sd) ∧
    d.survival (d.mean + 2 * d.sd) ≤ 1 / 4 := by
  have hc := d.chebyshev_two h2
  have hleft : d.law.real (Set.Iio (d.mean - 2 * d.sd)) ≤ 1 / 4 := by
    apply le_trans (measureReal_mono ?_) hc
    intro x hx
    simp only [Set.mem_Iio, Set.mem_ofPred_eq] at hx ⊢
    exact (neg_le_abs _).trans' (by linarith : 2 * d.sd ≤ -(x - d.mean))
  have hsum : d.law.real (Set.Ici (d.mean - 2 * d.sd)) =
      1 - d.law.real (Set.Iio (d.mean - 2 * d.sd)) := by
    rw [← Set.compl_Iio, measureReal_compl measurableSet_Iio]
    simp
  constructor
  · dsimp [survival]
    rw [hsum]
    linarith
  · apply le_trans (measureReal_mono ?_) hc
    intro x hx
    change 2 * d.sd ≤ |x - d.mean|
    exact (le_abs_self (x - d.mean)).trans' (by change d.mean + 2 * d.sd ≤ x at hx; linarith)

theorem survival_tail (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) (u : ℝ) :
    d.survival (d.mean + u) ≤ Real.exp (2 * tailRate - tailRate * u / d.sd) :=
  survival_tail_from_anchors d.lc_survival d.survival_pos d.survival_le_one
    (d.sd_pos h2) (d.survival_anchors h2).1 (d.survival_anchors h2).2

end SKFluctuations.PreKopa.Density

namespace SKFluctuations.PreKopa.Density
open ProbabilityTheory

theorem memLp_reflect (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    MemLp (fun x : ℝ => x) 2 d.reflect.law := by
  rw [law_reflect]
  exact (memLp_map_measure_iff (measurable_id.aestronglyMeasurable)
    measurable_neg.aemeasurable).mpr h2.neg

theorem mean_reflect (d : Density) : d.reflect.mean = -d.mean := by
  simp only [mean, law_reflect]
  rw [integral_map (φ := fun x : ℝ => -x) (f := fun x : ℝ => x)
    measurable_neg.aemeasurable measurable_id.aestronglyMeasurable]
  exact integral_neg _

theorem sd_reflect (d : Density) : d.reflect.sd = d.sd := by
  simp only [sd, law_reflect]
  rw [variance_map (X := fun x : ℝ => x) (Y := fun x : ℝ => -x)
    measurable_id.aemeasurable measurable_neg.aemeasurable]
  congr 1
  exact variance_neg (X := fun x : ℝ => x)

theorem reflect_survival (d : Density) (z : ℝ) :
    d.reflect.survival (-z) = d.law.real (Set.Iic z) := by
  simp only [survival, Measure.real, law_reflect,
    Measure.map_apply measurable_neg measurableSet_Ici]
  congr 2
  ext x
  simp

theorem left_tail (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) (u : ℝ) :
    d.law.real (Set.Iic (d.mean - u)) ≤ Real.exp (2 * tailRate - tailRate * u / d.sd) := by
  have h := d.reflect.survival_tail (d.memLp_reflect h2) u
  rw [mean_reflect, sd_reflect] at h
  rw [show -d.mean + u = -(d.mean - u) by ring, reflect_survival] at h
  exact h

def tailConstant : ℝ := 2 * Real.exp (2 * tailRate)

theorem tailConstant_pos : 0 < tailConstant := by unfold tailConstant; positivity

theorem abs_tail (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) (u : ℝ) :
    d.law.real {x | u ≤ |x - d.mean|} ≤ tailConstant * Real.exp (-tailRate * u / d.sd) := by
  have heq : {x : ℝ | u ≤ |x - d.mean|} =
      Set.Iic (d.mean - u) ∪ Set.Ici (d.mean + u) := by
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
  calc d.law.real (Set.Iic (d.mean - u) ∪ Set.Ici (d.mean + u))
    _ ≤ d.law.real (Set.Iic (d.mean - u)) + d.law.real (Set.Ici (d.mean + u)) :=
      measureReal_union_le _ _
    _ ≤ Real.exp (2 * tailRate - tailRate * u / d.sd) +
        Real.exp (2 * tailRate - tailRate * u / d.sd) :=
      add_le_add (d.left_tail h2 u) (d.survival_tail h2 u)
    _ = tailConstant * Real.exp (-tailRate * u / d.sd) := by
      rw [show 2 * tailRate - tailRate * u / d.sd =
        2 * tailRate + (-tailRate * u / d.sd) by ring, Real.exp_add]
      unfold tailConstant
      ring

end SKFluctuations.PreKopa.Density

namespace SKFluctuations.PreKopa

 
theorem exponential_integral_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (ht : ∀ u, 0 < u → μ.real {x | u ≤ f x} ≤ A * Real.exp (-2 * c * u)) :
    Integrable (fun x => Real.exp (c * f x)) μ ∧
      (∫ x, Real.exp (c * f x) ∂μ) ≤ 1 + A := by
  have hint (v : ℝ) : IntervalIntegrable (fun u => c * Real.exp (c * u)) volume 0 v :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hcalc (v : ℝ) : (∫ u in (0 : ℝ)..v, c * Real.exp (c * u)) = Real.exp (c * v) - 1 := by
    have hd (u : ℝ) : HasDerivAt (fun u => Real.exp (c * u)) (c * Real.exp (c * u)) u := by
      simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id u).const_mul c).exp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hint v)]
    simp
  have hl := lintegral_comp_eq_lintegral_meas_le_mul μ
    (ae_of_all μ hn) hf.aemeasurable (fun v _ => hint v)
    (ae_of_all _ (fun u => mul_nonneg hc.le (Real.exp_pos _).le))
  simp_rw [hcalc] at hl
  have hbound : (∫⁻ x, ENNReal.ofReal (Real.exp (c * f x) - 1) ∂μ) ≤ ENNReal.ofReal A := by
    rw [hl]
    calc (∫⁻ u in Ioi (0 : ℝ), μ {x | u ≤ f x} * ENNReal.ofReal (c * Real.exp (c * u)))
      _ ≤ ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (A * c * Real.exp (-c * u)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hμ : μ {x | u ≤ f x} ≤ ENNReal.ofReal (A * Real.exp (-2 * c * u)) := by
          rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal (ht u hu)
        apply (mul_le_mul hμ le_rfl bot_le bot_le).trans_eq
        rw [← ENNReal.ofReal_mul (mul_nonneg hA (Real.exp_pos _).le)]
        congr 1
        calc A * Real.exp (-2 * c * u) * (c * Real.exp (c * u))
          _ = A * c * (Real.exp (-2 * c * u) * Real.exp (c * u)) := by ring
          _ = A * c * Real.exp (-c * u) := by rw [← Real.exp_add]; congr 2; ring
      _ = ENNReal.ofReal A := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0).const_mul (A * c))
          (ae_of_all _ (fun u => by positivity)), integral_const_mul,
          integral_exp_mul_Ioi (neg_lt_zero.mpr hc)]
        simp only [mul_zero, Real.exp_zero]
        congr 1
        field_simp
  have hnonneg (x : Ω) : 0 ≤ Real.exp (c * f x) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hc.le (hn x)))
  have hi0 : Integrable (fun x => Real.exp (c * f x) - 1) μ := by
    refine ⟨(hf.const_mul c).exp.sub_const 1 |>.aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all μ hnonneg)).mpr
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hi : Integrable (fun x => Real.exp (c * f x)) μ := by
    have hi' : Integrable (fun x => (Real.exp (c * f x) - 1) + 1) μ :=
      hi0.add (integrable_const (1 : ℝ))
    simpa only [sub_add_cancel] using hi'
  refine ⟨hi, ?_⟩
  have hi0le : (∫ x, Real.exp (c * f x) - 1 ∂μ) ≤ A := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all μ hnonneg) hi0.aestronglyMeasurable]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hA)
  rw [integral_sub hi (integrable_const 1)] at hi0le
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using (by linarith :
    (∫ x, Real.exp (c * f x) ∂μ) ≤ (∫ _ : Ω, (1 : ℝ) ∂μ) + A)

end SKFluctuations.PreKopa

namespace SKFluctuations.PreKopa.Density
open ProbabilityTheory

def smallTilt (d : Density) : ℝ := tailRate / (2 * d.sd)

theorem smallTilt_pos (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) : 0 < d.smallTilt :=
  div_pos tailRate_pos (mul_pos (by norm_num) (d.sd_pos h2))

theorem exponential_abs_bound (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    Integrable (fun x => Real.exp (d.smallTilt * |x - d.mean|)) d.law ∧
      (∫ x, Real.exp (d.smallTilt * |x - d.mean|) ∂d.law) ≤ 1 + tailConstant := by
  apply exponential_integral_of_tail d.law (measurable_id.sub_const _).abs
    (fun x => abs_nonneg _) (d.smallTilt_pos h2) tailConstant_pos.le
  intro u _
  convert d.abs_tail h2 u using 1
  congr 2
  unfold smallTilt
  ring_nf

theorem exponential_centered_le (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law)
    {t : ℝ} (ht : |t| ≤ d.smallTilt) :
    Integrable (fun x => Real.exp (t * (x - d.mean))) d.law ∧
      (∫ x, Real.exp (t * (x - d.mean)) ∂d.law) ≤ 1 + tailConstant := by
  have hp (x : ℝ) : Real.exp (t * (x - d.mean)) ≤ Real.exp (d.smallTilt * |x - d.mean|) := by
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right ht (abs_nonneg _)))
  have hi : Integrable (fun x => Real.exp (t * (x - d.mean))) d.law :=
    (d.exponential_abs_bound h2).1.mono' (by fun_prop)
      (ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hp x))
  exact ⟨hi, (integral_mono hi (d.exponential_abs_bound h2).1 hp).trans (d.exponential_abs_bound h2).2⟩

 
def momentConstant (k : ℕ) : ℝ := (k.factorial : ℝ) * (2 / tailRate) ^ k * (1 + tailConstant)

theorem momentConstant_pos (k : ℕ) : 0 < momentConstant k := by
  unfold momentConstant
  exact mul_pos (mul_pos (by exact_mod_cast Nat.factorial_pos k)
    (pow_pos (div_pos (by norm_num) tailRate_pos) _)) (by linarith [tailConstant_pos])

theorem centered_abs_moment (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) (k : ℕ) :
    Integrable (fun x => |x - d.mean| ^ k) d.law ∧
      (∫ x, |x - d.mean| ^ k ∂d.law) ≤ momentConstant k * d.sd ^ k := by
  have hc := d.smallTilt_pos h2
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  let B : ℝ := (k.factorial : ℝ) / d.smallTilt ^ k
  have hB : 0 < B := div_pos hfac (pow_pos hc _)
  have hp (x : ℝ) : |x - d.mean| ^ k ≤ B * Real.exp (d.smallTilt * |x - d.mean|) := by
    have h := Real.pow_div_factorial_le_exp (d.smallTilt * |x - d.mean|)
      (mul_nonneg hc.le (abs_nonneg _)) k
    rw [mul_pow, div_le_iff₀ hfac] at h
    dsimp [B]
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc k)]
    nlinarith [h]
  have hiB : Integrable (fun x => B * Real.exp (d.smallTilt * |x - d.mean|)) d.law :=
    (d.exponential_abs_bound h2).1.const_mul B
  have hi : Integrable (fun x => |x - d.mean| ^ k) d.law := hiB.mono' (by fun_prop)
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]; exact hp x))
  refine ⟨hi, (integral_mono hi hiB hp).trans ?_⟩
  rw [integral_const_mul]
  apply (mul_le_mul_of_nonneg_left (d.exponential_abs_bound h2).2 hB.le).trans_eq
  dsimp [B]
  rw [div_eq_mul_inv, ← inv_pow]
  have heq : d.smallTilt⁻¹ = (2 / tailRate) * d.sd := by
    unfold smallTilt
    rw [inv_div]
    ring
  rw [heq, mul_pow]
  unfold momentConstant
  ring

end SKFluctuations.PreKopa.Density

namespace SKFluctuations.PreKopa.Density
open ProbabilityTheory

 
def standardized (d : Density) (x : ℝ) : ℝ := (x - d.mean) / d.sd

@[fun_prop] theorem measurable_standardized (d : Density) : Measurable d.standardized := by
  unfold standardized
  fun_prop

theorem integrable_standardized (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    Integrable d.standardized d.law :=
  ((h2.integrable (by norm_num)).sub (integrable_const d.mean)).div_const d.sd

theorem integral_standardized (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    ∫ x, d.standardized x ∂d.law = 0 := by
  unfold standardized
  rw [integral_div, integral_sub (h2.integrable (by norm_num)) (integrable_const _)]
  simp [mean]

theorem standardized_second (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    Integrable (fun x => d.standardized x ^ 2) d.law ∧
      (∫ x, d.standardized x ^ 2 ∂d.law) = 1 := by
  have hi := (h2.sub (memLp_const d.mean)).integrable_sq
  constructor
  · simpa only [standardized, div_pow, Pi.sub_apply] using hi.div_const (d.sd ^ 2)
  · simp only [standardized, div_pow]
    rw [integral_div]
    change (∫ x, (x - ∫ y, y ∂d.law) ^ 2 ∂d.law) / d.sd ^ 2 = 1
    rw [← variance_eq_integral (X := fun x : ℝ => x) (μ := d.law) measurable_id.aemeasurable]
    unfold sd
    rw [Real.sq_sqrt (ProbabilityTheory.variance_nonneg _ _), div_self (d.variance_pos h2).ne']

theorem standardized_fourth (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    Integrable (fun x => d.standardized x ^ 4) d.law ∧
      (∫ x, d.standardized x ^ 4 ∂d.law) ≤ momentConstant 4 := by
  have hp := d.sd_pos h2
  have habs (x : ℝ) : |x| ^ 4 = x ^ 4 := (by decide : Even (4 : ℕ)).pow_abs x
  have hi : Integrable (fun x => (x - d.mean) ^ 4) d.law := by
    simpa only [habs] using (d.centered_abs_moment h2 4).1
  constructor
  · simpa only [standardized, div_pow] using hi.div_const (d.sd ^ 4)
  · simp only [standardized, div_pow]
    rw [integral_div, div_le_iff₀ (pow_pos hp 4)]
    simpa only [habs] using (d.centered_abs_moment h2 4).2

def momentRadius : ℝ := 2 * (momentConstant 4 + 1)

theorem momentRadius_pos : 0 < momentRadius := by
  unfold momentRadius
  linarith [momentConstant_pos 4]

theorem momentRadius_ge_one : 1 ≤ momentRadius := by
  unfold momentRadius
  linarith [momentConstant_pos 4]

theorem fourth_over_radius : momentConstant 4 / momentRadius ^ 2 ≤ 1 / 2 := by
  rw [div_le_iff₀ (sq_pos_of_pos momentRadius_pos)]
  unfold momentRadius
  nlinarith [sq_nonneg (momentConstant 4), momentConstant_pos 4]

theorem square_cutoff (z r : ℝ) (hz : 0 ≤ z) (hr : 0 < r) :
    z ^ 2 ≤ r * z + z ^ 4 / r ^ 2 := by
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hr)).mp
  have heq : r ^ 2 * (z ^ 4 / r ^ 2) = z ^ 4 := by field_simp
  rw [mul_add, heq]
  by_cases hzr : z ≤ r
  · have hz2 : z ^ 2 ≤ r * z := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hz2 (sq_nonneg r)
    nlinarith [pow_nonneg hz 4]
  · have hz2 : r ^ 2 ≤ z ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hz2 (sq_nonneg z)
    have hp : 0 ≤ r * z * r ^ 2 := mul_nonneg (mul_nonneg hr.le hz) (sq_nonneg _)
    nlinarith

theorem standardized_abs_lower (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    1 / (2 * momentRadius) ≤ ∫ x, |d.standardized x| ∂d.law := by
  have hi := d.integrable_standardized h2
  have hsecond := d.standardized_second h2
  have hfourth := d.standardized_fourth h2
  have hineq := integral_mono hsecond.1
    ((hi.abs.const_mul momentRadius).add (hfourth.1.div_const (momentRadius ^ 2)))
    (fun x => by simpa only [sq_abs, (by decide : Even (4 : ℕ)).pow_abs, Pi.add_apply] using
      square_cutoff |d.standardized x| momentRadius (abs_nonneg _) momentRadius_pos)
  simp only [Pi.add_apply] at hineq
  rw [hsecond.2, integral_add (hi.abs.const_mul momentRadius)
    (hfourth.1.div_const (momentRadius ^ 2)), integral_const_mul, integral_div] at hineq
  have hbound := (div_le_div_of_nonneg_right hfourth.2 (sq_nonneg momentRadius)).trans fourth_over_radius
  rw [div_le_iff₀ (mul_pos (by norm_num) momentRadius_pos)]
  nlinarith

theorem standardized_positive_lower (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    1 / (4 * momentRadius) ≤ ∫ x, max (d.standardized x) 0 ∂d.law := by
  have h := integral_abs_eq_two_mul_integral_posPart_sub_integral (d.integrable_standardized h2)
  rw [d.integral_standardized h2, sub_zero] at h
  have ha := d.standardized_abs_lower h2
  rw [h] at ha
  change 1 / (2 * momentRadius) ≤ 2 * (∫ x, max (d.standardized x) 0 ∂d.law) at ha
  have heq : 1 / (4 * momentRadius) = 1 / (2 * momentRadius) / 2 := by ring
  rw [heq]
  linarith

def positiveThreshold : ℝ := 1 / (8 * momentRadius)
def positiveMass : ℝ := 1 / (256 * momentRadius ^ 2)

theorem positiveThreshold_pos : 0 < positiveThreshold := by
  unfold positiveThreshold
  exact div_pos (by norm_num) (mul_pos (by norm_num) momentRadius_pos)

theorem positiveMass_pos : 0 < positiveMass := by
  unfold positiveMass
  exact div_pos (by norm_num) (mul_pos (by norm_num) (sq_pos_of_pos momentRadius_pos))

theorem positive_cutoff (z a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) :
    max z 0 ≤ a + r * (if a ≤ z then 1 else 0) + z ^ 2 / r := by
  split_ifs with h
  · simp only [mul_one]
    rw [max_eq_left (ha.trans h)]
    by_cases hzr : z ≤ r
    · have := div_nonneg (sq_nonneg z) hr.le
      linarith
    · have hz : 0 ≤ z := ha.trans h
      have hz2 : z * r ≤ z ^ 2 := by simpa only [pow_two] using mul_le_mul_of_nonneg_left (le_of_not_ge hzr) hz
      have hh : z ≤ z ^ 2 / r := (le_div_iff₀ hr).mpr hz2
      linarith
  · simp only [mul_zero, add_zero]
    have hh : max z 0 ≤ a := max_le (le_of_not_ge h) ha
    exact hh.trans (le_add_of_nonneg_right (div_nonneg (sq_nonneg z) hr.le))

theorem standardized_positive_mass (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    positiveMass ≤ d.law.real {x | positiveThreshold ≤ d.standardized x} := by
  let A := {x | positiveThreshold ≤ d.standardized x}
  have hA : MeasurableSet A := measurableSet_le measurable_const d.measurable_standardized
  have hi := d.integrable_standardized h2
  have hsecond := d.standardized_second h2
  have hInd : Integrable (A.indicator (fun _ => (1 : ℝ))) d.law := (integrable_const _).indicator hA
  have heq (x : ℝ) : (if positiveThreshold ≤ d.standardized x then (1 : ℝ) else 0) =
      A.indicator (fun _ => (1 : ℝ)) x := by rfl
  have hiPos : Integrable (fun x => max (d.standardized x) 0) d.law := hi.sup (integrable_const 0)
  have hp (x : ℝ) : max (d.standardized x) 0 ≤ positiveThreshold +
      (16 * momentRadius) * A.indicator (fun _ => (1 : ℝ)) x +
        d.standardized x ^ 2 / (16 * momentRadius) := by
    have hh := positive_cutoff (d.standardized x) positiveThreshold (16 * momentRadius)
      positiveThreshold_pos.le (mul_pos (by norm_num) momentRadius_pos)
    simpa only [heq] using hh
  have hiM : Integrable (fun x => positiveThreshold +
      (16 * momentRadius) * A.indicator (fun _ => (1 : ℝ)) x) d.law :=
    (integrable_const positiveThreshold).add (hInd.const_mul (16 * momentRadius))
  have hb := integral_mono hiPos (hiM.add (hsecond.1.div_const (16 * momentRadius))) hp
  change (∫ x, max (d.standardized x) 0 ∂d.law) ≤
    ∫ x, positiveThreshold + (16 * momentRadius) * A.indicator (fun _ => (1 : ℝ)) x +
      d.standardized x ^ 2 / (16 * momentRadius) ∂d.law at hb
  rw [integral_add hiM (hsecond.1.div_const (16 * momentRadius)),
    integral_add (integrable_const _) (hInd.const_mul (16 * momentRadius)),
    integral_const, show d.law.real Set.univ = 1 by simp, one_smul, integral_const_mul,
    integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one, integral_div,
    hsecond.2] at hb
  have hlo := d.standardized_positive_lower h2
  change positiveMass ≤ d.law.real A
  dsimp only [positiveMass, positiveThreshold] at hb ⊢
  have hr := momentRadius_pos
  field_simp at hb hlo ⊢
  nlinarith

end SKFluctuations.PreKopa.Density

namespace SKFluctuations.PreKopa.Density
open ProbabilityTheory

theorem positive_mass (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law) :
    positiveMass ≤ d.law.real {x | positiveThreshold * d.sd ≤ x - d.mean} := by
  have h := d.standardized_positive_mass h2
  simpa only [standardized, le_div_iff₀ (d.sd_pos h2)] using h

theorem centered_mgf_lower (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law)
    {t : ℝ} (ht : 0 ≤ t) (hi : Integrable (fun x => Real.exp (t * (x - d.mean))) d.law) :
    positiveMass * Real.exp (t * positiveThreshold * d.sd) ≤
      ∫ x, Real.exp (t * (x - d.mean)) ∂d.law := by
  let A := {x | positiveThreshold * d.sd ≤ x - d.mean}
  have hA : MeasurableSet A := measurableSet_le measurable_const (measurable_id.sub_const _)
  have hInd := (integrable_const (Real.exp (t * positiveThreshold * d.sd))).indicator (μ := d.law) hA
  have hbound : ∀ x, A.indicator (fun _ => Real.exp (t * positiveThreshold * d.sd)) x ≤
      Real.exp (t * (x - d.mean)) := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hx ht
      nlinarith
    · rw [Set.indicator_of_notMem hx]
      exact (Real.exp_pos _).le
  have hh := integral_mono hInd hi hbound
  rw [integral_indicator hA, setIntegral_const, smul_eq_mul] at hh
  exact (mul_le_mul_of_nonneg_right (d.positive_mass h2) (Real.exp_pos _).le).trans hh

theorem centered_log_mgf_lower (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law)
    {t : ℝ} (ht : 0 ≤ t) (hi : Integrable (fun x => Real.exp (t * (x - d.mean))) d.law) :
    t * positiveThreshold * d.sd + Real.log positiveMass ≤
      Real.log (∫ x, Real.exp (t * (x - d.mean)) ∂d.law) := by
  have h := Real.log_le_log (mul_pos positiveMass_pos (Real.exp_pos _)) (d.centered_mgf_lower h2 ht hi)
  rw [Real.log_mul positiveMass_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  linarith

theorem centered_log_mgf_small (d : Density) (h2 : MemLp (fun x : ℝ => x) 2 d.law)
    {t : ℝ} (ht : |t| ≤ d.smallTilt) :
    Real.log (∫ x, Real.exp (t * (x - d.mean)) ∂d.law) ≤ Real.log (1 + tailConstant) := by
  have h := d.exponential_centered_le h2 ht
  apply Real.log_le_log _ h.2
  exact mgf_pos h.1

end SKFluctuations.PreKopa.Density

end

end OAI
