import Mathlib
import OAI.Probability.SKFluctuations.Cumulative
import OAI.Probability.SKFluctuations.Spin

namespace OAI

/-! Completed Index. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
namespace SKFluctuations

 
abbrev CompletedIndex (n : ℕ) := Option (Edge n)
abbrev StandardCompletedDisorder (n : ℕ) := CompletedIndex n → ℝ

def standardCompletedLaw (n : ℕ) : Measure (StandardCompletedDisorder n) :=
  Measure.pi (fun _ : CompletedIndex n => gaussianReal 0 1)

def toCompletedDisorder (beta : ℝ) (n : ℕ) (x : StandardCompletedDisorder n) : Disorder n × ℝ :=
  (fun e => x (some e), beta / Real.sqrt 2 * x none)

def liftedFreeEnergy (beta : ℝ) (n : ℕ) (x : StandardCompletedDisorder n) : ℝ :=
  completedFreeEnergy beta n (toCompletedDisorder beta n x)

def liftedHamiltonian (beta : ℝ) (n : ℕ) (x : StandardCompletedDisorder n)
    (sigma : Spin n) : ℝ :=
  hamiltonian beta n (fun e => x (some e)) sigma + beta / Real.sqrt 2 * x none

theorem continuous_liftedFreeEnergy (beta : ℝ) (n : ℕ) :
    Continuous (liftedFreeEnergy beta n) := by
  apply Continuous.add
    ((continuous_freeEnergy beta n).comp (show Continuous (fun (x : StandardCompletedDisorder n) e => x (some e)) by fun_prop))
    (by fun_prop)

theorem convexOn_liftedFreeEnergy (beta : ℝ) (n : ℕ) :
    ConvexOn ℝ Set.univ (liftedFreeEnergy beta n) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := (convex_freeEnergy beta n).2
    (Set.mem_univ (fun e => x (some e))) (Set.mem_univ (fun e => y (some e))) ha hb hab
  change freeEnergy beta n (a • (fun e => x (some e)) + b • (fun e => y (some e))) ≤
    a * freeEnergy beta n (fun e => x (some e)) + b * freeEnergy beta n (fun e => y (some e)) at h
  change freeEnergy beta n (a • (fun e => x (some e)) + b • (fun e => y (some e))) +
      beta / Real.sqrt 2 * (a * x none + b * y none) ≤
    a * (freeEnergy beta n (fun e => x (some e)) + beta / Real.sqrt 2 * x none) +
      b * (freeEnergy beta n (fun e => y (some e)) + beta / Real.sqrt 2 * y none)
  linarith

 
theorem exp_liftedFreeEnergy (beta : ℝ) (n : ℕ) (x : StandardCompletedDisorder n) :
    Real.exp (liftedFreeEnergy beta n x) =
      (2 : ℝ) ^ (-(n : ℤ)) * ∑ sigma : Spin n, Real.exp (liftedHamiltonian beta n x sigma) := by
  simp only [liftedFreeEnergy, completedFreeEnergy, toCompletedDisorder, Real.exp_add,
    liftedHamiltonian, Real.exp_log (partitionFunction_pos beta n _), freeEnergy]
  simp only [partitionFunction, ← Finset.sum_mul, mul_assoc]

 
def liftedCoefficients (beta : ℝ) (n : ℕ) (sigma : Spin n) : CompletedIndex n → ℝ
  | none => beta / Real.sqrt 2
  | some e => beta / Real.sqrt (n : ℝ) * spinValue (sigma e.val.1) * spinValue (sigma e.val.2)

theorem liftedHamiltonian_eq_sum (beta : ℝ) (n : ℕ) (x : StandardCompletedDisorder n)
    (sigma : Spin n) : liftedHamiltonian beta n x sigma =
      ∑ i : CompletedIndex n, liftedCoefficients beta n sigma i * x i := by
  rw [Fintype.sum_option]
  simp only [liftedHamiltonian, liftedCoefficients, hamiltonian, Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

def liftedGauge {n : ℕ} (tau : Spin n) (x : StandardCompletedDisorder n) :
    StandardCompletedDisorder n
  | none => x none
  | some e => x (some e) * spinValue (tau e.val.1) * spinValue (tau e.val.2)

@[simp] theorem liftedFreeEnergy_gauge (beta : ℝ) (n : ℕ) (tau : Spin n)
    (x : StandardCompletedDisorder n) :
    liftedFreeEnergy beta n (liftedGauge tau x) = liftedFreeEnergy beta n x := by
  change freeEnergy beta n (gaugeDisorder tau (fun e => x (some e))) +
    beta / Real.sqrt 2 * x none = _
  rw [freeEnergy_gauge]
  rfl

theorem liftedHamiltonian_gauge (beta : ℝ) (n : ℕ) (tau sigma : Spin n)
    (x : StandardCompletedDisorder n) :
    liftedHamiltonian beta n (liftedGauge tau x) sigma =
      liftedHamiltonian beta n x (spinGauge tau sigma) := by
  change hamiltonian beta n (gaugeDisorder tau (fun e => x (some e))) sigma +
    beta / Real.sqrt 2 * x none = _
  rw [hamiltonian_gauge]
  rfl

theorem measurePreserving_liftedGauge {n : ℕ} (tau : Spin n) :
    MeasurePreserving (liftedGauge tau) (standardCompletedLaw n) (standardCompletedLaw n) := by
  let signs : CompletedIndex n → ℝ → ℝ
    | none => id
    | some e => fun t => t * spinValue (tau e.val.1) * spinValue (tau e.val.2)
  have hm (i : CompletedIndex n) : Measurable (signs i) := by
    cases i <;> dsimp [signs] <;> fun_prop
  have hp (i : CompletedIndex n) : (gaussianReal 0 1).map (signs i) = gaussianReal 0 1 := by
    cases i with
    | none => simp [signs]
    | some e => exact gaussianReal_map_spinSigns _ _
  have he : liftedGauge tau = fun (x : StandardCompletedDisorder n) i => signs i (x i) := by
    funext x i
    cases i <;> rfl
  rw [he]
  refine ⟨Measurable.of_eval (fun i => (hm i).comp (measurable_pi_apply i)), ?_⟩
  rw [standardCompletedLaw, Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  simp only [hp]

end SKFluctuations

namespace SKFluctuations

instance standardCompletedLaw_isProbability (n : ℕ) :
    IsProbabilityMeasure (standardCompletedLaw n) := by
  unfold standardCompletedLaw
  infer_instance

theorem measurePreserving_toCompletedDisorder (beta : ℝ) (n : ℕ) :
    MeasurePreserving (toCompletedDisorder beta n) (standardCompletedLaw n)
      (completedLaw beta n) := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : CompletedIndex n => ℝ)
  have he (x : StandardCompletedDisorder n) : e x = (fun i => x (some i), x none) := by
    rfl
  have hp : MeasurePreserving e (standardCompletedLaw n)
      ((disorderLaw n).prod (gaussianReal 0 1)) := by
    refine ⟨e.measurable, ?_⟩
    unfold standardCompletedLaw disorderLaw
    rw [← Measure.pi_map_piOptionEquivProd (fun _ : CompletedIndex n => gaussianReal 0 1)]
    exact MeasurableEquiv.map_map_symm e
  have hm : MeasurePreserving (fun t : ℝ => beta / Real.sqrt 2 * t)
      (gaussianReal 0 1) (gaussianReal 0 (completionVariance beta)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      change (beta / Real.sqrt 2) ^ 2 * 1 = beta ^ 2 / 2
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
  have h := ((MeasurePreserving.id (disorderLaw n)).prod hm).comp hp
  have hf : toCompletedDisorder beta n = (Prod.map id (fun t => beta / Real.sqrt 2 * t)) ∘ e := by
    funext x
    rw [Function.comp_apply, he]
    rfl
  rw [hf]
  exact h

theorem integrable_exp_liftedFreeEnergy (beta t : ℝ) (n : ℕ) :
    Integrable (fun x => Real.exp (t * liftedFreeEnergy beta n x)) (standardCompletedLaw n) :=
  (measurePreserving_toCompletedDisorder beta n).integrable_comp_of_integrable
    (integrable_exp_completedFreeEnergy beta t n)

end SKFluctuations

namespace SKFluctuations

 
theorem integrable_exp_liftedHamiltonian (beta : ℝ) (n : ℕ) (sigma : Spin n) :
    Integrable (fun x => Real.exp (liftedHamiltonian beta n x sigma)) (standardCompletedLaw n) := by
  have h := Integrable.fintype_prod (fun i : CompletedIndex n =>
    integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (liftedCoefficients beta n sigma i))
  simpa only [standardCompletedLaw, liftedHamiltonian_eq_sum, Real.exp_sum] using h

def spinEpigraphIntegrand (beta : ℝ) (n : ℕ) (sigma : Spin n) (z : ℝ)
    (x : StandardCompletedDisorder n) : ℝ :=
  if liftedFreeEnergy beta n x ≤ z then Real.exp (liftedHamiltonian beta n x sigma) else 0

theorem integrable_spinEpigraphIntegrand (beta : ℝ) (n : ℕ) (sigma : Spin n) (z : ℝ) :
    Integrable (spinEpigraphIntegrand beta n sigma z) (standardCompletedLaw n) :=
  (integrable_exp_liftedHamiltonian beta n sigma).indicator
    (isClosed_le (continuous_liftedFreeEnergy beta n) continuous_const).measurableSet

theorem integral_spinEpigraphIntegrand_eq (beta : ℝ) (n : ℕ) (sigma rho : Spin n) (z : ℝ) :
    (∫ x, spinEpigraphIntegrand beta n sigma z x ∂standardCompletedLaw n) =
      ∫ x, spinEpigraphIntegrand beta n rho z x ∂standardCompletedLaw n := by
  obtain ⟨tau, htau⟩ := spinGauge_transitive sigma rho
  have hp := measurePreserving_liftedGauge tau
  have h := integral_map hp.measurable.aemeasurable
    ((integrable_spinEpigraphIntegrand beta n sigma z).aestronglyMeasurable.mono_ac
      hp.map_eq.absolutelyContinuous)
  rw [hp.map_eq] at h
  simpa only [spinEpigraphIntegrand, liftedFreeEnergy_gauge, liftedHamiltonian_gauge, htau] using h

 
def augmentedDensity (beta : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  Real.exp (-z) * ∫ x, (if liftedFreeEnergy beta n x ≤ z
    then Real.exp (liftedFreeEnergy beta n x) else 0) ∂standardCompletedLaw n

theorem augmentedDensity_eq_gaussianEpigraphTilt (beta : ℝ) (n : ℕ) (sigma : Spin n) :
    augmentedDensity beta n =
      PreKopa.gaussianEpigraphTilt (liftedFreeEnergy beta n) (liftedCoefficients beta n sigma) := by
  funext z
  have he (x : StandardCompletedDisorder n) :
      (if liftedFreeEnergy beta n x ≤ z then Real.exp (liftedFreeEnergy beta n x) else 0) =
        (2 : ℝ) ^ (-(n : ℤ)) * ∑ rho : Spin n, spinEpigraphIntegrand beta n rho z x := by
    by_cases hx : liftedFreeEnergy beta n x ≤ z
    · simp only [hx, ite_true, spinEpigraphIntegrand, exp_liftedFreeEnergy]
    · simp only [hx, ite_false, spinEpigraphIntegrand, Finset.sum_const_zero, mul_zero]
  unfold augmentedDensity PreKopa.gaussianEpigraphTilt
  simp_rw [he]
  congr 1
  rw [integral_const_mul, integral_finsetSum _ (fun rho _ =>
    integrable_spinEpigraphIntegrand beta n rho z)]
  simp_rw [integral_spinEpigraphIntegrand_eq beta n _ sigma z]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    prior_mass, one_mul]
  simp only [spinEpigraphIntegrand, liftedHamiltonian_eq_sum, standardCompletedLaw]

 
theorem logConcave_augmentedDensity (beta : ℝ) (n : ℕ) :
    PreKopa.LogConcave (augmentedDensity beta n) := by
  rw [augmentedDensity_eq_gaussianEpigraphTilt beta n (fun _ => true)]
  exact PreKopa.logConcave_gaussianEpigraphTilt (continuous_liftedFreeEnergy beta n)
    (convexOn_liftedFreeEnergy beta n) _

end SKFluctuations

namespace SKFluctuations

 
theorem map_add_expMeasure_withDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {F : Ω → ℝ} (hF : Measurable F) :
    (μ.prod (expMeasure 1)).map (fun p => F p.1 + p.2) =
      volume.withDensity (fun z => ∫⁻ x, exponentialPDF 1 (z - F x) ∂μ) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  ext s hs
  have hm : Measurable (fun p : Ω × ℝ => F p.1 + p.2) :=
    (hF.comp measurable_fst).add measurable_snd
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs), withDensity_apply _ hs]
  have hi (x : Ω) : expMeasure 1 (Prod.mk x ⁻¹' ((fun p : Ω × ℝ => F p.1 + p.2) ⁻¹' s)) =
      ∫⁻ z in s, exponentialPDF 1 (z - F x) := by
    change volume.withDensity (exponentialPDF 1) ((fun y => F x + y) ⁻¹' s) = _
    have hsx : MeasurableSet ((fun y : ℝ => F x + y) ⁻¹' s) :=
      hs.preimage (measurable_const.add measurable_id)
    rw [withDensity_apply _ hsx]
    rw [← lintegral_indicator hsx,
      ← lintegral_indicator hs]
    have h := lintegral_add_left_eq_self (μ := volume)
      (fun z : ℝ => s.indicator (fun z => exponentialPDF 1 (z - F x)) z) (F x)
    rw [← h]
    apply lintegral_congr
    intro y
    by_cases hy : F x + y ∈ s <;> simp [Set.indicator, hy]
  simp_rw [hi]
  exact lintegral_lintegral_swap (by
    unfold exponentialPDF
    exact (measurable_exponentialPDFReal 1).comp
      (measurable_snd.sub (hF.comp measurable_fst)) |>.ennreal_ofReal.aemeasurable)

 
def augmentedLaw (beta : ℝ) (n : ℕ) : Measure ℝ :=
  ((standardCompletedLaw n).prod (expMeasure 1)).map
    (fun p => liftedFreeEnergy beta n p.1 + p.2)

theorem augmentedDensity_nonneg (beta : ℝ) (n : ℕ) (z : ℝ) :
    0 ≤ augmentedDensity beta n z := by
  apply mul_nonneg (Real.exp_nonneg _)
  apply integral_nonneg
  intro x
  change 0 ≤ if liftedFreeEnergy beta n x ≤ z then Real.exp (liftedFreeEnergy beta n x) else 0
  split_ifs <;> positivity

theorem ofReal_augmentedDensity (beta : ℝ) (n : ℕ) (z : ℝ) :
    ENNReal.ofReal (augmentedDensity beta n z) =
      ∫⁻ x, exponentialPDF 1 (z - liftedFreeEnergy beta n x) ∂standardCompletedLaw n := by
  have hI : Integrable (fun x => if liftedFreeEnergy beta n x ≤ z
      then Real.exp (liftedFreeEnergy beta n x) else 0) (standardCompletedLaw n) := by
    have h := integrable_exp_liftedFreeEnergy beta 1 n
    simp only [one_mul] at h
    exact h.indicator
      (isClosed_le (continuous_liftedFreeEnergy beta n) continuous_const).measurableSet
  rw [augmentedDensity, ← integral_const_mul]
  rw [ofReal_integral_eq_lintegral_ofReal (hI.const_mul _) (Filter.Eventually.of_forall (fun x => by
    apply mul_nonneg (Real.exp_nonneg _)
    split_ifs <;> positivity))]
  apply lintegral_congr
  intro x
  rw [exponentialPDF_eq]
  simp only [sub_nonneg, one_mul]
  congr 1
  by_cases hx : liftedFreeEnergy beta n x ≤ z
  · simp only [hx, ite_true, ← Real.exp_add]
    congr 1
    ring
  · simp only [hx, ite_false, mul_zero]

theorem augmentedLaw_withDensity (beta : ℝ) (n : ℕ) :
    augmentedLaw beta n = volume.withDensity (fun z => ENNReal.ofReal (augmentedDensity beta n z)) := by
  rw [augmentedLaw, map_add_expMeasure_withDensity _ (continuous_liftedFreeEnergy beta n).measurable]
  congr 1
  funext z
  exact (ofReal_augmentedDensity beta n z).symm

end SKFluctuations

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace SKFluctuations

instance expMeasure_one_isProbability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

lemma exponentialPDF_one_toReal (x : ℝ) :
    (exponentialPDF 1 x).toReal = if 0 ≤ x then Real.exp (-x) else 0 := by
  rw [exponentialPDF_eq]
  simp only [one_mul]
  rw [ENNReal.toReal_ofReal]
  split_ifs <;> positivity

lemma integral_expMeasure_one (f : ℝ → ℝ) :
    ∫ x, f x ∂expMeasure 1 = ∫ x in Ici 0, Real.exp (-x) * f x := by
  change ∫ x, f x ∂volume.withDensity (exponentialPDF 1) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (exponentialPDF 1) from (measurable_exponentialPDFReal 1).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [smul_eq_mul, exponentialPDF_one_toReal]
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : 0 ≤ x <;> simp [Set.indicator, hx]

lemma integrable_expMeasure_one_iff {f : ℝ → ℝ} :
    Integrable f (expMeasure 1) ↔
      IntegrableOn (fun x => Real.exp (-x) * f x) (Ici 0) := by
  change Integrable f (volume.withDensity (exponentialPDF 1)) ↔ _
  rw [integrable_withDensity_iff_integrable_smul₀'
    (show AEMeasurable (exponentialPDF 1) volume from (measurable_exponentialPDFReal 1).ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [smul_eq_mul, exponentialPDF_one_toReal]
  rw [← integrable_indicator_iff measurableSet_Ici]
  have he : (fun x => (if 0 ≤ x then Real.exp (-x) else 0) * f x) =
      (Ici 0).indicator (fun x => Real.exp (-x) * f x) := by
    funext x
    by_cases hx : 0 ≤ x <;> simp [Set.indicator, hx]
  rw [he]

lemma integrable_exp_expMeasure_one {t : ℝ} (ht : t < 1) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (expMeasure 1) := by
  rw [integrable_expMeasure_one_iff]
  simp_rw [← Real.exp_add]
  have he (x : ℝ) : -x + t * x = (t - 1) * x := by ring
  simp_rw [he]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (by linarith) 0

lemma mgf_expMeasure_one {t : ℝ} (ht : t < 1) :
    mgf (id : ℝ → ℝ) (expMeasure 1) t = 1 / (1 - t) := by
  rw [mgf, integral_expMeasure_one]
  simp only [id_eq, ← Real.exp_add]
  have he (x : ℝ) : -x + t * x = (t - 1) * x := by ring
  simp_rw [he]
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (by linarith : t - 1 < 0)]
  simp only [mul_zero, Real.exp_zero]
  rw [show t - 1 = -(1 - t) by ring, neg_div_neg_eq]

lemma expMeasure_one_mem_interior {t : ℝ} (ht : t < 1) :
    t ∈ interior (integrableExpSet (id : ℝ → ℝ) (expMeasure 1)) := by
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact integrable_exp_expMeasure_one hs

lemma memLp_expMeasure_one (p : NNReal) : MemLp (id : ℝ → ℝ) p (expMeasure 1) :=
  memLp_of_mem_interior_integrableExpSet (expMeasure_one_mem_interior (by norm_num)) p

lemma hasDerivAt_one_div_one_sub {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun s : ℝ => 1 / (1 - s)) (1 / (1 - t) ^ 2) t := by
  convert! (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) (by linarith : 1 - t ≠ 0) using 1
  simp

lemma mean_expMeasure_one : ∫ x : ℝ, x ∂expMeasure 1 = 1 := by
  change ∫ x : ℝ, id x ∂expMeasure 1 = 1
  rw [← deriv_mgf_zero (expMeasure_one_mem_interior (by norm_num))]
  have he : mgf (id : ℝ → ℝ) (expMeasure 1) =ᶠ[𝓝 0] (fun t => 1 / (1 - t)) := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact mgf_expMeasure_one ht
  rw [he.deriv_eq, (hasDerivAt_one_div_one_sub (by norm_num : (0 : ℝ) < 1)).deriv]
  norm_num

lemma secondMoment_expMeasure_one : ∫ x : ℝ, x ^ 2 ∂expMeasure 1 = 2 := by
  have h0 := expMeasure_one_mem_interior (by norm_num : (0 : ℝ) < 1)
  have he : deriv (mgf (id : ℝ → ℝ) (expMeasure 1)) =ᶠ[𝓝 0]
      (fun t => 1 / (1 - t) ^ 2) := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    have he' : mgf (id : ℝ → ℝ) (expMeasure 1) =ᶠ[𝓝 t] (fun t => 1 / (1 - t)) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact mgf_expMeasure_one hs
    rw [he'.deriv_eq, (hasDerivAt_one_div_one_sub ht).deriv]
  have hd : HasDerivAt (fun t : ℝ => 1 / (1 - t) ^ 2) 2 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div
      (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))).pow 2)
      (by norm_num : ((1 : ℝ) - 0) ^ 2 ≠ 0) using 1
    norm_num
  have hi := iteratedDeriv_mgf_zero h0 2
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Pi.pow_apply, id_eq] at hi
  rw [← hi, he.deriv_eq, hd.deriv]

lemma variance_expMeasure_one : variance (id : ℝ → ℝ) (expMeasure 1) = 1 := by
  rw [variance_eq_sub (memLp_expMeasure_one 2)]
  change (∫ x : ℝ, x ^ 2 ∂expMeasure 1) - (∫ x : ℝ, x ∂expMeasure 1) ^ 2 = 1
  rw [secondMoment_expMeasure_one, mean_expMeasure_one]
  norm_num

end SKFluctuations

namespace SKFluctuations

attribute [fun_prop] continuous_freeEnergy continuous_liftedFreeEnergy

@[fun_prop] theorem continuous_completedFreeEnergy (beta : ℝ) (n : ℕ) :
    Continuous (completedFreeEnergy beta n) :=
  ((continuous_freeEnergy beta n).comp continuous_fst).add continuous_snd

theorem memLp_liftedFreeEnergy (beta : ℝ) (n : ℕ) :
    MemLp (liftedFreeEnergy beta n) 2 (standardCompletedLaw n) := by
  exact (memLp_completedFreeEnergy beta n).comp_measurePreserving
    (measurePreserving_toCompletedDisorder beta n)

theorem mean_liftedFreeEnergy (beta : ℝ) (n : ℕ) :
    ∫ x, liftedFreeEnergy beta n x ∂standardCompletedLaw n = meanFreeEnergy beta n := by
  have hp := measurePreserving_toCompletedDisorder beta n
  have hi := integral_map hp.aemeasurable
    ((continuous_completedFreeEnergy beta n).aestronglyMeasurable (μ := (standardCompletedLaw n).map (toCompletedDisorder beta n)))
  rw [hp.map_eq, mean_completedFreeEnergy] at hi
  exact hi.symm

theorem variance_liftedFreeEnergy (beta : ℝ) (n : ℕ) :
    variance (liftedFreeEnergy beta n) (standardCompletedLaw n) =
      freeEnergyVariance beta n + beta ^ 2 / 2 := by
  change variance (fun x => completedFreeEnergy beta n (toCompletedDisorder beta n x)) _ = _
  rw [(measurePreserving_toCompletedDisorder beta n).variance_fun_comp
    (continuous_completedFreeEnergy beta n).aemeasurable, variance_completedFreeEnergy]

theorem mgf_liftedFreeEnergy (beta t : ℝ) (n : ℕ) :
    mgf (liftedFreeEnergy beta n) (standardCompletedLaw n) t =
      mgf (completedFreeEnergy beta n) (completedLaw beta n) t := by
  have hp := measurePreserving_toCompletedDisorder beta n
  have hi := integral_map hp.aemeasurable
    (by fun_prop : AEStronglyMeasurable
      (fun x => Real.exp (t * completedFreeEnergy beta n x))
      ((standardCompletedLaw n).map (toCompletedDisorder beta n)))
  rw [hp.map_eq] at hi
  exact hi.symm

instance augmentedLaw_isProbability (beta : ℝ) (n : ℕ) :
    IsProbabilityMeasure (augmentedLaw beta n) := by
  unfold augmentedLaw
  infer_instance

theorem mean_augmentedLaw (beta : ℝ) (n : ℕ) :
    ∫ z : ℝ, z ∂augmentedLaw beta n = meanFreeEnergy beta n + 1 := by
  unfold augmentedLaw
  rw [integral_map (by fun_prop : AEMeasurable
    (fun p : StandardCompletedDisorder n × ℝ => liftedFreeEnergy beta n p.1 + p.2)
    ((standardCompletedLaw n).prod (expMeasure 1))) (by fun_prop :
      AEStronglyMeasurable (fun z : ℝ => z) _)]
  have hF := (memLp_liftedFreeEnergy beta n).integrable (by norm_num)
  have hE : Integrable (fun x : ℝ => x) (expMeasure 1) :=
    (memLp_expMeasure_one 2).integrable (by norm_num)
  rw [integral_add (hF.comp_fst _) (hE.comp_snd _), integral_fun_fst, integral_fun_snd (fun x : ℝ => x)]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, mean_liftedFreeEnergy,
    mean_expMeasure_one]

theorem variance_augmentedLaw (beta : ℝ) (n : ℕ) :
    variance (id : ℝ → ℝ) (augmentedLaw beta n) =
      freeEnergyVariance beta n + beta ^ 2 / 2 + 1 := by
  unfold augmentedLaw
  rw [variance_map (by fun_prop) (by fun_prop)]
  change variance (fun p : StandardCompletedDisorder n × ℝ =>
    liftedFreeEnergy beta n p.1 + p.2) _ = _
  have h := variance_add_prod (memLp_liftedFreeEnergy beta n) (memLp_expMeasure_one 2)
  rw [variance_liftedFreeEnergy, variance_expMeasure_one] at h
  exact h

theorem mgf_augmentedLaw (beta : ℝ) (n : ℕ) {t : ℝ} (ht : t < 1) :
    mgf (id : ℝ → ℝ) (augmentedLaw beta n) t =
      mgf (completedFreeEnergy beta n) (completedLaw beta n) t / (1 - t) := by
  unfold mgf augmentedLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [id_eq, mul_add, Real.exp_add]
  rw [integral_prod_mul (fun x => Real.exp (t * liftedFreeEnergy beta n x))
    (fun z : ℝ => Real.exp (t * z))]
  change mgf (liftedFreeEnergy beta n) (standardCompletedLaw n) t *
    mgf (id : ℝ → ℝ) (expMeasure 1) t = _
  rw [mgf_liftedFreeEnergy, mgf_expMeasure_one ht]
  unfold mgf
  ring

theorem centeredLogLaplace_augmentedLaw (beta : ℝ) (n : ℕ) {t : ℝ} (ht : t < 1) :
    Real.log (∫ z : ℝ, Real.exp (t * (z - ∫ w : ℝ, w ∂augmentedLaw beta n))
      ∂augmentedLaw beta n) = completedCenteredLogLaplace beta t n - t - Real.log (1 - t) := by
  rw [mean_augmentedLaw]
  simp_rw [mul_sub, Real.exp_sub]
  rw [integral_div]
  change Real.log (mgf (id : ℝ → ℝ) (augmentedLaw beta n) t /
    Real.exp (t * (meanFreeEnergy beta n + 1))) = _
  rw [mgf_augmentedLaw beta n ht]
  have hp : 0 < mgf (completedFreeEnergy beta n) (completedLaw beta n) t :=
    mgf_pos (integrable_exp_completedFreeEnergy beta t n)
  rw [Real.log_div (div_ne_zero hp.ne' (by linarith)) (Real.exp_pos _).ne',
    Real.log_div hp.ne' (by linarith : 1 - t ≠ 0), Real.log_exp]
  have hc : completedCenteredLogLaplace beta t n =
      Real.log (mgf (completedFreeEnergy beta n) (completedLaw beta n) t) -
        t * meanFreeEnergy beta n := by
    unfold completedCenteredLogLaplace completedLaplaceTransform
    simp_rw [mul_sub, Real.exp_sub]
    rw [integral_div]
    exact Real.log_div hp.ne' (Real.exp_pos _).ne' |>.trans (by rw [Real.log_exp])
  rw [hc]
  ring

end SKFluctuations

namespace SKFluctuations.PreKopa

theorem LogConcave.mul {E : Type*} [Add E] [SMul ℝ E] {f g : E → ℝ}
    (hf : LogConcave f) (hg : LogConcave g) : LogConcave (fun x => f x * g x) := by
  refine ⟨fun x => mul_nonneg (hf.1 x) (hg.1 x), ?_⟩
  intro x y a b ha hb hab
  rw [Real.mul_rpow (hf.1 x) (hg.1 x), Real.mul_rpow (hf.1 y) (hg.1 y)]
  calc
    f x ^ a * g x ^ a * (f y ^ b * g y ^ b) =
        (f x ^ a * f y ^ b) * (g x ^ a * g y ^ b) := by ring
    _ ≤ f (a • x + b • y) * g (a • x + b • y) :=
      mul_le_mul (hf.2 x y a b ha hb hab) (hg.2 x y a b ha hb hab)
        (mul_nonneg (Real.rpow_nonneg (hg.1 x) _) (Real.rpow_nonneg (hg.1 y) _)) (hf.1 _)

theorem LogConcave.concaveOn_log {f : ℝ → ℝ} (hf : LogConcave f)
    (hp : ∀ x, 0 < f x) : ConcaveOn ℝ univ (fun x => Real.log (f x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos (hp x) a)
    (Real.rpow_pos_of_pos (hp y) b)) (hf.2 x y a b ha hb hab)
  rw [Real.log_mul (Real.rpow_pos_of_pos (hp x) a).ne'
    (Real.rpow_pos_of_pos (hp y) b).ne', Real.log_rpow (hp x), Real.log_rpow (hp y)] at h
  exact h

theorem LogConcave.continuous_of_pos {f : ℝ → ℝ} (hf : LogConcave f)
    (hp : ∀ x, 0 < f x) : Continuous f := by
  have hc := continuousOn_univ.mp ((hf.concaveOn_log hp).continuousOn isOpen_univ)
  have he : f = fun x => Real.exp (Real.log (f x)) := by
    funext x
    exact (Real.exp_log (hp x)).symm
  rw [he]
  exact Real.continuous_exp.comp hc

 
def survivalApprox (f : ℝ → ℝ) (k : ℕ) (z x : ℝ) : ℝ :=
  f x * Real.exp (-((k : ℝ) * max (z - x) 0))

def survivalIntegral (f : ℝ → ℝ) (z : ℝ) : ℝ := ∫ x in Ici z, f x

theorem logConcave_survivalApprox {f : ℝ → ℝ} (hf : LogConcave f) (k : ℕ) :
    LogConcave (fun p : ℝ × ℝ => survivalApprox f k p.1 p.2) := by
  have hf' : LogConcave (fun p : ℝ × ℝ => f p.2) := by
    refine ⟨fun p => hf.1 _, ?_⟩
    intro x y a b ha hb hab
    exact hf.2 x.2 y.2 a b ha hb hab
  have hc : ConvexOn ℝ univ (fun p : ℝ × ℝ => (k : ℝ) * max (p.1 - p.2) 0) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [Prod.smul_fst, Prod.fst_add, Prod.smul_snd, Prod.snd_add, smul_eq_mul]
    have hm : max (a * x.1 + b * y.1 - (a * x.2 + b * y.2)) 0 ≤
        a * max (x.1 - x.2) 0 + b * max (y.1 - y.2) 0 := by
      apply max_le
      · have h1 := mul_le_mul_of_nonneg_left (le_max_left (x.1 - x.2) 0) ha
        have h2 := mul_le_mul_of_nonneg_left (le_max_left (y.1 - y.2) 0) hb
        nlinarith
      · positivity
    have h := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith
  exact hf'.mul (logConcave_exp_neg hc)

theorem survivalApprox_bound {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x)
    (k : ℕ) (z x : ℝ) : ‖survivalApprox f k z x‖ ≤ f x := by
  have he : Real.exp (-((k : ℝ) * max (z - x) 0)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg k) (le_max_right _ _)))
  rw [survivalApprox, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf x) (Real.exp_nonneg _))]
  nlinarith [hf x]

theorem integrable_survivalApprox {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f)
    (hf : ∀ x, 0 ≤ f x) (k : ℕ) (z : ℝ) : Integrable (survivalApprox f k z) := by
  apply hi.mono' (by unfold survivalApprox; fun_prop)
  exact Filter.Eventually.of_forall (survivalApprox_bound hf k z)

theorem tendsto_survivalApprox {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f)
    (hf : ∀ x, 0 ≤ f x) (z : ℝ) :
    Tendsto (fun k : ℕ => ∫ x, survivalApprox f k z x) atTop (𝓝 (survivalIntegral f z)) := by
  unfold survivalIntegral
  rw [← integral_indicator measurableSet_Ici]
  apply tendsto_integral_of_dominated_convergence f
  · intro k
    unfold survivalApprox
    fun_prop
  · exact hi
  · intro k
    exact Filter.Eventually.of_forall (survivalApprox_bound hf k z)
  · apply Filter.Eventually.of_forall
    intro x
    by_cases hx : z ≤ x
    · have hh : max (z - x) 0 = 0 := max_eq_right (by linarith)
      simp only [survivalApprox, hh, mul_zero, neg_zero, Real.exp_zero, mul_one]
      simp [Set.indicator, hx]
    · have hz : 0 < z - x := by linarith
      have he : Tendsto (fun k : ℕ => Real.exp (-((k : ℝ) * (z - x)))) atTop (𝓝 0) := by
        apply Real.tendsto_exp_atBot.comp
        exact tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hz)
      simpa [survivalApprox, max_eq_left hz.le, Set.indicator, hx] using he.const_mul (f x)

 
theorem logConcave_survivalIntegral {f : ℝ → ℝ} (hf : LogConcave f)
    (hp : ∀ x, 0 < f x) (hi : Integrable f) : LogConcave (survivalIntegral f) := by
  have hc := hf.continuous_of_pos hp
  apply LogConcave.of_tendsto (F := fun k z => ∫ x, survivalApprox f k z x)
  · intro k
    refine ⟨fun z => integral_nonneg fun x => mul_nonneg (hf.1 x) (Real.exp_nonneg _), ?_⟩
    intro z w a b ha hb hab
    obtain rfl | ha' := ha.eq_or_lt
    · simp_all
    obtain rfl | hb' := hb.eq_or_lt
    · simp_all
    apply prekopaLeindler ha' hb' hab
      (integrable_survivalApprox hi hc hf.1 k z) (by unfold survivalApprox; fun_prop)
      (fun x => mul_pos (hp x) (Real.exp_pos _))
      (integrable_survivalApprox hi hc hf.1 k w) (by unfold survivalApprox; fun_prop)
      (fun x => mul_pos (hp x) (Real.exp_pos _))
      (integrable_survivalApprox hi hc hf.1 k (a * z + b * w))
      (fun x => mul_nonneg (hf.1 x) (Real.exp_nonneg _))
    intro x y
    exact (logConcave_survivalApprox hf k).2 (z, x) (w, y) a b ha hb hab
  · exact tendsto_survivalApprox hi hc hf.1

end SKFluctuations.PreKopa

end

end OAI
