import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingSeparated
import OAI.Analysis.IrrationalRotation.Analysis.PeriodicIntervalDiscrepancy
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingMoments

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductSamplingPhaseMoments

theorem eVariationOn_ofReal (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => (f x : ℂ)) s = eVariationOn f s := by
  simp only [eVariationOn, Complex.isometry_ofReal.edist_eq]

theorem real_bv_discrepancy {m : ℕ} (hm : 200 ≤ m)
    {N₀ N : ℝ} {n n' : ℕ} (hp : ScalarSampling.SamplingPair m N₀ N n n')
    (f g : ℝ → ℝ) (hf : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hg : BoundedVariationOn g (Icc (0 : ℝ) 1)) :
    |(∫ a, f (Int.fract ((n : ℝ) * a)) * g (Int.fract ((n' : ℝ) * a))
        ∂UniformIntervalPhase.lambdaLaw N₀) -
      (∫ t in (0 : ℝ)..1, f t) * (∫ t in (0 : ℝ)..1, g t)| ≤
      (29 / (m : ℝ)^80) *
        (sSup ((fun t => |f t|) '' Icc (0 : ℝ) 1) +
          (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (sSup ((fun t => |g t|) '' Icc (0 : ℝ) 1) +
          (eVariationOn g (Icc (0 : ℝ) 1)).toReal) := by
  have hfc : BoundedVariationOn (fun t => (f t : ℂ)) (Icc (0 : ℝ) 1) := by
    simpa only [BoundedVariationOn, eVariationOn_ofReal] using hf
  have hgc : BoundedVariationOn (fun t => (g t : ℂ)) (Icc (0 : ℝ) 1) := by
    simpa only [BoundedVariationOn, eVariationOn_ofReal] using hg
  have hsep : ∀ i j : ℤ, |i| ≤ (m ^ 300 : ℕ) → |j| ≤ (m ^ 300 : ℕ) →
      (i, j) ≠ (0, 0) → N * (m : ℝ)^1000 < |(i : ℝ) * n + (j : ℝ) * n'| := by
    intro i j hi hj hij
    apply hp.separated i j hi hj
    by_contra h
    push Not at h
    exact hij (by simp [h.1, h.2])
  have h := ScalarRectangles.scalar_bv_discrepancy m hm N₀ N hp.N₀_pos hp.N₀_le
    hp.N_le n n' hp.first_range.1 hp.second_range.1 hsep
    (fun t => (f t : ℂ)) (fun t => (g t : ℂ)) hfc hgc
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal,
    intervalIntegral.integral_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, eVariationOn_ofReal] using h

theorem real_one_phase_error {N₀ n : ℝ} (hN : 0 < N₀) (hn : 0 < n)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) :
    |(∫ a, f (Int.fract (n * a)) ∂UniformIntervalPhase.lambdaLaw N₀) -
      (∫ t in (0 : ℝ)..1, f t)| ≤
        (N₀ / n) * ∫ t in (0 : ℝ)..1, f t := by
  rw [UniformIntervalPhase.lambdaLaw_eq_cond N₀ hN]
  have h := PeriodicIntervalDiscrepancy.uniform_angle_test_le hN hn hf
  have heq : (∫ t in (0 : ℝ)..1, |f t|) = ∫ t in (0 : ℝ)..1, f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact abs_of_nonneg (hf0 t (by simpa using ht))
  simpa only [heq] using h

def unitInterval : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)

instance unitInterval_probability : IsProbabilityMeasure unitInterval := by
  constructor
  simp [unitInterval]

theorem integral_unitInterval (f : ℝ → ℝ) :
    (∫ t, f t ∂unitInterval) = ∫ t in (0 : ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [unitInterval, restrict_Ico_eq_restrict_Ioc]

theorem fractionLaw_le_two {N₀ n : ℝ} (hN : 0 < N₀) (hn : N₀ ≤ n) :
    UniformIntervalPhase.fractionLaw N₀ n ≤ (2 : ℝ≥0∞) • unitInterval := by
  rw [← (UniformIntervalPhase.scalar_marginal N₀ n hN (hN.trans_le hn)).2.2]
  have hb := UniformIntervalPhase.fractionDensity_le_two N₀ n hN hn
  have h := withDensity_mono (μ := unitInterval) (f := fun t =>
    ENNReal.ofReal (UniformIntervalPhase.fractionDensity N₀ n t))
    (g := fun _ => (2 : ℝ≥0∞)) (hb.mono fun t ht => by
      simpa using ENNReal.ofReal_le_ofReal ht)
  simpa only [withDensity_const, unitInterval] using h

theorem integral_sample_le_two {N₀ n : ℝ} (hN : 0 < N₀) (hn : N₀ ≤ n)
    (f : ℝ → ℝ) (hf : Integrable f unitInterval)
    (hf0 : ∀ᵐ t ∂unitInterval, 0 ≤ f t) :
    Integrable (fun a => f (Int.fract (n * a))) (UniformIntervalPhase.lambdaLaw N₀) ∧
      (∫ a, f (Int.fract (n * a)) ∂UniformIntervalPhase.lambdaLaw N₀) ≤
        2 * ∫ t, f t ∂unitInterval := by
  have hdom := fractionLaw_le_two hN hn
  have hfi := (hf.smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono_measure hdom
  have hm : Measurable (fun a : ℝ => Int.fract (n * a)) :=
    (measurable_const_mul n).fract
  refine ⟨hfi.comp_measurable hm, ?_⟩
  rw [← integral_map hm.aemeasurable hfi.aestronglyMeasurable]
  have hb := integral_mono_measure hdom (Measure.ae_smul_measure hf0 (2 : ℝ≥0∞))
    (hf.smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  simpa [integral_smul_measure, UniformIntervalPhase.fractionLaw] using hb

def mean (u : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := ∫ t, u s t ∂unitInterval

def sample (u : ℝ → ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  u p.2 (Int.fract ((n : ℝ) * p.1))

def realBVSize (f : ℝ → ℝ) : ℝ :=
  sSup ((fun t => |f t|) '' Icc (0 : ℝ) 1) +
    (eVariationOn f (Icc (0 : ℝ) 1)).toReal

theorem realBVSize_nonneg (f : ℝ → ℝ) : 0 ≤ realBVSize f := by
  apply add_nonneg _ ENNReal.toReal_nonneg
  apply Real.sSup_nonneg
  rintro _ ⟨t, _, rfl⟩
  exact abs_nonneg _

@[fun_prop] theorem measurable_sample {u : ℝ → ℝ → ℝ}
    (hu : Measurable (Function.uncurry u)) (n : ℕ) : Measurable (sample u n) := by
  exact hu.comp (measurable_snd.prodMk ((measurable_const_mul (n : ℝ)).comp measurable_fst).fract)

@[fun_prop] theorem measurable_mean {u : ℝ → ℝ → ℝ}
    (hu : Measurable (Function.uncurry u)) : Measurable (mean u) :=
  hu.stronglyMeasurable.integral_prod_right.measurable

theorem sample_memLp {u : ℝ → ℝ → ℝ} {N₀ C : ℝ} (hN : 0 < N₀)
    (hu : Measurable (Function.uncurry u))
    (hbound : ∀ s t, |u s t| ≤ C) (n : ℕ) :
    MemLp (sample u n) 2 ((UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hN
  apply MemLp.of_bound (measurable_sample hu n).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun p => by simpa [sample, Real.norm_eq_abs] using hbound p.2 _)

theorem mean_memLp {u : ℝ → ℝ → ℝ} {C : ℝ}
    (hu : Measurable (Function.uncurry u)) (hbound : ∀ s t, |u s t| ≤ C) :
    MemLp (mean u) 2 unitInterval := by
  apply MemLp.of_bound (measurable_mean hu).aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro s
  have h := norm_integral_le_of_norm_le_const (μ := unitInterval)
    (f := u s) (Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using hbound s t))
  simpa [mean] using h

theorem coordinate_pair_error_le {m : ℕ} (hm : 200 ≤ m)
    {N₀ N C V : ℝ} {n n' : ℕ} (hp : ScalarSampling.SamplingPair m N₀ N n n')
    (u : ℝ → ℝ → ℝ) (hu : Measurable (Function.uncurry u))
    (hbound : ∀ s t, |u s t| ≤ C)
    (hBV : ∀ s ∈ Ico (0 : ℝ) 1, BoundedVariationOn (u s) (Icc (0 : ℝ) 1))
    (hV : ∀ s ∈ Ico (0 : ℝ) 1, realBVSize (u s) ≤ V) :
    |(∫ p, sample u n p * sample u n' p ∂(UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) -
      (∫ s, (mean u s)^2 ∂unitInterval)| ≤ (29 / (m : ℝ)^80) * V^2 := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hp.N₀_pos
  have hv := sample_memLp hp.N₀_pos hu hbound n
  have hv' := sample_memLp hp.N₀_pos hu hbound n'
  have hz := mean_memLp hu hbound
  have hi : Integrable (fun p => sample u n p * sample u n' p)
      ((UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) := hv.integrable_mul hv'
  rw [integral_prod_symm _ hi, ← integral_sub hi.integral_prod_right hz.integrable_sq]
  have hb : ∀ s ∈ Ico (0 : ℝ) 1,
      |(∫ a, sample u n (a, s) * sample u n' (a, s)
          ∂UniformIntervalPhase.lambdaLaw N₀) - (mean u s)^2| ≤
        (29 / (m : ℝ)^80) * V^2 := by
    intro s hs
    have h := real_bv_discrepancy hm hp (u s) (u s) (hBV s hs) (hBV s hs)
    have hV0 : 0 ≤ V := (realBVSize_nonneg (u s)).trans (hV s hs)
    have hsquare : realBVSize (u s) * realBVSize (u s) ≤ V * V :=
      mul_le_mul (hV s hs) (hV s hs) (realBVSize_nonneg _) hV0
    calc
      _ ≤ (29 / (m : ℝ)^80) * realBVSize (u s) * realBVSize (u s) := by
        simpa only [sample, mean, integral_unitInterval, pow_two, realBVSize] using h
      _ ≤ _ := by
        rw [mul_assoc, pow_two]
        exact mul_le_mul_of_nonneg_left hsquare (by positivity)
  have h := norm_integral_le_of_norm_le_const (μ := unitInterval)
    (f := fun s => (∫ a, sample u n (a, s) * sample u n' (a, s)
      ∂UniformIntervalPhase.lambdaLaw N₀) - (mean u s)^2)
    (C := (29 / (m : ℝ)^80) * V^2)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
      simpa only [Real.norm_eq_abs] using hb s hs)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

theorem section_intervalIntegrable {u : ℝ → ℝ → ℝ} {C : ℝ}
    (hu : Measurable (Function.uncurry u)) (hbound : ∀ s t, |u s t| ≤ C) (s : ℝ) :
    IntervalIntegrable (u s) volume 0 1 := by
  have hm : Measurable (u s) := hu.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (u s) unitInterval :=
    (MemLp.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using hbound s t)) : MemLp (u s) 1 unitInterval).integrable le_rfl
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
  simpa only [unitInterval, IntegrableOn, restrict_Ico_eq_restrict_Ioc] using hi

theorem coordinate_cross_error_le {N₀ C : ℝ} (hN : 0 < N₀)
    {n : ℕ} (hn : 0 < n)
    (u : ℝ → ℝ → ℝ) (hu : Measurable (Function.uncurry u))
    (hbound : ∀ s t, |u s t| ≤ C) (hzero : ∀ s t, 0 ≤ u s t) :
    |(∫ p, sample u n p * mean u p.2 ∂(UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) -
      (∫ s, (mean u s)^2 ∂unitInterval)| ≤
        (N₀ / (n : ℝ)) * ∫ s, (mean u s)^2 ∂unitInterval := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hN
  have hv := sample_memLp hN hu hbound n
  have hz := mean_memLp hu hbound
  have hi : Integrable (fun p : ℝ × ℝ => sample u n p * mean u p.2)
      ((UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) :=
    hv.integrable_mul (hz.comp_snd (UniformIntervalPhase.lambdaLaw N₀))
  rw [integral_prod_symm _ hi, ← integral_sub hi.integral_prod_right hz.integrable_sq]
  have hdiff := hi.integral_prod_right.sub hz.integrable_sq
  have hb (s : ℝ) :
      |(∫ a, sample u n (a, s) * mean u s ∂UniformIntervalPhase.lambdaLaw N₀) -
        (mean u s)^2| ≤ (N₀ / (n : ℝ)) * (mean u s)^2 := by
    have hz0 : 0 ≤ mean u s := integral_nonneg (hzero s)
    have he := real_one_phase_error (n := (n : ℝ)) hN (by exact_mod_cast hn)
      (section_intervalIntegrable hu hbound s) (fun t _ => hzero s t)
    rw [← integral_unitInterval] at he
    change |(∫ a, sample u n (a, s) ∂UniformIntervalPhase.lambdaLaw N₀) - mean u s| ≤
      (N₀ / (n : ℝ)) * mean u s at he
    rw [integral_mul_const]
    calc
      _ = |((∫ a, sample u n (a, s) ∂UniformIntervalPhase.lambdaLaw N₀) -
          mean u s) * mean u s| := by congr 1; ring
      _ = |(∫ a, sample u n (a, s) ∂UniformIntervalPhase.lambdaLaw N₀) -
          mean u s| * mean u s := by rw [abs_mul, abs_of_nonneg hz0]
      _ ≤ ((N₀ / (n : ℝ)) * mean u s) * mean u s :=
        mul_le_mul_of_nonneg_right he hz0
      _ = _ := by ring
  calc
    _ ≤ ∫ s, |(∫ a, sample u n (a, s) * mean u s
          ∂UniformIntervalPhase.lambdaLaw N₀) - (mean u s)^2| ∂unitInterval :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s, (N₀ / (n : ℝ)) * (mean u s)^2 ∂unitInterval :=
      integral_mono_ae hdiff.abs (hz.integrable_sq.const_mul _)
        (Filter.Eventually.of_forall hb)
    _ = _ := integral_const_mul _ _

theorem coordinate_square_le_two {N₀ C : ℝ} (hN : 0 < N₀)
    {n : ℕ} (hn : N₀ ≤ (n : ℝ))
    (u : ℝ → ℝ → ℝ) (hu : Measurable (Function.uncurry u))
    (hbound : ∀ s t, |u s t| ≤ C) :
    (∫ p, (sample u n p)^2 ∂(UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) ≤
      2 * ∫ s, ∫ t, (u s t)^2 ∂unitInterval ∂unitInterval := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hN
  have hv := sample_memLp hN hu hbound n
  have hkernel : MemLp (Function.uncurry u) 2 (unitInterval.prod unitInterval) := by
    apply MemLp.of_bound hu.aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs, Function.uncurry] using hbound p.1 p.2)
  have hi : Integrable (fun p => (sample u n p)^2)
      ((UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) := hv.integrable_sq
  rw [integral_prod_symm _ hi, ← integral_const_mul]
  apply integral_mono_ae hi.integral_prod_right
    (hkernel.integrable_sq.integral_prod_left.const_mul 2)
  apply Filter.Eventually.of_forall
  intro s
  have hm : Measurable (u s) := hu.comp (measurable_const.prodMk measurable_id)
  have hs : MemLp (u s) 2 unitInterval := by
    apply MemLp.of_bound hm.aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hbound s t)
  exact (integral_sample_le_two hN hn (fun t => (u s t)^2) hs.integrable_sq
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).2

theorem coordinate_cross_error_le_four {N₀ C : ℝ} (hN : 0 < N₀)
    {n : ℕ} (hn : 0 < n)
    (u : ℝ → ℝ → ℝ) (hu : Measurable (Function.uncurry u))
    (hbound : ∀ s t, |u s t| ≤ C) (hzero : ∀ s t, 0 ≤ u s t)
    (hmean : ∀ s, mean u s ≤ 2) :
    |(∫ p, sample u n p * mean u p.2 ∂(UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) -
      (∫ s, (mean u s)^2 ∂unitInterval)| ≤ 4 * N₀ / (n : ℝ) := by
  have hA : (∫ s, (mean u s)^2 ∂unitInterval) ≤ 4 := by
    have hb (s : ℝ) : (mean u s)^2 ≤ 4 := by
      have h0 : 0 ≤ mean u s := integral_nonneg (hzero s)
      nlinarith [hmean s]
    simpa using integral_mono_ae (mean_memLp hu hbound).integrable_sq
      (integrable_const (4 : ℝ)) (Filter.Eventually.of_forall hb)
  calc
    _ ≤ (N₀ / (n : ℝ)) * ∫ s, (mean u s)^2 ∂unitInterval :=
      coordinate_cross_error_le hN hn u hu hbound hzero
    _ ≤ (N₀ / (n : ℝ)) * 4 := mul_le_mul_of_nonneg_left hA (by positivity)
    _ = _ := by ring

theorem expected_average_error_le {κ : Type*} [Fintype κ]
    {m : ℕ} (hm : 200 ≤ m) (N₀ : κ → ℝ) (hN : ∀ i, 0 < N₀ i)
    (N : ℝ) (powers : Finset ℕ) (hpowers : powers.Nonempty)
    (hpositive : ∀ n ∈ powers, 0 < n)
    (hlarge : ∀ n ∈ powers, ∀ i, N₀ i ≤ (n : ℝ))
    (hseparated : ∀ n ∈ powers, ∀ n' ∈ powers, n ≠ n' → ∀ i,
      ScalarSampling.SamplingPair m (N₀ i) N n n')
    (u : κ → ℝ → ℝ → ℝ) (C : κ → ℝ)
    (hu : ∀ i, Measurable (Function.uncurry (u i)))
    (hbound : ∀ i s t, |u i s t| ≤ C i)
    (hzero : ∀ i s t, 0 ≤ u i s t)
    (hmean : ∀ i s, mean (u i) s ≤ 2)
    {B D V ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hBV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → BoundedVariationOn (u i s) (Icc (0 : ℝ) 1))
    (hV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → realBVSize (u i s) ≤ V)
    (hbase : ∀ i, (∫ s, (mean (u i) s)^2 ∂unitInterval) ≤ B)
    (hsquare : ∀ i, (∫ s, ∫ t, (u i s t)^2 ∂unitInterval ∂unitInterval) ≤ D)
    (hpairBudget : (29 / (m : ℝ)^80) * V^2 ≤ ε)
    (hcrossBudget : ∀ n ∈ powers, ∀ i, 4 * N₀ i / (n : ℝ) ≤ ε) :
    (∫ a, ∫ x, ((powers.card : ℝ)⁻¹ *
        (∑ n ∈ powers, ∏ i, u i (x i) (Int.fract ((n : ℝ) * a i))) -
        ∏ i, mean (u i) (x i))^2
      ∂Measure.pi (fun _ : κ => unitInterval)
      ∂Measure.pi (fun i => UniformIntervalPhase.lambdaLaw (N₀ i))) ≤
      (2 * D)^Fintype.card κ / (powers.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * ε * (B + ε)^(Fintype.card κ - 1)) := by
  let (i : κ) : IsProbabilityMeasure (UniformIntervalPhase.lambdaLaw (N₀ i)) :=
    UniformIntervalPhase.lambdaLaw_probability (N₀ i) (hN i)
  apply InvariantRotation.SamplingMomentBounds.expected_integral_average_products_sub_sq_le
    (fun i => UniformIntervalPhase.lambdaLaw (N₀ i)) (fun _ : κ => unitInterval)
    powers hpowers (fun n i a x => u i x (Int.fract ((n : ℝ) * a)))
    (fun i => mean (u i))
  · intro n i
    exact sample_memLp (hN i) (hu i) (hbound i) n
  · intro i
    exact mean_memLp (hu i) (hbound i)
  · exact hB
  · exact hε
  · exact hbase
  · intro n hn i
    exact (coordinate_square_le_two (hN i) (hlarge n hn i) (u i) (hu i) (hbound i)).trans
      (mul_le_mul_of_nonneg_left (hsquare i) (by norm_num))
  · intro n hn n' hn' hnn' i
    exact (coordinate_pair_error_le hm (hseparated n hn n' hn' hnn' i)
      (u i) (hu i) (hbound i) (hBV i) (hV i)).trans hpairBudget
  · intro n hn i
    exact (coordinate_cross_error_le_four (hN i) (hpositive n hn)
      (u i) (hu i) (hbound i) (hzero i) (hmean i)).trans (hcrossBudget n hn i)

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
