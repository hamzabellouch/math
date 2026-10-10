import OAI.Analysis.IrrationalRotation.Analysis.FejerApproximation
import OAI.Analysis.IrrationalRotation.Analysis.IntervalIndicatorTranslation
import OAI.Analysis.IrrationalRotation.Analysis.UniformIntervalFourier
import OAI.Analysis.IrrationalRotation.Sampling.UniformIntervalPhase

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.ScalarRectangles

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  norm_num
  infer_instance

def intervalTest (a b : ℝ) (x : UnitAddCircle) : ℝ :=
  (Icc a b).indicator (fun _ => 1) (UniformIntervalPhase.representative x)

theorem measurable_intervalTest (a b : ℝ) : Measurable (intervalTest a b) :=
  (measurable_const.indicator measurableSet_Icc).comp
    UniformIntervalPhase.measurable_representative

theorem intervalTest_bounds (a b : ℝ) (x : UnitAddCircle) :
    0 ≤ intervalTest a b x ∧ intervalTest a b x ≤ 1 := by
  unfold intervalTest
  by_cases h : UniformIntervalPhase.representative x ∈ Icc a b <;> simp [h]

theorem intervalTest_translation (a b : ℝ) {η : ℝ} (hη : 0 ≤ η)
    (t : UnitAddCircle) (ht : dist t 0 ≤ η) :
    CircleKernelConvolution.translationError (intervalTest a b) t ≤ 6 * η := by
  induction t using QuotientAddGroup.induction_on with
  | H u =>
    have hround : (((round u : ℤ) : ℝ) : UnitAddCircle) = 0 := by
      have hc := AddCircle.coe_zsmul (p := (1 : ℝ)) (n := round u) (x := (1 : ℝ))
      simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using hc
    have hcoe : ((u - round u : ℝ) : UnitAddCircle) = (u : UnitAddCircle) := by
      rw [QuotientAddGroup.mk_sub, hround, sub_zero]
    have hu : |u - round u| ≤ η := by
      simpa only [dist_zero_right, UnitAddCircle.norm_eq] using ht
    have h := IntervalIndicatorTranslation.circle_integral_indicator_translation_le
      (a := a) (b := b) hη hu
    rw [hcoe] at h
    exact h

theorem kernel_tail_le (H : ℕ) (hH : H ≠ 0) {η : ℝ} (hη : 0 < η) :
    (∫ t in {x : UnitAddCircle | dist x 0 ≤ η}ᶜ, Fejer.kernel H t) ≤
      1 / (4 * (H : ℝ) * η ^ 2) := by
  have hB : MeasurableSet {x : UnitAddCircle | dist x 0 ≤ η} :=
    isClosed_le (continuous_id.dist continuous_const) continuous_const |>.measurableSet
  have hk : Integrable (Fejer.kernel H) (volume : Measure UnitAddCircle) :=
    (Fejer.continuous_kernel H).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_indicator hB.compl]
  have hbound : ∀ t : UnitAddCircle,
      {x : UnitAddCircle | dist x 0 ≤ η}ᶜ.indicator (Fejer.kernel H) t ≤
        1 / (4 * (H : ℝ) * η ^ 2) := by
    intro t
    by_cases ht : t ∈ {x : UnitAddCircle | dist x 0 ≤ η}ᶜ
    · rw [Set.indicator_of_mem ht]
      exact Fejer.kernel_le_of_distance_ge H hH hη t (le_of_lt (not_le.mp ht))
    · rw [Set.indicator_of_notMem ht]
      positivity
  have hi := integral_mono (hk.indicator hB.compl) (integrable_const
    (1 / (4 * (H : ℝ) * η ^ 2))) hbound
  simpa using hi

theorem interval_approximation_error (H : ℕ) (hH : H ≠ 0)
    (a b : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ x : UnitAddCircle, |Fejer.approximation H (intervalTest a b) x -
      intervalTest a b x|) ≤ 6 * η + 1 / (4 * (H : ℝ) * η ^ 2) := by
  apply Fejer.approximation_l1_error_le H hH (measurable_intervalTest a b)
    (fun x => (intervalTest_bounds a b x).1) (fun x => (intervalTest_bounds a b x).2)
    (B := {x : UnitAddCircle | dist x 0 ≤ η})
  · exact (isClosed_le (continuous_id.dist continuous_const) continuous_const).measurableSet
  · positivity
  · exact fun t ht => intervalTest_translation a b hη.le t ht
  · exact kernel_tail_le H hH hη

private theorem integrable_unit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℂ}
    (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ 1) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb)

theorem rectangle_error_of_character_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → UnitAddCircle) (hX : Measurable X) (hY : Measurable Y)
    (hmapX : μ.map X ≤ (2 : ℝ≥0∞) • volume)
    (hmapY : μ.map Y ≤ (2 : ℝ≥0∞) • volume)
    (H : ℕ) (hH : H ≠ 0) (a b c d : ℝ) {η ε : ℝ}
    (hη : 0 < η) (hε : 0 ≤ ε)
    (hchar : ∀ i ∈ Fejer.frequencies H, ∀ j ∈ Fejer.frequencies H,
      (i, j) ≠ (0, 0) →
      ‖∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ‖ ≤ ε) :
    ‖(∫ ω, (intervalTest a b (X ω) : ℂ) * (intervalTest c d (Y ω) : ℂ) ∂μ) -
      (∫ x : UnitAddCircle, intervalTest a b x : ℝ) *
      (∫ x : UnitAddCircle, intervalTest c d x : ℝ)‖ ≤
      4 * (6 * η + 1 / (4 * (H : ℝ) * η ^ 2)) + (2 * (H : ℝ)) ^ 2 * ε := by
  let f := intervalTest a b
  let g := intervalTest c d
  let p := Fejer.approximation H f
  let q := Fejer.approximation H g
  have hf := measurable_intervalTest a b
  have hg := measurable_intervalTest c d
  have hf0 := fun x => (intervalTest_bounds a b x).1
  have hf1 := fun x => (intervalTest_bounds a b x).2
  have hg0 := fun x => (intervalTest_bounds c d x).1
  have hg1 := fun x => (intervalTest_bounds c d x).2
  have hpcont : Continuous p := Fejer.continuous_approximation H hf hf0 hf1
  have hqcont : Continuous q := Fejer.continuous_approximation H hg hg0 hg1
  have hpb : ∀ x, 0 ≤ p x ∧ p x ≤ 1 := Fejer.approximation_bounds H hH hf hf0 hf1
  have hqb : ∀ x, 0 ≤ q x ∧ q x ≤ 1 := Fejer.approximation_bounds H hH hg hg0 hg1
  have hfn : ∀ x, ‖(f x : ℂ)‖ ≤ 1 := fun x => by
    simpa only [f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hf1 x
  have hgn : ∀ x, ‖(g x : ℂ)‖ ≤ 1 := fun x => by
    simpa only [g, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 x)] using hg1 x
  have hpn : ∀ x, ‖(p x : ℂ)‖ ≤ 1 := fun x => by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpb x).1] using (hpb x).2
  have hqn : ∀ x, ‖(q x : ℂ)‖ ≤ 1 := fun x => by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hqb x).1] using (hqb x).2
  have hfX := (Complex.measurable_ofReal.comp hf).comp hX
  have hgY := (Complex.measurable_ofReal.comp hg).comp hY
  have hpX := (Complex.measurable_ofReal.comp hpcont.measurable).comp hX
  have hqY := (Complex.measurable_ofReal.comp hqcont.measurable).comp hY
  have hfi := integrable_unit μ hfX (fun ω => hfn (X ω))
  have hgi := integrable_unit μ hgY (fun ω => hgn (Y ω))
  have hpi := integrable_unit μ hpX (fun ω => hpn (X ω))
  have hqi := integrable_unit μ hqY (fun ω => hqn (Y ω))
  have hfg := hgi.bdd_mul hfX.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => hfn (X ω))
  have hpq := hqi.bdd_mul hpX.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => hpn (X ω))
  have hfvol := integrable_unit (volume : Measure UnitAddCircle)
    (Complex.measurable_ofReal.comp hf) hfn
  have hgvol := integrable_unit (volume : Measure UnitAddCircle)
    (Complex.measurable_ofReal.comp hg) hgn
  have hpvol := integrable_unit (volume : Measure UnitAddCircle)
    (Complex.measurable_ofReal.comp hpcont.measurable) hpn
  have hqvol := integrable_unit (volume : Measure UnitAddCircle)
    (Complex.measurable_ofReal.comp hqcont.measurable) hqn
  have herrX := FourierSampling.marginal_l1_error_le hX (by norm_num : (0 : ℝ) ≤ 2)
    (by simpa using hmapX) (hfvol.sub hpvol)
  have herrY := FourierSampling.marginal_l1_error_le hY (by norm_num : (0 : ℝ) ≤ 2)
    (by simpa using hmapY) (hgvol.sub hqvol)
  have herrf : (∫ x : UnitAddCircle, ‖(f x : ℂ) - (p x : ℂ)‖) ≤
      6 * η + 1 / (4 * (H : ℝ) * η ^ 2) := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      using interval_approximation_error H hH a b hη
  have herrg : (∫ x : UnitAddCircle, ‖(g x : ℂ) - (q x : ℂ)‖) ≤
      6 * η + 1 / (4 * (H : ℝ) * η ^ 2) := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      using interval_approximation_error H hH c d hη
  have hzero : 0 ∈ Fejer.frequencies H := by
    simp only [Fejer.frequencies, Finset.mem_Ioo]
    have hpos := Nat.pos_of_ne_zero hH
    constructor <;> omega
  have heqp (x : UnitAddCircle) : FourierSampling.polynomial (Fejer.frequencies H)
      (Fejer.approximationCoefficient H f) x = (p x : ℂ) :=
    (Fejer.approximation_eq_polynomial H hf hf0 hf1 x).symm
  have heqq (x : UnitAddCircle) : FourierSampling.polynomial (Fejer.frequencies H)
      (Fejer.approximationCoefficient H g) x = (q x : ℂ) :=
    (Fejer.approximation_eq_polynomial H hg hg0 hg1 x).symm
  have hmain := FourierSampling.test_error_le hX hY
    (Fejer.frequencies H) (Fejer.frequencies H) hzero hzero
    (Fejer.approximationCoefficient H f) (Fejer.approximationCoefficient H g)
    hfg (by simpa only [heqp, heqq, Function.comp_apply] using hpq)
    (by simp only [heqp]; exact hfi.sub hpi)
    (by simp only [heqq]; exact hgi.sub hqi)
    (Filter.Eventually.of_forall fun ω => hgn (Y ω))
    (by simpa only [heqp] using Filter.Eventually.of_forall fun ω => hpn (X ω))
    (fun i _ => Fejer.approximationCoefficient_norm_le_one H hH hf hf0 hf1 i)
    (fun j _ => Fejer.approximationCoefficient_norm_le_one H hH hg hg0 hg1 j)
    hε hchar
  simp only [Fejer.approximationCoefficient_zero H hH, heqp, heqq] at hmain
  have hcard : ((Fejer.frequencies H).card : ℝ) ≤ 2 * (H : ℝ) := by
    exact_mod_cast Fejer.card_frequencies_le H
  have hcard2 : ((Fejer.frequencies H).card : ℝ) * (Fejer.frequencies H).card * ε ≤
      (2 * (H : ℝ)) ^ 2 * ε := by
    apply mul_le_mul_of_nonneg_right _ hε
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fejer.frequencies H).card]
  dsimp only [Function.comp_apply, f, g] at herrX herrY herrf herrg hmain ⊢
  exact hmain.trans (by nlinarith only [herrX, herrY, herrf, herrg, hcard2])

theorem sampled_character_pair (i j : ℤ) (n n' t : ℝ) :
    fourier i ((n * t : ℝ) : UnitAddCircle) *
      fourier j ((n' * t : ℝ) : UnitAddCircle) =
      Complex.exp ((((2 * Real.pi * ((i : ℝ) * n + (j : ℝ) * n')) * t : ℝ) : ℂ) *
        Complex.I) := by
  rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sampling_rectangle_error
    {N₀ N m n n' : ℝ} (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hm : 0 < m)
    (hn : N₀ ≤ n) (hn' : N₀ ≤ n') (H : ℕ) (hH : H ≠ 0)
    (hsep : ∀ i j : ℤ, |i| ≤ (H : ℤ) → |j| ≤ (H : ℤ) →
      (i, j) ≠ (0, 0) → N * m ^ 1000 < |(i : ℝ) * n + (j : ℝ) * n'|)
    (a b c d : ℝ) {η : ℝ} (hη : 0 < η) :
    ‖(∫ t, (intervalTest a b ((n * t : ℝ) : UnitAddCircle) : ℂ) *
        (intervalTest c d ((n' * t : ℝ) : UnitAddCircle) : ℂ)
        ∂UniformIntervalPhase.lambdaLaw N₀) -
      (∫ x : UnitAddCircle, intervalTest a b x : ℝ) *
      (∫ x : UnitAddCircle, intervalTest c d x : ℝ)‖ ≤
      4 * (6 * η + 1 / (4 * (H : ℝ) * η ^ 2)) +
        (2 * (H : ℝ)) ^ 2 / m ^ 1000 := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hN₀
  have hX : Measurable (fun t : ℝ => ((n * t : ℝ) : UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (measurable_const_mul n)
  have hY : Measurable (fun t : ℝ => ((n' * t : ℝ) : UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (measurable_const_mul n')
  have hchar : ∀ i ∈ Fejer.frequencies H, ∀ j ∈ Fejer.frequencies H,
      (i, j) ≠ (0, 0) →
      ‖∫ t, fourier i ((n * t : ℝ) : UnitAddCircle) *
        fourier j ((n' * t : ℝ) : UnitAddCircle)
        ∂UniformIntervalPhase.lambdaLaw N₀‖ ≤ 1 / m ^ 1000 := by
    intro i hi j hj hij
    have hi' : |i| ≤ (H : ℤ) := by
      simp only [Fejer.frequencies, Finset.mem_Ioo] at hi
      exact abs_le.mpr ⟨hi.1.le, hi.2.le⟩
    have hj' : |j| ≤ (H : ℤ) := by
      simp only [Fejer.frequencies, Finset.mem_Ioo] at hj
      exact abs_le.mpr ⟨hj.1.le, hj.2.le⟩
    simp_rw [sampled_character_pair]
    rw [UniformIntervalPhase.lambdaLaw_eq_cond N₀ hN₀]
    apply (UniformIntervalFourier.norm_sampling_interval_character_le_of_separation
      hN₀ hN hm (hsep i j hi' hj' hij)).trans
    apply one_div_le_one_div_of_le (pow_pos hm _)
    nlinarith [Real.pi_gt_three, pow_pos hm 1000]
  have h := rectangle_error_of_character_bounds (UniformIntervalPhase.lambdaLaw N₀)
    _ _ hX hY (UniformIntervalPhase.sampled_circle_le_two N₀ n hN₀ hn)
    (UniformIntervalPhase.sampled_circle_le_two N₀ n' hN₀ hn')
    H hH a b c d hη (by positivity : 0 ≤ 1 / m ^ 1000) hchar
  simpa only [mul_one_div] using h

theorem integral_intervalTest (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ x : UnitAddCircle, intervalTest a b x) = b - a := by
  have hf : Measurable ((Icc a b).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator measurableSet_Icc
  have h := integral_map (μ := (volume : Measure UnitAddCircle))
    UniformIntervalPhase.measurable_representative.aemeasurable
    hf.aestronglyMeasurable
  rw [UniformIntervalPhase.map_representative_haar] at h
  change (∫ x : UnitAddCircle, (Icc a b).indicator (fun _ => (1 : ℝ))
    (UniformIntervalPhase.representative x)) = b - a
  rw [← h, integral_indicator_const 1 measurableSet_Icc,
    measureReal_restrict_apply measurableSet_Icc, smul_eq_mul, mul_one]
  have heq : (Icc a b ∩ Ico (0 : ℝ) 1 : Set ℝ) =ᵐ[volume]
      (Icc a b ∩ Icc (0 : ℝ) 1 : Set ℝ) :=
    Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl Ico_ae_eq_Icc
  rw [measureReal_congr heq, Set.inter_eq_left.mpr (Icc_subset_Icc ha hb)]
  exact Real.volume_real_Icc_of_le hab

theorem integral_sample_interval_product (N₀ n n' a b c d : ℝ) :
    (∫ t, (intervalTest a b ((n * t : ℝ) : UnitAddCircle) : ℂ) *
      (intervalTest c d ((n' * t : ℝ) : UnitAddCircle) : ℂ)
      ∂UniformIntervalPhase.lambdaLaw N₀) =
      ((UniformIntervalPhase.lambdaLaw N₀).real
        {t : ℝ | Int.fract (n * t) ∈ Icc a b ∧ Int.fract (n' * t) ∈ Icc c d} : ℂ) := by
  have hs : MeasurableSet
      {t : ℝ | Int.fract (n * t) ∈ Icc a b ∧ Int.fract (n' * t) ∈ Icc c d} :=
    (measurableSet_Icc.preimage (measurable_fract.comp (measurable_const_mul n))).inter
      (measurableSet_Icc.preimage (measurable_fract.comp (measurable_const_mul n')))
  have heq : (fun t => (intervalTest a b ((n * t : ℝ) : UnitAddCircle) : ℂ) *
      (intervalTest c d ((n' * t : ℝ) : UnitAddCircle) : ℂ)) =
      {t : ℝ | Int.fract (n * t) ∈ Icc a b ∧ Int.fract (n' * t) ∈ Icc c d}.indicator
        (fun _ => (1 : ℂ)) := by
    funext t
    simp only [intervalTest, UniformIntervalPhase.representative_coe, Set.indicator_apply,
      Set.mem_ofPred_eq]
    by_cases hi : Int.fract (n * t) ∈ Icc a b <;>
      by_cases hj : Int.fract (n' * t) ∈ Icc c d <;> simp [hi, hj]
  rw [heq, integral_indicator_const 1 hs]
  simp

theorem sampling_rectangle_probability_error
    {N₀ N m n n' : ℝ} (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hm : 0 < m)
    (hn : N₀ ≤ n) (hn' : N₀ ≤ n') (H : ℕ) (hH : H ≠ 0)
    (hsep : ∀ i j : ℤ, |i| ≤ (H : ℤ) → |j| ≤ (H : ℤ) →
      (i, j) ≠ (0, 0) → N * m ^ 1000 < |(i : ℝ) * n + (j : ℝ) * n'|)
    (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) {η : ℝ} (hη : 0 < η) :
    |(UniformIntervalPhase.lambdaLaw N₀).real
        {t : ℝ | Int.fract (n * t) ∈ Icc a b ∧ Int.fract (n' * t) ∈ Icc c d} -
      (b - a) * (d - c)| ≤
      4 * (6 * η + 1 / (4 * (H : ℝ) * η ^ 2)) +
        (2 * (H : ℝ)) ^ 2 / m ^ 1000 := by
  have h := sampling_rectangle_error hN₀ hN hm hn hn' H hH hsep a b c d hη
  rw [integral_sample_interval_product, integral_intervalTest a b ha hab hb,
    integral_intervalTest c d hc hcd hd] at h
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using h

theorem horizon_ge_twice_square {m : ℝ} (hm : 200 ≤ m) :
    2 * m ^ 2 ≤ m ^ ((7 / 10 : ℝ) * m) := by
  have hm1 : 1 ≤ m := by linarith
  calc
    2 * m ^ 2 ≤ m ^ 3 := by nlinarith [sq_nonneg m]
    _ = m ^ (3 : ℝ) := (Real.rpow_natCast m 3).symm
    _ ≤ m ^ ((7 / 10 : ℝ) * m) :=
      Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)

theorem numerical_rectangle_error {m : ℝ} (hm : 1 ≤ m) :
    4 * (6 * (1 / m ^ 80) + 1 / (4 * m ^ 300 * (1 / m ^ 80) ^ 2)) +
      (2 * m ^ 300) ^ 2 / m ^ 1000 ≤ 29 / m ^ 80 := by
  have hm0 : 0 < m := by linarith
  have heq :
      4 * (6 * (1 / m ^ 80) + 1 / (4 * m ^ 300 * (1 / m ^ 80) ^ 2)) +
        (2 * m ^ 300) ^ 2 / m ^ 1000 =
          24 / m ^ 80 + 1 / m ^ 140 + 4 / m ^ 400 := by
    field_simp
    ring
  rw [heq]
  have h140 : 1 / m ^ 140 ≤ 1 / m ^ 80 :=
    one_div_le_one_div_of_le (pow_pos hm0 _) (pow_le_pow_right₀ hm (by norm_num))
  have h400 : 4 / m ^ 400 ≤ 4 / m ^ 80 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hm0 _)
      (pow_le_pow_right₀ hm (by norm_num))
  calc
    _ ≤ 24 / m ^ 80 + 1 / m ^ 80 + 4 / m ^ 80 :=
      add_le_add (add_le_add le_rfl h140) h400
    _ = 29 / m ^ 80 := by ring

theorem scalar_rectangles (m : ℕ) (hm : 200 ≤ m)
    (N₀ N : ℝ) (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hNm : N ≤ (m : ℝ) ^ 2)
    (n n' : ℕ)
    (hn : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n)
    (hn' : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n')
    (hsep : ∀ i j : ℤ, |i| ≤ (m ^ 300 : ℕ) → |j| ≤ (m ^ 300 : ℕ) →
      (i, j) ≠ (0, 0) →
      N * (m : ℝ) ^ 1000 < |(i : ℝ) * n + (j : ℝ) * n'|)
    (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    |(UniformIntervalPhase.lambdaLaw N₀).real
        {t : ℝ | Int.fract ((n : ℝ) * t) ∈ Icc a b ∧
          Int.fract ((n' : ℝ) * t) ∈ Icc c d} - (b - a) * (d - c)| ≤
      29 / (m : ℝ) ^ 80 := by
  have hmr : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hmn : m ≠ 0 := by omega
  have hhor := horizon_ge_twice_square hmr
  have hnN : N₀ ≤ (n : ℝ) := by linarith
  have hn'N : N₀ ≤ (n' : ℝ) := by linarith
  have h := sampling_rectangle_probability_error hN₀ hN hm0 hnN hn'N
    (m ^ 300) (pow_ne_zero _ hmn) hsep a b c d ha hab hb hc hcd hd
    (η := 1 / (m : ℝ) ^ 80) (by positivity)
  simp only [Nat.cast_pow] at h
  exact h.trans (numerical_rectangle_error (by linarith))

theorem sampled_fraction_absolutelyContinuous (N₀ n : ℝ) (hN₀ : 0 < N₀) (hn : 0 < n) :
    (UniformIntervalPhase.lambdaLaw N₀).map (fun t => Int.fract (n * t)) ≪
      volume.restrict (Icc (0 : ℝ) 1) := by
  have hac : UniformIntervalPhase.fractionLaw N₀ n ≪ volume.restrict (Ico (0 : ℝ) 1) := by
    rw [← (UniformIntervalPhase.scalar_marginal N₀ n hN₀ hn).2.2]
    exact withDensity_absolutelyContinuous _ _
  simpa only [UniformIntervalPhase.fractionLaw, restrict_Ico_eq_restrict_Icc] using hac

theorem sampled_fraction_ae_eq {E : Type*} (N₀ n : ℝ)
    (hN₀ : 0 < N₀) (hn : 0 < n) {f g : ℝ → E} (hfg : f =ᵐ[volume] g) :
    (fun t => f (Int.fract (n * t))) =ᵐ[UniformIntervalPhase.lambdaLaw N₀]
      (fun t => g (Int.fract (n * t))) := by
  have h := (sampled_fraction_absolutelyContinuous N₀ n hN₀ hn).ae_eq
    (ae_restrict_of_ae hfg)
  exact ae_of_ae_map (measurable_fract.comp (measurable_const_mul n)).aemeasurable h

theorem rectangle_probability_congr (N₀ n n' : ℝ)
    (hN₀ : 0 < N₀) (hn : 0 < n) (hn' : 0 < n')
    {s s' t t' : Set ℝ} (hs : s =ᵐ[volume] s') (ht : t =ᵐ[volume] t') :
    (UniformIntervalPhase.lambdaLaw N₀).real
        {x | Int.fract (n * x) ∈ s ∧ Int.fract (n' * x) ∈ t} =
      (UniformIntervalPhase.lambdaLaw N₀).real
        {x | Int.fract (n * x) ∈ s' ∧ Int.fract (n' * x) ∈ t'} := by
  apply measureReal_congr
  filter_upwards [sampled_fraction_ae_eq N₀ n hN₀ hn hs,
    sampled_fraction_ae_eq N₀ n' hN₀ hn' ht] with x hx hy
  exact congrArg₂ And hx hy

theorem scalar_rectangles_ae (m : ℕ) (hm : 200 ≤ m)
    (N₀ N : ℝ) (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hNm : N ≤ (m : ℝ) ^ 2)
    (n n' : ℕ)
    (hn : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n)
    (hn' : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n')
    (hsep : ∀ i j : ℤ, |i| ≤ (m ^ 300 : ℕ) → |j| ≤ (m ^ 300 : ℕ) →
      (i, j) ≠ (0, 0) →
      N * (m : ℝ) ^ 1000 < |(i : ℝ) * n + (j : ℝ) * n'|)
    (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1)
    (s t : Set ℝ) (hs : s =ᵐ[volume] Icc a b) (ht : t =ᵐ[volume] Icc c d) :
    |(UniformIntervalPhase.lambdaLaw N₀).real
        {x : ℝ | Int.fract ((n : ℝ) * x) ∈ s ∧
          Int.fract ((n' : ℝ) * x) ∈ t} - (b - a) * (d - c)| ≤
      29 / (m : ℝ) ^ 80 := by
  have hmr : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : 0 < (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 := by
    apply div_pos (Real.rpow_pos_of_pos (by linarith) _) (by norm_num)
  rw [rectangle_probability_congr N₀ n n' hN₀ (hmp.trans_le hn) (hmp.trans_le hn') hs ht]
  exact scalar_rectangles m hm N₀ N hN₀ hN hNm n n' hn hn' hsep a b c d ha hab hb hc hcd hd

theorem scalar_tail_rectangles_integral (m : ℕ) (hm : 200 ≤ m)
    (N₀ N : ℝ) (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hNm : N ≤ (m : ℝ) ^ 2)
    (n n' : ℕ)
    (hn : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n)
    (hn' : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n')
    (hsep : ∀ i j : ℤ, |i| ≤ (m ^ 300 : ℕ) → |j| ≤ (m ^ 300 : ℕ) →
      (i, j) ≠ (0, 0) →
      N * (m : ℝ) ^ 1000 < |(i : ℝ) * n + (j : ℝ) * n'|)
    (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    ‖(∫ t, (Icc a 1).indicator (fun _ => (1 : ℂ)) (Int.fract ((n : ℝ) * t)) *
        (Icc b 1).indicator (fun _ => (1 : ℂ)) (Int.fract ((n' : ℝ) * t))
        ∂UniformIntervalPhase.lambdaLaw N₀) - ((1 - a) * (1 - b) : ℝ)‖ ≤
      29 / (m : ℝ) ^ 80 := by
  have h := scalar_rectangles m hm N₀ N hN₀ hN hNm n n' hn hn' hsep
    a 1 b 1 ha.1 ha.2 le_rfl hb.1 hb.2 le_rfl
  have heq (u v z : ℝ) :
      (intervalTest u v (z : UnitAddCircle) : ℂ) =
        (Icc u v).indicator (fun _ => (1 : ℂ)) (Int.fract z) := by
    simp only [intervalTest, UniformIntervalPhase.representative_coe, Set.indicator_apply]
    split_ifs <;> simp
  have hid := integral_sample_interval_product N₀ n n' a 1 b 1
  simp_rw [heq] at hid
  rw [hid, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact h

end Invariant233.ScalarRectangles

end

end OAI
