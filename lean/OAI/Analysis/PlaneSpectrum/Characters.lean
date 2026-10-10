import OAI.Analysis.PlaneSpectrum.Basic

namespace OAI

noncomputable section
open scoped ComplexConjugate

noncomputable section
open scoped BigOperators
namespace PlaneFiveColor.ContinuousCharacters

theorem abs_arg_exp_le (t : ℝ) : |Complex.arg (Circle.exp t : ℂ)| ≤ |t| := by
  by_cases h : |t| ≤ Real.pi
  · rcases (abs_le.mp h) with ⟨hl, hr⟩
    rcases eq_or_lt_of_le hl with hh | hh
    · have ht : t = -Real.pi := hh.symm
      rw [ht, Circle.coe_exp]
      simp [Complex.arg_neg_one]
    · rw [Circle.arg_exp hh hr]
  · have ha : |Complex.arg (Circle.exp t : ℂ)| ≤ Real.pi :=
      abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
    exact ha.trans (le_of_not_ge h)

theorem abs_arg_pow_le (z : Circle) (n : ℕ) :
    |Complex.arg (z ^ n : Circle)| ≤ n * |Complex.arg (z : ℂ)| := by
  have he : Circle.exp ((n : ℝ) * Complex.arg (z : ℂ)) = z ^ n := by
    rw [Circle.exp_natCast_mul, Circle.exp_arg]
  rw [← he]
  simpa [abs_mul] using abs_arg_exp_le ((n : ℝ) * Complex.arg (z : ℂ))

/-- Canonical frequencies of the dyadic restrictions. -/
def frequency (X : ℕ → Circle) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * Complex.arg (X n : ℂ)

theorem frequency_abs_mono (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1) ^ 2) :
    Monotone (fun n => |frequency X n|) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [frequency, abs_mul, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
  rw [hX n]
  calc
    2 ^ n * |Complex.arg (X (n+1) ^ 2 : Circle)| ≤
        2 ^ n * (2 * |Complex.arg (X (n+1) : ℂ)|) := by
      gcongr
      simpa using abs_arg_pow_le (X (n+1)) 2
    _ = _ := by ring

@[simp] theorem exp_frequency_div (X : ℕ → Circle) (n : ℕ) :
    Circle.exp (frequency X n / (2 : ℝ)^n) = X n := by
  rw [frequency, mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num)), Circle.exp_arg]

theorem frequency_exp_previous (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (n : ℕ) : Circle.exp (frequency X (n+1) / (2 : ℝ)^n) = X n := by
  rw [hX n, ← exp_frequency_div X (n+1), ← Circle.exp_natCast_mul]
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

theorem frequency_stabilizes (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (R : ℝ) (hR : ∀ n, |frequency X n| ≤ R) :
    ∃ N, ∀ n, N ≤ n → frequency X n = frequency X N := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((Filter.tendsto_atTop.1
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))
    (R / Real.pi + 1))
  have hp (n : ℕ) (hn : N ≤ n) : R < Real.pi * (2 : ℝ)^n := by
    have ht := hN n hn
    have hπ := Real.pi_pos
    have heq : R / Real.pi * Real.pi = R := div_mul_cancel₀ _ Real.pi_ne_zero
    nlinarith
  have hstep (n : ℕ) (hn : N ≤ n) : frequency X (n+1) = frequency X n := by
    have hb (m : ℕ) : |frequency X m / (2 : ℝ)^n| < Real.pi := by
      rw [abs_div, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
      exact (div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
        ((hR m).trans_lt (hp n hn))
    have he : frequency X (n+1) / (2 : ℝ)^n = frequency X n / (2 : ℝ)^n := by
      apply Circle.exp_injOn_Ico (a := -Real.pi) (b := Real.pi) (by linarith)
      · exact ⟨(abs_lt.mp (hb (n+1))).1.le, (abs_lt.mp (hb (n+1))).2⟩
      · exact ⟨(abs_lt.mp (hb n)).1.le, (abs_lt.mp (hb n)).2⟩
      · rw [frequency_exp_previous X hX, exp_frequency_div]
    exact (div_left_inj' (pow_ne_zero _ (by norm_num))).mp he
  refine ⟨N, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => exact (hstep n hn).trans ih

/-- The quantitative lower chord bound on the principal argument. -/
theorem chord_bound (z : Circle) :
    2 / Real.pi * |Complex.arg (z : ℂ)| ≤ ‖(z : ℂ) - 1‖ := by
  have ha : |Complex.arg (z : ℂ)| ≤ Real.pi :=
    abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hc := Real.cos_le_one_sub_mul_cos_sq ha
  have hr := Complex.norm_mul_cos_arg (z : ℂ)
  have hn := Complex.normSq_sub (z : ℂ) 1
  simp only [Circle.norm_coe, one_mul] at hr
  simp only [Complex.normSq_eq_norm_sq, Circle.norm_coe, map_one,
    mul_one, one_pow] at hn
  have hp := Real.pi_pos
  have hπ : (0 : ℝ) < Real.pi ^ 2 := sq_pos_of_pos hp
  have h0 : 0 ≤ 2 / Real.pi * |Complex.arg (z : ℂ)| := by positivity
  have hsq : (2 / Real.pi * |Complex.arg (z : ℂ)|)^2 ≤ ‖(z : ℂ)-1‖^2 := by
    rw [mul_pow, sq_abs, div_pow]
    rw [hr] at hc
    calc
      2 ^ 2 / Real.pi ^ 2 * (Complex.arg (z : ℂ))^2 =
          2 * (2 / Real.pi ^ 2 * (Complex.arg (z : ℂ))^2) := by ring
      _ ≤ 2 * (1 - (z : ℂ).re) := by linarith
      _ = _ := by linarith
  exact (sq_le_sq₀ h0 (norm_nonneg _)).mp hsq

/-- Cesàro averages of a circle point are small away from one. -/
theorem geom_sum_chord_bound (z : Circle) (m : ℕ) :
    ‖∑ k ∈ Finset.range m, (z : ℂ)^k‖ * ‖(z : ℂ)-1‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul]
  calc
    ‖(z : ℂ)^m-1‖ ≤ ‖(z : ℂ)^m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by simp only [norm_pow, Circle.norm_coe, norm_one, one_pow]; norm_num

/-- A large canonical frequency has a large averaged real deviation. -/
theorem average_deviation (z : Circle) (m : ℕ)
    (h : 4 ≤ (m : ℝ) * ‖(z : ℂ)-1‖) :
    (m : ℝ) / 2 ≤ ∑ k ∈ Finset.range m, (1 - ((z : ℂ)^k).re) := by
  have hn : 0 < ‖(z : ℂ)-1‖ := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    by_contra hh
    have hz := le_antisymm (le_of_not_gt hh) (norm_nonneg ((z : ℂ)-1))
    rw [hz, mul_zero] at h
    norm_num at h
  have hb := geom_sum_chord_bound z m
  have hr := (Complex.re_le_norm (∑ k ∈ Finset.range m, (z : ℂ)^k))
  have hs : (∑ k ∈ Finset.range m, (z : ℂ)^k).re ≤ (m : ℝ)/2 := by
    nlinarith [norm_nonneg (∑ k ∈ Finset.range m, (z : ℂ)^k)]
  simp only [Complex.re_sum] at hs
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  linarith

open MeasureTheory

def deviation (z : Circle) (k : ℕ) : ℝ := 1 - ((z : ℂ)^k).re

lemma deviation_bound (z : Circle) (k : ℕ) : 0 ≤ deviation z k ∧ deviation z k ≤ 2 := by
  have h := Complex.abs_re_le_norm ((z : ℂ)^k)
  simp only [norm_pow, Circle.norm_coe, one_pow] at h
  have hh := abs_le.mp h
  constructor <;> dsimp [deviation] <;> linarith

lemma deviation_measurable {Ω : Type*} [MeasurableSpace Ω] (X : Ω → Circle)
    (hX : Measurable (fun x => (X x : ℂ))) (k : ℕ) : Measurable (fun x => deviation (X x) k) := by
  exact measurable_const.sub (Complex.measurable_re.comp (hX.pow_const k))

lemma deviation_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → Circle) (hX : Measurable (fun x => (X x : ℂ))) (k : ℕ) :
    Integrable (fun x => deviation (X x) k) μ := by
  apply Integrable.of_bound (deviation_measurable X hX k).aestronglyMeasurable 2
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (deviation_bound (X x) k).1] using
    (deviation_bound (X x) k).2

/-- Uniform small deviations imply a quantitative frequency-tail bound. -/
theorem frequency_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → Circle) (hX : Measurable (fun x => (X x : ℂ)))
    (n m : ℕ) (hm : 0 < m) (R ε : ℝ)
    (hR : 4 ≤ (m : ℝ) * (2 / Real.pi) * (R / (2 : ℝ)^n))
    (hε : ∀ k ∈ Finset.range m, ∫ x, deviation (X x) k ∂μ ≤ ε) :
    μ.real {x | R ≤ |(2 : ℝ)^n * Complex.arg (X x : ℂ)|} ≤ 2 * ε := by
  let S : Ω → ℝ := fun x => ∑ k ∈ Finset.range m, deviation (X x) k
  have hS : Integrable S μ := by
    apply integrable_finsetSum
    intro k hk
    exact deviation_integrable μ X hX k
  have hSn : 0 ≤ᵐ[μ] S := Filter.Eventually.of_forall fun x =>
    Finset.sum_nonneg fun k hk => (deviation_bound (X x) k).1
  have hi : ∫ x, S x ∂μ ≤ (m : ℝ)*ε := by
    dsimp [S]
    rw [integral_finsetSum _ (fun k _ => deviation_integrable μ X hX k)]
    calc
      _ ≤ ∑ _k ∈ Finset.range m, ε := Finset.sum_le_sum hε
      _ = _ := by simp
  have ht : {x | R ≤ |(2 : ℝ)^n * Complex.arg (X x : ℂ)|} ⊆
      {x | (m : ℝ)/2 ≤ S x} := by
    intro x hx
    apply average_deviation (X x) m
    have hn : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
    have hf : R / (2 : ℝ)^n ≤ |Complex.arg (X x : ℂ)| := by
      apply (div_le_iff₀ hn).mpr
      simpa only [Set.mem_ofPred_eq, abs_mul, abs_of_pos hn, mul_comm] using hx
    calc
      4 ≤ (m : ℝ) * (2 / Real.pi) * (R / (2 : ℝ)^n) := hR
      _ ≤ (m : ℝ) * (2 / Real.pi) * |Complex.arg (X x : ℂ)| := by gcongr
      _ = (m : ℝ) * (2 / Real.pi * |Complex.arg (X x : ℂ)|) := by ring
      _ ≤ _ := by gcongr; exact chord_bound (X x)
  have hmark := mul_meas_ge_le_integral_of_nonneg hSn hS ((m : ℝ)/2)
  have hmono := measureReal_mono (μ := μ) ht
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  nlinarith

/-- Choosing a Cesàro window within a fixed neighborhood of zero gives
frequency tightness with a bound independent of the dyadic level. -/
theorem dyadic_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (δ ε : ℝ) (hδ : 0 < δ)
    (he : ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ →
      ∫ x, deviation (X n x) k ∂μ ≤ ε) (n : ℕ) :
    μ.real {x | 2 * Real.pi / δ ≤ |frequency (fun j => X j x) n|} ≤ 2*ε := by
  let m := Nat.ceil (δ * (2 : ℝ)^n)
  have hn : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
  have hm : 0 < m := Nat.ceil_pos.mpr (mul_pos hδ hn)
  apply frequency_tail_bound μ (X n) (hX n) n m hm
  · calc
      4 = (δ * (2 : ℝ)^n) * (2 / Real.pi) * ((2 * Real.pi / δ)/(2 : ℝ)^n) := by
        field_simp
        ring
      _ ≤ _ := by
        gcongr
        exact Nat.le_ceil _
  · intro k hk
    apply he
    apply (div_lt_iff₀ hn).mpr
    simpa only [mul_comm] using Nat.lt_ceil.mp (Finset.mem_range.mp hk)

/-- A measure with coefficients continuous at zero is almost surely supported
on dyadic paths whose principal frequencies are bounded. -/
theorem dyadic_frequencies_ae_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (hcoh : ∀ x n, X n x = X (n+1) x ^ 2)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε) :
    ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ n, |frequency (fun j => X j x) n| ≤ R := by
  rw [ae_iff]
  apply (measureReal_eq_zero_iff (μ := μ)).mp
  apply le_antisymm _ measureReal_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, he⟩ := hcont (ε/2) (by positivity)
  let R := 2 * Real.pi / δ
  let A : ℕ → Set Ω := fun n => {x | R ≤ |frequency (fun j => X j x) n|}
  have hmono : Monotone A := by
    intro n m hnm x hx
    exact hx.trans (frequency_abs_mono _ (hcoh x) hnm)
  have hA (n : ℕ) : μ (A n) ≤ ENNReal.ofReal ε := by
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hε.le).mpr
    have ht := dyadic_tail_bound μ X hX δ (ε/2) hδ he n
    dsimp [A, R]
    simpa only [measureReal_def, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using ht
  have hi : μ (⋃ n, A n) ≤ ENNReal.ofReal ε := by
    rw [hmono.measure_iUnion]
    exact iSup_le hA
  have hsub : {x | ¬ ∃ R : ℝ, ∀ n, |frequency (fun j => X j x) n| ≤ R} ⊆
      ⋃ n, A n := by
    intro x hx
    push Not at hx
    obtain ⟨n, hn⟩ := hx R
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  have hz := ENNReal.toReal_le_of_le_ofReal hε.le ((measure_mono hsub).trans hi)
  simpa only [zero_add, measureReal_def] using hz

/-- The canonical frequencies of almost every such path eventually stabilize. -/
theorem dyadic_frequencies_ae_stable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (hcoh : ∀ x n, X n x = X (n+1) x ^ 2)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε) :
    ∀ᵐ x ∂μ, ∃ N, ∀ n, N ≤ n →
      frequency (fun j => X j x) n = frequency (fun j => X j x) N := by
  filter_upwards [dyadic_frequencies_ae_bounded μ X hX hcoh hcont] with x hx
  obtain ⟨R, hR⟩ := hx
  exact frequency_stabilizes _ (hcoh x) R hR

/-- A stable coherent path is an ordinary frequency on every dyadic scale. -/
theorem ordinary_of_stable (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (N : ℕ) (hN : ∀ n, N ≤ n → frequency X n = frequency X N) :
    ∀ n, X n = Circle.exp (frequency X N / (2 : ℝ)^n) := by
  intro n
  refine Nat.decreasingInduction (n := max N n)
    (motive := fun k _ => X k = Circle.exp (frequency X N / (2 : ℝ)^k))
    ?_ ?_ (Nat.le_max_right N n)
  · intro k hk ih
    rw [hX k, ih, ← Circle.exp_natCast_mul]
    congr 1
    push_cast
    rw [pow_succ]
    field_simp
  · rw [← exp_frequency_div X (max N n), hN _ (Nat.le_max_left N n)]

abbrev F := algebraicClosure ℚ ℝ

def dyadicApprox (t : F) (n : ℕ) : F :=
  (Int.floor ((2 : ℝ)^n * (t : ℝ)) : F) / (2 : F)^n

lemma dyadicApprox_error (t : F) (n : ℕ) :
    |(dyadicApprox t n : ℝ) - (t : ℝ)| ≤ ((2 : ℝ)^n)⁻¹ := by
  have hpos : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
  have hl := Int.floor_le ((2 : ℝ)^n * (t : ℝ))
  have hr := Int.lt_floor_add_one ((2 : ℝ)^n * (t : ℝ))
  change |(Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n - (t : ℝ)| ≤ _
  calc
    _ = |(Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) - (2 : ℝ)^n * (t : ℝ)| /
        (2 : ℝ)^n := by
      have heq : (Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n - (t : ℝ) =
          ((Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) - (2 : ℝ)^n * (t : ℝ))/(2 : ℝ)^n := by
        field_simp
      rw [heq, abs_div, abs_of_pos hpos]
    _ ≤ 1 / (2 : ℝ)^n := by
      gcongr
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = _ := one_div _

lemma dyadicApprox_tendsto (t : F) :
    Filter.Tendsto (fun n => (dyadicApprox t n : ℝ)) Filter.atTop (nhds (t : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => dyadicApprox_error t n)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

/-- Exact squared distance identity for unit characters. -/
lemma circle_sq_dist (z w : Circle) :
    ‖(z : ℂ)-(w : ℂ)‖^2 = 2 * deviation (z/w) 1 := by
  have h := Complex.normSq_sub (z : ℂ) (w : ℂ)
  simp only [Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow] at h
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← div_eq_mul_inv] at h
  simp only [Circle.coe_div] at h
  dsimp [deviation]
  rw [pow_one]
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

def coeff (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle) (t : F) : ℝ :=
  ∫ x, deviation (χ x (Multiplicative.ofAdd t)) 1 ∂μ

@[simp] lemma coeff_zero (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle) :
    coeff μ χ 0 = 0 := by
  simp [coeff, deviation]

lemma coeff_small (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle)
    (hc : ContinuousAt (coeff μ χ) 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : F, |(t : ℝ)| < δ → coeff μ χ t ≤ ε := by
  obtain ⟨δ, hδ, hh⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hdist : dist t 0 < δ := by
    rw [dist_eq_norm, sub_zero]
    change ‖(t : ℝ)‖ < δ
    exact ht
  have hb := hh hdist
  rw [coeff_zero, dist_zero_right, Real.norm_eq_abs] at hb
  exact (le_abs_self _).trans hb.le

lemma char_nat_dyadic (χ : Multiplicative F →* Circle) (n k : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) ^ k =
      χ (Multiplicative.ofAdd ((k : F)/(2 : F)^n)) := by
  rw [← map_pow]
  congr 1
  change Multiplicative.ofAdd ((k : ℕ) • ((2 : F)^n)⁻¹) = _
  simp only [nsmul_eq_mul, div_eq_mul_inv]

lemma char_int_dyadic (χ : Multiplicative F →* Circle) (k : ℤ) (m : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^m)⁻¹)) ^ k =
      χ (Multiplicative.ofAdd ((k : F)/(2 : F)^m)) := by
  rw [← map_zpow]
  congr 1
  change Multiplicative.ofAdd ((k : ℤ) • ((2 : F)^m)⁻¹) = _
  simp only [zsmul_eq_mul, div_eq_mul_inv]

lemma char_dyadic_coherent (χ : Multiplicative F →* Circle) (n : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) =
      χ (Multiplicative.ofAdd (((2 : F)^(n+1))⁻¹)) ^ 2 := by
  rw [char_nat_dyadic]
  congr 2
  norm_num only [Nat.cast_ofNat]
  rw [pow_succ]
  field_simp

/-- Continuous averaged coefficients give ordinary frequencies on dyadics a.e. -/
theorem character_ae_dyadic (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, ∀ n : ℕ,
      χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n) := by
  let X : ℕ → Ω → Circle := fun n x => χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹))
  have hX : ∀ n, Measurable (fun x => (X n x : ℂ)) := fun n => hχ _
  have hcoh : ∀ x n, X n x = X (n+1) x ^ 2 := fun x n => char_dyadic_coherent _ _
  have hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hh⟩ := coeff_small μ χ hc ε hε
    refine ⟨δ, hδ, fun n k hk => ?_⟩
    have he : (∫ x, deviation (X n x) k ∂μ) = coeff μ χ ((k : F)/(2 : F)^n) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [coeff, deviation, X]
      rw [← Circle.coe_pow, char_nat_dyadic, pow_one]
    rw [he]
    apply hh
    change |(k : ℝ)/(2 : ℝ)^n| < δ
    simpa only [abs_of_nonneg
      (div_nonneg (Nat.cast_nonneg k) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))] using hk
  filter_upwards [dyadic_frequencies_ae_stable μ X hX hcoh hcont] with x hx
  obtain ⟨N, hN⟩ := hx
  exact ⟨frequency (fun n => X n x) N, ordinary_of_stable _ (hcoh x) N hN⟩

lemma char_sub (χ : Multiplicative F →* Circle) (t s : F) :
    χ (Multiplicative.ofAdd (t-s)) =
      χ (Multiplicative.ofAdd t) / χ (Multiplicative.ofAdd s) := by
  exact map_div χ (Multiplicative.ofAdd t) (Multiplicative.ofAdd s)

lemma char_sq_distance (χ : Multiplicative F →* Circle) (t s : F) :
    ‖(χ (Multiplicative.ofAdd t) : ℂ)-(χ (Multiplicative.ofAdd s) : ℂ)‖^2 =
      2 * deviation (χ (Multiplicative.ofAdd (t-s))) 1 := by
  rw [circle_sq_dist, char_sub]

lemma char_sq_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ))) (t s : F) :
    Integrable (fun x => ‖(χ x (Multiplicative.ofAdd t) : ℂ)-
      (χ x (Multiplicative.ofAdd s) : ℂ)‖^2) μ := by
  simp_rw [char_sq_distance]
  exact (deviation_integrable μ _ (hχ (t-s)) 1).const_mul 2

lemma char_sq_integral (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle) (t s : F) :
    (∫ x, ‖(χ x (Multiplicative.ofAdd t) : ℂ)-
      (χ x (Multiplicative.ofAdd s) : ℂ)‖^2 ∂μ) = 2 * coeff μ χ (t-s) := by
  simp_rw [char_sq_distance]
  exact integral_const_mul _ _

/-- At coefficient-continuity points, dyadic character evaluations converge in measure. -/
lemma character_tendstoInMeasure (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) (r : ℕ → F) (t : F)
    (hr : Filter.Tendsto r Filter.atTop (nhds t)) :
    TendstoInMeasure μ (fun n x => (χ x (Multiplicative.ofAdd (r n)) : ℂ))
      Filter.atTop (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have hpos : 0 < ε^2 := sq_pos_of_pos hε
  have hdiff : Filter.Tendsto (fun n => r n - t) Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hr.sub (tendsto_const_nhds (x := t))
  have hint : Filter.Tendsto (fun n => (∫ x, ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
      (χ x (Multiplicative.ofAdd t) : ℂ)‖^2 ∂μ)/ε^2) Filter.atTop (nhds 0) := by
    simp_rw [char_sq_integral]
    simpa only [Function.comp_def, coeff_zero, mul_zero, zero_div] using
      ((hc.tendsto.comp hdiff).const_mul 2).div_const (ε^2)
  apply squeeze_zero (fun n => measureReal_nonneg) _ hint
  intro n
  apply (le_div_iff₀ hpos).mpr
  have hh := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg
      ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-(χ x (Multiplicative.ofAdd t) : ℂ)‖)
    (char_sq_integrable μ χ hχ (r n) t) (ε^2)
  have heq : {x | ε^2 ≤ ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
    (χ x (Multiplicative.ofAdd t) : ℂ)‖^2} =
      {x | ε ≤ ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
    (χ x (Multiplicative.ofAdd t) : ℂ)‖} := by
    ext x
    exact sq_le_sq₀ hε.le (norm_nonneg _)
  rw [heq] at hh
  simpa only [mul_comm] using hh

instance F_countable : Countable F := by
  apply Set.Countable.to_subtype
  have heq : (algebraicClosure ℚ ℝ : Set ℝ) = {x | IsAlgebraic ℚ x} := by
    ext z
    exact mem_algebraicClosure_iff
  rw [heq]
  exact Algebraic.countable ℚ ℝ

lemma char_dyadicApprox_eq (χ : Multiplicative F →* Circle) (l : ℝ)
    (hl : ∀ n : ℕ, χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) =
      Circle.exp (l/(2 : ℝ)^n)) (t : F) (n : ℕ) :
    χ (Multiplicative.ofAdd (dyadicApprox t n)) = Circle.exp (l * (dyadicApprox t n : ℝ)) := by
  rw [dyadicApprox, ← char_int_dyadic, hl, ← Circle.exp_intCast_mul]
  congr 1
  change (Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) * (l/(2 : ℝ)^n) =
    l * ((Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n)
  ring

/-- Direct ordinary-character support theorem on the algebraic real line.
No Bochner representing-measure theorem is an input: frequency tightness and
an a.e. subsequence argument prove the actual simultaneous character formula. -/
theorem character_ae_ordinary (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, ∀ t : F,
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := by
  have ha (t : F) : ∀ᵐ x ∂μ, ∀ l : ℝ,
      (∀ n : ℕ, χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n)) →
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := by
    have hr : Filter.Tendsto (dyadicApprox t) Filter.atTop (nhds t) :=
      tendsto_subtype_rng.mpr (dyadicApprox_tendsto t)
    obtain ⟨ns, hns, hae⟩ :=
      (character_tendstoInMeasure μ χ hχ hc (dyadicApprox t) t hr).exists_seq_tendsto_ae
    filter_upwards [hae] with x hx
    intro l hl
    have hlim : Filter.Tendsto
        (fun n => (Circle.exp (l*(dyadicApprox t (ns n) : ℝ)) : ℂ)) Filter.atTop
        (nhds (Circle.exp (l*(t : ℝ)) : ℂ)) := by
      apply (continuous_subtype_val.comp Circle.exp.continuous).continuousAt.tendsto.comp
      exact tendsto_const_nhds.mul ((dyadicApprox_tendsto t).comp hns.tendsto_atTop)
    have heq : (fun n => (χ x (Multiplicative.ofAdd (dyadicApprox t (ns n))) : ℂ)) =
        fun n => (Circle.exp (l*(dyadicApprox t (ns n) : ℝ)) : ℂ) := by
      funext n
      rw [char_dyadicApprox_eq _ l hl]
    rw [heq] at hx
    exact Subtype.ext (tendsto_nhds_unique hx hlim)
  have hall : ∀ᵐ x ∂μ, ∀ t : F, ∀ l : ℝ,
      (∀ n : ℕ, χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n)) →
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := ae_all_iff.mpr ha
  filter_upwards [character_ae_dyadic μ χ hχ hc, hall] with x hx hxall
  obtain ⟨l, hl⟩ := hx
  exact ⟨l, fun t => hxall t l hl⟩

end PlaneFiveColor.ContinuousCharacters

namespace PlaneFiveColor.Spectral
open MeasureTheory

/-- The actual character on the algebraic parameter line, forgetting only
its discrete-domain continuity proof. -/
def lineCharacter (a : E) (d : D) : Multiplicative F →* Circle :=
  (restrictLine a d).toMonoidHom

theorem lineCharacter_measurable (a : E) (t : F) :
    Measurable (fun d : D => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ)) := by
  apply Continuous.measurable
  apply continuous_subtype_val.comp
  exact (continuous_apply (Multiplicative.ofAdd (a * ofF t))).comp
    ContinuousMonoidHom.isClosedEmbedding_coe.continuous

/-- The exact replacement of Bochner's support step for an arbitrary finite
weight absolutely continuous with respect to a wild law. -/
theorem wild_continuous_coefficient_zero (ν μ : Measure D) [IsProbabilityMeasure ν]
    [IsFiniteMeasure μ] (hν : IsWild ν) (hμ : μ ≪ ν) {a : E} (ha : a ≠ 0)
    (hc : ContinuousAt (ContinuousCharacters.coeff μ (lineCharacter a)) 0) : μ = 0 := by
  have hs := ContinuousCharacters.character_ae_ordinary μ (lineCharacter a)
    (lineCharacter_measurable a) hc
  have hL : ∀ᵐ d ∂μ, d ∈ L a := by
    filter_upwards [hs] with d hd
    obtain ⟨l, hl⟩ := hd
    apply (mem_L_iff a d).mpr
    refine ⟨l, ?_⟩
    apply PontryaginDual.ext
    intro t
    exact (hl (Multiplicative.toAdd t)).symm
  have hnull : μ (L a) = 0 := hμ (wild_line_null ν hν ha)
  have hnot : ∀ᵐ d ∂μ, d ∉ L a := (measure_eq_zero_iff_ae_notMem).mp hnull
  have hf : ∀ᵐ _d ∂μ, False := by
    filter_upwards [hL, hnot] with d hl hn
    exact hn hl
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true] using hf

end PlaneFiveColor.Spectral

end
end

end OAI
