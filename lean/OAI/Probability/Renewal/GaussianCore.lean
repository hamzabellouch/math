import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace HoneycombLocal

lemma norm_iteratedDeriv_charFun_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    {n : ℕ} (h : MemLp id n μ) (t : ℝ) :
    ‖iteratedDeriv n (charFun μ) t‖ ≤ ∫ x, ‖x‖ ^ n ∂μ := by
  rw [iteratedDeriv_charFun h, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1
  ext x
  simp only [norm_mul, norm_pow, Complex.norm_real]
  rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

lemma taylorWithinEval_eq_univ {f : ℝ → ℂ} {t : ℝ} (ht : 0 < t)
    (hf : ContDiff ℝ 3 f) :
    taylorWithinEval f 2 (Icc 0 t) 0 t = taylorWithinEval f 2 univ 0 t := by
  simp only [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hk3 : k ≤ 3 := by have := Finset.mem_range.mp hk; omega
  have hd : ContDiffAt ℝ k f 0 := hf.contDiffAt.of_le (by exact_mod_cast hk3)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht) hd ⟨le_rfl, ht.le⟩,
    iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_univ hd (mem_univ 0)]

lemma taylor_charFun_bound_nonneg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h3 : MemLp id 3 μ) (hmean : ∫ x, x ∂μ = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖charFun μ t - (1 - ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)‖ ≤
      (∫ x, ‖x‖ ^ 3 ∂μ) * t ^ 3 / 2 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hc : ContDiff ℝ 3 (charFun μ) := contDiff_charFun h3
  have h2 : MemLp id 2 μ := h3.mono_exponent (by norm_num)
  have h := taylor_mean_remainder_bound (n := 2) (a := 0) (b := t)
    (C := ∫ x, ‖x‖ ^ 3 ∂μ) ht.le hc.contDiffOn ⟨ht.le, le_rfl⟩ (by
      intro y hy
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht) hc.contDiffAt hy]
      exact norm_iteratedDeriv_charFun_le h3 y)
  rw [taylorWithinEval_eq_univ ht hc] at h
  have htaylor := taylorWithinEval_charFun_two_zero (P := μ) (X := id)
    aemeasurable_id (by simpa using h2) t
  simp only [Measure.map_id, id_eq, Pi.pow_apply, hmean, Complex.ofReal_zero,
    zero_mul, add_zero] at htaylor
  rw [htaylor] at h
  simpa using h

lemma taylor_charFun_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h3 : MemLp id 3 μ) (hmean : ∫ x, x ∂μ = 0) (t : ℝ) :
    ‖charFun μ t - (1 - ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)‖ ≤
      (∫ x, ‖x‖ ^ 3 ∂μ) * |t| ^ 3 / 2 := by
  by_cases ht : 0 ≤ t
  · simpa [abs_of_nonneg ht] using taylor_charFun_bound_nonneg h3 hmean ht
  · have ht' : 0 ≤ -t := by linarith
    have h := taylor_charFun_bound_nonneg h3 hmean ht'
    have heq : charFun μ (-t) -
        (1 - ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) * ((-t : ℝ) : ℂ) ^ 2 / 2) =
        star (charFun μ t - (1 - ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) := by
      simp [charFun_neg]
    rw [heq, norm_star] at h
    simpa [abs_of_neg (lt_of_not_ge ht)] using h

lemma norm_pow_difference {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (k : ℕ) :
    ‖z ^ k - w ^ k‖ ≤ k * ‖z - w‖ := by
  induction k with
  | zero => simp
  | succ k hk =>
    calc
      ‖z ^ (k + 1) - w ^ (k + 1)‖ =
          ‖z * (z ^ k - w ^ k) + (z - w) * w ^ k‖ := by congr 1; ring
      _ ≤ ‖z * (z ^ k - w ^ k)‖ + ‖(z - w) * w ^ k‖ := norm_add_le _ _
      _ = ‖z‖ * ‖z ^ k - w ^ k‖ + ‖z - w‖ * ‖w‖ ^ k := by simp [norm_pow]
      _ ≤ 1 * (k * ‖z - w‖) + ‖z - w‖ * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) hw
      _ = (k + 1 : ℕ) * ‖z - w‖ := by push_cast; ring

lemma exp_neg_error_le {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖Complex.exp (-(y : ℂ)) - (1 - (y : ℂ))‖ ≤ y ^ 2 := by
  have h := Complex.norm_exp_sub_one_sub_id_le
    (x := -(y : ℂ)) (by simpa [abs_of_nonneg hy] using hy1)
  convert h using 1
  · congr 1; ring
  · simp [abs_of_nonneg hy]

lemma gaussian_power_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h3 : MemLp id 3 μ) (hmean : ∫ x, x ∂μ = 0) (k : ℕ) (t : ℝ)
    (hsmall : (∫ x, x ^ 2 ∂μ) * t ^ 2 / 2 ≤ 1) :
    ‖charFun μ t ^ k - Complex.exp (-((k : ℂ) *
      ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))‖ ≤
      k * ((∫ x, ‖x‖ ^ 3 ∂μ) * |t| ^ 3 / 2 +
        ((∫ x, x ^ 2 ∂μ) * t ^ 2 / 2) ^ 2) := by
  let v : ℝ := ∫ x, x ^ 2 ∂μ
  let y : ℝ := v * t ^ 2 / 2
  have hv : 0 ≤ v := integral_nonneg (fun x => sq_nonneg x)
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hnorm : ‖Complex.exp (-(y : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)
  have hdiff : ‖charFun μ t - Complex.exp (-(y : ℂ))‖ ≤
      (∫ x, ‖x‖ ^ 3 ∂μ) * |t| ^ 3 / 2 + y ^ 2 := by
    refine (norm_sub_le_norm_sub_add_norm_sub (charFun μ t) (1 - (y : ℂ))
      (Complex.exp (-(y : ℂ)))).trans ?_
    apply add_le_add
    · simpa [y, v] using taylor_charFun_bound h3 hmean t
    · rw [norm_sub_rev]
      exact exp_neg_error_le hy hsmall
  have hpow := (norm_pow_difference (norm_charFun_le_one t) hnorm k).trans
    (mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg k))
  have heq : Complex.exp (-(y : ℂ)) ^ k =
      Complex.exp (-((k : ℂ) * (v : ℂ) * (t : ℂ) ^ 2 / 2)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [y, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_ofNat]
    ring
  rw [heq] at hpow
  exact hpow

lemma normalized_gaussian_power_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h3 : MemLp id 3 μ) (hmean : ∫ x, x ∂μ = 0) {k : ℕ} (hk : 0 < k)
    {σ : ℝ} (hσ : 0 < σ) (hvariance : σ ^ 2 = k * ∫ x, x ^ 2 ∂μ)
    (t : ℝ) (hsmall : t ^ 2 ≤ 2 * k) :
    ‖charFun μ (t / σ) ^ k - Complex.exp (-((t : ℂ) ^ 2 / 2))‖ ≤
      ((k : ℝ) * (∫ x, ‖x‖ ^ 3 ∂μ) / σ ^ 3) * |t| ^ 3 / 2 +
      t ^ 4 / (4 * k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have heq : (∫ x, x ^ 2 ∂μ) * (t / σ) ^ 2 / 2 = t ^ 2 / (2 * k) := by
    field_simp
    nlinarith [hvariance]
  have h := gaussian_power_error h3 hmean k (t / σ) (by
    rw [heq]; exact (div_le_one (by positivity)).2 hsmall)
  have hexp : -((k : ℂ) * ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) *
      ((t / σ : ℝ) : ℂ) ^ 2 / 2) = -((t : ℂ) ^ 2 / 2) := by
    have hvr : (∫ x, x ^ 2 ∂μ) = σ ^ 2 / k := by
      exact (eq_div_iff (ne_of_gt hk')).2 (by simpa [mul_comm] using hvariance.symm)
    rw [hvr]
    push_cast
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    field_simp
  rw [hexp, heq] at h
  convert h using 1
  rw [abs_div, abs_of_pos hσ]
  field_simp
  ring

end HoneycombLocal

end

end OAI
