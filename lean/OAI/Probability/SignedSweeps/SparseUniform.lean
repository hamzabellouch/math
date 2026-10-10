import OAI.Probability.SignedSweeps.SparseBridge

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Topology
open Filter

lemma sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

lemma sparse_kernel_exponential_bound {t Δ : ℝ} (hΔ : Δ ≤ Real.exp (-t)) (k : ℕ) :
    (2 : ℝ) ^ k * Real.sqrt ((Real.sqrt Δ) ^ k * Real.exp (Real.exp 2 * k)) ≤
      Real.exp (((Real.log 2 + Real.exp 2 / 2) - t / 4) * k) := by
  have hroot : Real.sqrt Δ ≤ Real.exp (-t / 2) := by
    simpa only [sqrt_exp_half] using Real.sqrt_le_sqrt hΔ
  calc
    _ ≤ (2 : ℝ) ^ k * Real.sqrt ((Real.exp (-t / 2)) ^ k * Real.exp (Real.exp 2 * k)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg Δ) hroot k) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, sqrt_exp_half]
      nth_rw 1 [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

lemma sparse_depth_prefactors {δ : ℝ} (hδ : 0 < δ) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d ≥ d₀,
      2 * (d : ℝ) * Real.exp (-δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ)) ≤ 1 ∧
      Real.log 2 + Real.exp 2 / 2 ≤ δ / 16 * Real.log ((2 ^ d : ℕ) : ℝ) := by
  have hb : 0 < δ / 2 * Real.log 2 := mul_pos (half_pos hδ) (Real.log_pos (by norm_num))
  have ht := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1
    (δ / 2 * Real.log 2) hb).comp tendsto_natCast_atTop_atTop).const_mul 2
  have ht' : Tendsto (fun d : ℕ =>
      2 * (d : ℝ) * Real.exp (-δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ))) atTop (𝓝 0) := by
    convert ht using 1
    · funext d
      simp only [Function.comp_apply, Real.rpow_one, nat_two_pow_log]
      rw [mul_assoc]
      congr 2
      ring_nf
    · norm_num
  have ht'' : Tendsto (fun d : ℕ => δ / 16 * Real.log ((2 ^ d : ℕ) : ℝ)) atTop atTop := by
    have hh := tendsto_natCast_atTop_atTop.const_mul_atTop
      (by positivity : 0 < δ / 16 * Real.log 2)
    convert hh using 1
    funext d
    rw [nat_two_pow_log]
    ring
  obtain ⟨D, hD⟩ := eventually_atTop.mp
    ((ht'.eventually_le_const (by norm_num : (0 : ℝ) < 1)).and
      (ht''.eventually_ge_atTop (Real.log 2 + Real.exp 2 / 2)))
  exact ⟨max D 1, le_max_right _ _, fun d hd => hD d ((le_max_left _ _).trans hd)⟩

lemma sparse_delta_le_exp {δ : ℝ} {d k : ℕ}
    (hk : (k : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ))
    (hsmall : 2 * (d : ℝ) * Real.exp (-δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ)) ≤ 1) :
    2 * (d : ℝ) * k / (2 ^ d : ℕ) ≤
      Real.exp (-δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < (2 ^ d : ℕ) := by positivity
  let c := Real.exp (-δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ))
  have he : (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) = c * c * (2 ^ d : ℕ) := by
    conv_rhs => rhs; rw [← Real.exp_log hn]
    dsimp [c]
    rw [← Real.exp_add, ← Real.exp_add, Real.rpow_def_of_pos hn]
    congr 1
    ring
  calc
    _ ≤ 2 * (d : ℝ) * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) / (2 ^ d : ℕ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by positivity)) hn.le
    _ = (2 * (d : ℝ) * c) * c := by rw [he]; field_simp
    _ ≤ 1 * c := mul_le_mul_of_nonneg_right hsmall (Real.exp_nonneg _)
    _ = _ := one_mul c

theorem eventually_sparse_sweep_norm {δ : ℝ} (hδ : 0 < δ) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ lam : Partition (2 ^ d),
      1 ≤ 2 ^ d - lam.1.rowLen 0 →
      ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) →
      ‖(sweepOperator lam).toContinuousLinearMap‖ ≤
        Real.exp (-(δ / 16) * (2 ^ d - lam.1.rowLen 0 : ℕ) *
          Real.log ((2 ^ d : ℕ) : ℝ)) := by
  obtain ⟨d₀, hd₀, hsmall⟩ := sparse_depth_prefactors hδ
  refine ⟨d₀, hd₀, ?_⟩
  intro d hd lam hk hkbound
  obtain ⟨hpref, hlog⟩ := hsmall d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d from hd₀.trans hd)
  have hkpos : (0 : ℝ) < (2 ^ d - lam.1.rowLen 0 : ℕ) := by exact_mod_cast hk
  have hΔ := sparse_delta_le_exp hkbound hpref
  have hnlog : 0 ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by rw [nat_two_pow_log]; positivity
  have hΔ1 : 2 * (d : ℝ) * (2 ^ d - lam.1.rowLen 0 : ℕ) / (2 ^ d : ℕ) ≤ 1 := by
    apply hΔ.trans
    apply Real.exp_le_one_iff.mpr
    nlinarith
  apply (sparse_sweep_operator_bound lam (by positivity) hΔ1).trans
  have hb := sparse_kernel_exponential_bound (t := δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ))
    (by simpa only [neg_mul, neg_div] using hΔ) (2 ^ d - lam.1.rowLen 0)
  refine hb.trans (Real.exp_le_exp.mpr ?_)
  have hh := mul_le_mul_of_nonneg_right hlog hkpos.le
  nlinarith

theorem eventually_sparse_moments {δ : ℝ} (hδ : 0 < δ) :
    ∃ d₀ r₀ : ℕ, 1 ≤ d₀ ∧ 1 ≤ r₀ ∧ ∀ d ≥ d₀, ∀ r ≥ r₀,
      ∀ lam : Partition (2 ^ d),
      ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) →
      weightedMoment lam r ≤ 1 := by
  obtain ⟨d₀, hd₀, hnorm⟩ := eventually_sparse_sweep_norm hδ
  obtain ⟨R, hR⟩ := exists_nat_ge (16 / δ)
  refine ⟨d₀, max R 1, hd₀, le_max_right _ _, ?_⟩
  intro d hd r hr lam hk
  let k := 2 ^ d - lam.1.rowLen 0
  have hdim : (spechtDimension lam : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ k := by
    exact_mod_cast spechtDimension_le_pow_level lam
  have hn : (0 : ℝ) < (2 ^ d : ℕ) := by positivity
  have hnlog : 0 ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by rw [nat_two_pow_log]; positivity
  by_cases hk0 : k = 0
  · have hdim1 : (spechtDimension lam : ℝ) ≤ 1 := by simpa [hk0] using hdim
    exact (weightedMoment_le_dimension_squared lam r).trans (by
      simpa using pow_le_pow_left₀ (Nat.cast_nonneg (spechtDimension lam)) hdim1 2)
  have hs := hnorm d hd lam (by omega) hk
  calc
    weightedMoment lam r ≤ (spechtDimension lam : ℝ) ^ 2 *
        ‖(sweepOperator lam).toContinuousLinearMap‖ ^ (2 * r) := weightedMoment_le_opNorm lam r
    _ ≤ (((2 ^ d : ℕ) : ℝ) ^ k) ^ 2 *
        (Real.exp (-(δ / 16) * k * Real.log ((2 ^ d : ℕ) : ℝ))) ^ (2 * r) := by
      exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hdim 2)
        (pow_le_pow_left₀ (norm_nonneg _) hs (2 * r)) (by positivity) (by positivity)
    _ = Real.exp (((2 : ℝ) - δ / 8 * r) * k * Real.log ((2 ^ d : ℕ) : ℝ)) := by
      nth_rw 1 [← Real.exp_log hn]
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hRr : (R : ℝ) ≤ r := by exact_mod_cast (le_max_left R 1).trans hr
      have : 16 ≤ δ * r := by
        have hh := (div_le_iff₀ hδ).mp (hR.trans hRr)
        nlinarith
      have hh : 2 - δ / 8 * r ≤ 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hh (Nat.cast_nonneg k)) hnlog

theorem uniform_sparse_moments {δ : ℝ} (hδ : 0 < δ) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r ≥ r₀, ∀ d : ℕ, ∀ lam : Partition (2 ^ d),
      ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) →
      weightedMoment lam r ≤ 1 := by
  obtain ⟨d₀, r₀, _hd₀, hr₀, hlarge⟩ := eventually_sparse_moments hδ
  obtain ⟨R, _hR, hfinite⟩ := finite_base_moments d₀
  refine ⟨max r₀ R, hr₀.trans (le_max_left _ _), ?_⟩
  intro r hr d lam hk
  by_cases hd : d₀ ≤ d
  · exact hlarge d hd r ((le_max_left _ _).trans hr) lam hk
  · exact hfinite r ((le_max_right _ _).trans hr) d (by omega) lam

end SignedSweeps
end

end OAI
