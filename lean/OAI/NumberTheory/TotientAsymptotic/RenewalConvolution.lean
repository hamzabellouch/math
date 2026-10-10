import OAI.NumberTheory.TotientAsymptotic.Normalization

namespace OAI

/-!
The dominated convolution limit needed for the finite-tail volume asymptotic.
The sole published input here is Ford's bounded renewal error, Lemma 3.7 of
*The distribution of totients*, arXiv:1104.3264v2 (2013), with Ford's constant
lambda denoted by gamma in this development.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def FordRenewalInput : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |g n-gamma*(rho^n)⁻¹| ≤ C

def normalizedRenewal (n : ℕ) : ℝ := g n*rho^n

lemma normalizedRenewal_properties (hford : FordRenewalInput) :
    Tendsto normalizedRenewal atTop (nhds gamma) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ‖normalizedRenewal n‖ ≤ K := by
  obtain ⟨C, hC, herr⟩ := hford
  have hb (n : ℕ) : |normalizedRenewal n-gamma| ≤ C*rho^n := by
    have he : normalizedRenewal n-gamma = (g n-gamma*(rho^n)⁻¹)*rho^n := by
      unfold normalizedRenewal
      field_simp [rho_pos.ne']
    rw [he, abs_mul, abs_of_pos (pow_pos rho_pos _)]
    exact mul_le_mul_of_nonneg_right (herr n) (pow_nonneg rho_pos.le _)
  constructor
  · apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (g := fun n => C*rho^n) (fun n => dist_nonneg) ?_ ?_
    · intro n
      simpa only [Real.dist_eq] using hb n
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).const_mul C
  · refine ⟨gamma+C, add_nonneg gamma_pos.le hC, fun n => ?_⟩
    have hg : 0 ≤ normalizedRenewal n := mul_nonneg (g_pos n).le (pow_nonneg rho_pos.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg hg]
    have hpow : rho^n ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
    have h := (abs_le.mp (hb n)).2
    nlinarith

def renewalConvolution (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), normalizedRenewal (n-i)*c i

lemma renewalConvolution_eq_tsum (c : ℕ → ℝ) (n : ℕ) :
    renewalConvolution c n = ∑' i : ℕ,
      if i ≤ n then normalizedRenewal (n-i)*c i else 0 := by
  symm
  rw [tsum_eq_sum (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left (by have := Finset.mem_range.mp hi; omega)]
  · intro i hi
    rw [ite_eq_right (by have := mt Finset.mem_range.mpr hi; omega)]

/-- Summable arithmetic tail weights can be passed through the normalized
renewal convolution without requiring any continuity in the phase. -/
theorem renewalConvolution_tendsto (hford : FordRenewalInput)
    (c : ℕ → ℝ) (hc : Summable c) :
    Tendsto (renewalConvolution c) atTop (nhds (gamma * ∑' i, c i)) := by
  obtain ⟨hlim, K, hK, hbound⟩ := normalizedRenewal_properties hford
  let F : ℕ → ℕ → ℝ := fun n i =>
    if i ≤ n then normalizedRenewal (n-i)*c i else 0
  have hpoint (i : ℕ) : Tendsto (fun n => F n i) atTop (nhds (gamma*c i)) := by
    apply ((hlim.comp (tendsto_sub_atTop_nat i)).mul_const (c i)).congr'
    filter_upwards [eventually_ge_atTop i] with n hn
    simp [F, hn]
  have hdom : ∀ᶠ n : ℕ in atTop, ∀ i, ‖F n i‖ ≤ K*‖c i‖ := by
    apply Eventually.of_forall
    intro n i
    dsimp [F]
    split_ifs with hi
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using hbound (n-i)) (abs_nonneg _)
    · simpa using mul_nonneg hK (norm_nonneg (c i))
  have ht := tendsto_tsum_of_dominated_convergence (hc.norm.mul_left K) hpoint hdom
  simp only [tsum_mul_left] at ht
  exact ht.congr' (Eventually.of_forall (fun n => (renewalConvolution_eq_tsum c n).symm))

end TotientAsymptotic

end

end OAI
