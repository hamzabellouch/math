import OAI.NumberTheory.TwoPoint.Halasz.HalaszClassicalMeanValue

namespace OAI

/-! A fixed multiple of the degree gives the small quadratic defect
needed in the double mean-value argument. -/
namespace TwoPointCorrelations

lemma halasz_classical_ratio_block {k : ℕ} (hk : 2≤k) :
    (1-1/(k:ℝ))^k≤(1/2:ℝ) := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hq := (halasz_classical_ratio_bounds (by omega : 0<k)).1
  have hki : 0≤1/(k:ℝ) := by positivity
  have hb := one_add_mul_le_pow (show (-2:ℝ)≤1/(k:ℝ) by linarith) k
  have hb2 : (2:ℝ)≤(1+1/(k:ℝ))^k := by
    simpa only [mul_one_div_cancel hk0.ne',one_add_one_eq_two] using hb
  have hprod : (1-1/(k:ℝ))^k*(1+1/(k:ℝ))^k≤1 := by
    rw [← mul_pow]
    apply pow_le_one₀ (mul_nonneg hq (by positivity))
    nlinarith [sq_nonneg (1/(k:ℝ))]
  have hp := pow_nonneg hq k
  nlinarith

lemma halasz_classical_defect_ten_blocks {k : ℕ} (hk : 2≤k) :
    halaszClassicalDefect k (10*k)≤(k:ℝ)^2/2048 := by
  have hkpos : 0<k := by omega
  have hq := (halasz_classical_ratio_bounds hkpos).1
  have hp := pow_le_pow_left₀ (pow_nonneg hq k) (halasz_classical_ratio_block hk) 10
  norm_num at hp
  have he : (1-1/(k:ℝ))^(10*k)=((1-1/(k:ℝ))^k)^10 := by
    rw [← pow_mul]
    congr 1
    omega
  unfold halaszClassicalDefect
  rw [he]
  have htri0 : (0:ℝ)≤(halaszTriangularDegree k:ℝ) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hp htri0
  rw [halasz_triangular_degree_cast hkpos] at hm
  rw [halasz_triangular_degree_cast hkpos]
  have hk0 : (0:ℝ)≤k := Nat.cast_nonneg _
  simp only [one_div] at *
  nlinarith

/-- The selected moment has a defect at most `k^2/2048`, uniformly in
its endpoint. Its explicit constant is bounded separately. -/
theorem halasz_classical_selected_moment : ∃ R₀ : ℕ, ∀ k : ℕ, 2≤k →
    ∀ N : ℕ, 1≤N →
    (halaszVinogradovCount ((10*k+1)*k) k N:ℝ) ≤
      (halaszIterationConstant R₀ k (10*k):ℝ)*
        (N:ℝ)^(2*(((10*k+1)*k:ℕ):ℝ)-(halaszTotalDegree k:ℝ)+(k:ℝ)^2/2048) := by
  obtain ⟨R₀,hmean⟩ := halasz_classical_mean_value
  refine ⟨R₀,?_⟩
  intro k hk N hN
  apply (hmean k hk (10*k) N hN).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  unfold halaszClassicalExponent
  linarith [halasz_classical_defect_ten_blocks hk]

end TwoPointCorrelations

end OAI
