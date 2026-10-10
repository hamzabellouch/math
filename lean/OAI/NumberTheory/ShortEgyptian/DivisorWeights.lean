import OAI.NumberTheory.ShortEgyptian.PrimeReciprocals

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def momentSeriesConst (r : ℕ) : ℝ :=
  ∑' j : ℕ, ((j + 2 : ℕ) : ℝ) ^ r * (3 / 4 : ℝ) ^ j

theorem summable_shifted_geom (r k : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun j : ℕ => ((j + k : ℕ) : ℝ)^r * x^j) := by
  have hb : Summable (fun j : ℕ => (j : ℝ)^r * x^j) :=
    summable_pow_mul_geometric_of_norm_lt_one r (by simpa [Real.norm_eq_abs, abs_of_pos hx0] using hx1)
  have hs := (summable_nat_add_iff k).mpr hb
  have hs' := hs.mul_right (x ^ k)⁻¹
  apply hs'.congr
  intro j
  rw [pow_add]
  field_simp

theorem polynomial_geom_local (r : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 3/4) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ)^r * x^j) ∧
    (∑' j : ℕ, ((j + 1 : ℕ) : ℝ)^r * x^j) ≤ Real.exp (momentSeriesConst r * x) := by
  have hs (k : ℕ) := summable_shifted_geom r k (3/4) (by norm_num) (by norm_num)
  have hsum (k : ℕ) : Summable (fun j : ℕ => ((j+k:ℕ):ℝ)^r * x^j) := by
    apply Summable.of_nonneg_of_le (fun j => by positivity) _ (hs k)
    intro j
    gcongr
  refine ⟨hsum 1, ?_⟩
  have htail : (∑' j : ℕ, ((j+2:ℕ):ℝ)^r * x^j) ≤ momentSeriesConst r := by
    exact (hsum 2).tsum_le_tsum (fun j => by gcongr) (hs 2)
  rw [(hsum 1).tsum_eq_zero_add]
  simp only [Nat.zero_add, Nat.cast_one, one_pow, pow_zero, mul_one]
  have heq : (∑' b : ℕ, ((b + 1 + 1 : ℕ) : ℝ)^r * x^(b+1)) =
      x * ∑' b : ℕ, ((b+2:ℕ):ℝ)^r * x^b := by
    rw [← tsum_mul_left]
    congr 1
    ext b
    simp only [pow_succ]
    ring
  rw [heq]
  calc
    _ ≤ 1 + momentSeriesConst r * x := by nlinarith
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (momentSeriesConst r * x)

noncomputable def divisorWeight (r : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ)^r * (n : ℝ)^(-σ)

theorem divisorWeight_one (r : ℕ) (σ : ℝ) : divisorWeight r σ 1 = 1 := by
  simp [divisorWeight]

theorem divisorWeight_mul (r : ℕ) (σ : ℝ) {m n : ℕ} (h : m.Coprime n) :
    divisorWeight r σ (m*n) = divisorWeight r σ m * divisorWeight r σ n := by
  simp only [divisorWeight, h.card_divisors_mul, Nat.cast_mul, mul_pow,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem divisorWeight_prime_pow (r : ℕ) (σ : ℝ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    divisorWeight r σ (p^j) = ((j+1:ℕ):ℝ)^r * ((p:ℝ)^(-σ))^j := by
  have hcard : (p^j).divisors.card = j+1 := by
    rw [← ArithmeticFunction.sigma_zero_apply]
    exact ArithmeticFunction.sigma_zero_apply_prime_pow hp
  simp only [divisorWeight, hcard, Nat.cast_pow]
  congr 1
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _), mul_comm,
    Real.rpow_mul_natCast (Nat.cast_nonneg _)]

theorem prime_rpow_small {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1/2 ≤ σ) :
    0 < (p:ℝ)^(-σ) ∧ (p:ℝ)^(-σ) ≤ 3/4 := by
  have hpp : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hp2 : 2 ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hs : 4/3 ≤ Real.sqrt (p:ℝ) := by
    apply (Real.le_sqrt (by norm_num) hpp.le).mpr
    norm_num
    linarith
  refine ⟨Real.rpow_pos_of_pos hpp _, ?_⟩
  calc
    _ ≤ (p:ℝ)^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (Real.sqrt (p:ℝ))⁻¹ := by rw [Real.rpow_neg hpp.le, Real.sqrt_eq_rpow]
    _ ≤ 3/4 := by
      rw [← one_div]
      apply (div_le_iff₀ (Real.sqrt_pos.mpr hpp)).mpr
      linarith

theorem divisorWeight_prime_summable (r : ℕ) {σ : ℝ} (hσ : 1/2 ≤ σ)
    {p : ℕ} (hp : p.Prime) : Summable (fun j : ℕ => ‖divisorWeight r σ (p^j)‖) := by
  simp_rw [divisorWeight_prime_pow r σ hp]
  have hx := prime_rpow_small hp hσ
  have hnonneg (j : ℕ) : 0 ≤ ((j+1:ℕ):ℝ)^r * ((p:ℝ)^(-σ))^j := by positivity
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
  exact (polynomial_geom_local r _ hx.1.le hx.2).1

theorem smooth_divisor_weight (r : ℕ) {σ : ℝ} (hσ : 1/2 ≤ σ)
    (s P : Finset ℕ) (hs : ∀ d ∈ s, d ∈ Nat.factoredNumbers P) :
    ∑ d ∈ s, divisorWeight r σ d ≤
      Real.exp (momentSeriesConst r * ∑ p ∈ P with p.Prime, (p:ℝ)^(-σ)) := by
  classical
  have he := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (divisorWeight_one r σ) (fun h => divisorWeight_mul r σ h)
    (fun hp => divisorWeight_prime_summable r hσ hp) P
  have hnn (d : ℕ) : 0 ≤ divisorWeight r σ d := by
    unfold divisorWeight
    positivity
  calc
    _ = ∑ d ∈ s.subtype (· ∈ Nat.factoredNumbers P), divisorWeight r σ d :=
      (sum_subtype_of_mem _ hs).symm
    _ ≤ ∏ p ∈ P with p.Prime, ∑' j : ℕ, divisorWeight r σ (p^j) :=
      sum_le_hasSum _ (fun d _ => hnn d) he.2
    _ ≤ ∏ p ∈ P with p.Prime, Real.exp (momentSeriesConst r * (p:ℝ)^(-σ)) := by
      apply prod_le_prod₀
      · intro p _
        exact tsum_nonneg (fun j => hnn (p^j))
      · intro p hp
        have hp' := (mem_filter.mp hp).2
        simp_rw [divisorWeight_prime_pow r σ hp']
        exact (polynomial_geom_local r _ (prime_rpow_small hp' hσ).1.le
          (prime_rpow_small hp' hσ).2).2
    _ = _ := by rw [← Real.exp_sum, ← mul_sum]

theorem momentSeriesConst_nonneg (r : ℕ) : 0 ≤ momentSeriesConst r := by
  exact tsum_nonneg (fun _ => by positivity)

theorem rankin_divisor_weight (r : ℕ) (A lam : ℝ) (hA : 0 < A)
    (hlam : 0 ≤ lam) (hlamsmall : lam ≤ 1/2) (s P : Finset ℕ)
    (hs : ∀ d ∈ s, d ∈ Nat.factoredNumbers P ∧ A ≤ d) :
    ∑ d ∈ s, (d.divisors.card : ℝ)^r / d ≤
      Real.exp (-lam * Real.log A + momentSeriesConst r *
        ∑ p ∈ P with p.Prime, (p:ℝ)^(-(1-lam))) := by
  have hnonneg : 0 ≤ A ^ (-lam) := Real.rpow_nonneg hA.le _
  have hsum := smooth_divisor_weight r (by linarith : 1/2 ≤ 1-lam) s P (fun d hd => (hs d hd).1)
  calc
    _ ≤ ∑ d ∈ s, A^(-lam) * divisorWeight r (1-lam) d := by
      apply sum_le_sum
      intro d hd
      have hdpos : 0 < (d:ℝ) := lt_of_lt_of_le hA (hs d hd).2
      have hp : (d:ℝ)^(-lam) ≤ A^(-lam) :=
        Real.rpow_le_rpow_of_nonpos hA (hs d hd).2 (by linarith)
      have heq : (d.divisors.card : ℝ)^r / d =
          (d:ℝ)^(-lam) * divisorWeight r (1-lam) d := by
        unfold divisorWeight
        rw [mul_left_comm, ← Real.rpow_add hdpos]
        have hh : -lam + -(1-lam) = (-1:ℝ) := by ring
        rw [hh, Real.rpow_neg_one]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hp (by unfold divisorWeight; positivity)
    _ = A^(-lam) * ∑ d ∈ s, divisorWeight r (1-lam) d := (mul_sum _ _ _).symm
    _ ≤ A^(-lam) * Real.exp (momentSeriesConst r *
        ∑ p ∈ P with p.Prime, (p:ℝ)^(-(1-lam))) := mul_le_mul_of_nonneg_left hsum hnonneg
    _ = _ := by rw [Real.rpow_def_of_pos hA, ← Real.exp_add]; congr 1; ring

end ShortEgyptian

end OAI
