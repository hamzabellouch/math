import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBilinearExpansion

namespace OAI

/-! # Cauchy bounds for two independently truncated coprime arrays -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadratic_divisibility_partial_energy (D N : ℕ) (b : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 D, quadraticSieveEnergy N (fun n => if d ∣ n then b n else 0)) ≤
      ∑ n ∈ oddSquarefreeRange N, (n.divisors.card : ℝ) * ‖b n‖ ^ 2 := by
  unfold quadraticSieveEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 := (Finset.mem_filter.mp hn).2.2.ne_zero
  have hsub : (Finset.Icc 1 D).filter (fun d => d ∣ n) ⊆ n.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hn0⟩
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (sq_nonneg _)

 theorem quadratic_coprime_bilinear_pointwise (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (m : ℤ) :
    ‖quadraticCoprimeBilinear N₁ N₂ a b m‖ ≤
      ∑ d ∈ Finset.Icc 1 N₂,
        ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ *
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ := by
  rw [quadratic_coprime_bilinear_expansion]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  have hd : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  simp only [norm_mul, Complex.norm_conj]
  calc
    _ ≤ 1 * ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ *
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ := by
      gcongr
    _ = _ := by ring

 theorem quadratic_coprime_bilinear_cauchy (M N₁ N₂ : ℕ) (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂ a b m‖) ≤
      Real.sqrt (∑ d ∈ Finset.Icc 1 N₂, ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ ^ 2) *
      Real.sqrt (∑ d ∈ Finset.Icc 1 N₂, ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ ^ 2) := by
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M, ∑ d ∈ Finset.Icc 1 N₂,
        ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ *
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ :=
      Finset.sum_le_sum (fun m _ => quadratic_coprime_bilinear_pointwise N₁ N₂ a b m)
    _ = ∑ z ∈ (Finset.Icc 1 N₂).product (oddSquarefreeRange M),
        ‖quadraticTransposeSum N₁ (fun n => if z.1 ∣ n then a n else 0) z.2‖ *
        ‖quadraticTransposeSum N₂ (fun n => if z.1 ∣ n then b n else 0) z.2‖ := by
      rw [Finset.sum_comm, Finset.product_eq_sprod, Finset.sum_product]
    _ ≤ _ := by
      have hc := Real.sum_mul_le_sqrt_mul_sqrt
        ((Finset.Icc 1 N₂).product (oddSquarefreeRange M))
        (fun z => ‖quadraticTransposeSum N₁ (fun n => if z.1 ∣ n then a n else 0) z.2‖)
        (fun z => ‖quadraticTransposeSum N₂ (fun n => if z.1 ∣ n then b n else 0) z.2‖)
      simpa only [Finset.product_eq_sprod, Finset.sum_product] using hc

 theorem quadratic_coprime_two_array_bound {M N₁ N₂ : ℕ} {K₁ K₂ : ℝ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M N₁ K₁) (h₂ : QuadraticSieveBound M N₂ K₂)
    (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂ a b m‖) ≤
      Real.sqrt (2 * K₁ * ∑ n ∈ oddSquarefreeRange N₁, (n.divisors.card : ℝ) * ‖a n‖ ^ 2) *
      Real.sqrt (2 * K₂ * ∑ n ∈ oddSquarefreeRange N₂, (n.divisors.card : ℝ) * ‖b n‖ ^ 2) := by
  let S := (Finset.Icc 1 N₂).product (oddSquarefreeRange M)
  let f : ℕ × ℕ → ℝ := fun z =>
    ‖quadraticTransposeSum N₁ (fun n => if z.1 ∣ n then a n else 0) z.2‖
  let g : ℕ × ℕ → ℝ := fun z =>
    ‖quadraticTransposeSum N₂ (fun n => if z.1 ∣ n then b n else 0) z.2‖
  have hA : (∑ z ∈ S, f z ^ 2) ≤
      2 * K₁ * ∑ n ∈ oddSquarefreeRange N₁, (n.divisors.card : ℝ) * ‖a n‖ ^ 2 := by
    change (∑ z ∈ (Finset.Icc 1 N₂).product (oddSquarefreeRange M), f z ^ 2) ≤ _
    rw [Finset.product_eq_sprod, Finset.sum_product]
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 N₂,
          2 * K₁ * quadraticSieveEnergy N₁ (fun n => if d ∣ n then a n else 0) :=
        Finset.sum_le_sum (fun d _ => quadraticTranspose_of_bound h₁ _)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (quadratic_divisibility_partial_energy N₂ N₁ a)
          (by positivity)
  have hB : (∑ z ∈ S, g z ^ 2) ≤
      2 * K₂ * ∑ n ∈ oddSquarefreeRange N₂, (n.divisors.card : ℝ) * ‖b n‖ ^ 2 := by
    change (∑ z ∈ (Finset.Icc 1 N₂).product (oddSquarefreeRange M), g z ^ 2) ≤ _
    rw [Finset.product_eq_sprod, Finset.sum_product]
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 N₂,
          2 * K₂ * quadraticSieveEnergy N₂ (fun n => if d ∣ n then b n else 0) :=
        Finset.sum_le_sum (fun d _ => quadraticTranspose_of_bound h₂ _)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (quadratic_divisibility_partial_energy N₂ N₂ b)
          (by positivity)
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M, ∑ d ∈ Finset.Icc 1 N₂,
        ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ *
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ :=
      Finset.sum_le_sum (fun m _ => quadratic_coprime_bilinear_pointwise N₁ N₂ a b m)
    _ = ∑ z ∈ S, f z * g z := by
      change _ = ∑ z ∈ (Finset.Icc 1 N₂).product (oddSquarefreeRange M), f z * g z
      rw [Finset.sum_comm, Finset.product_eq_sprod, Finset.sum_product]
    _ ≤ Real.sqrt (∑ z ∈ S, f z ^ 2) * Real.sqrt (∑ z ∈ S, g z ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt S f g
    _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end Ostmann

end OAI
