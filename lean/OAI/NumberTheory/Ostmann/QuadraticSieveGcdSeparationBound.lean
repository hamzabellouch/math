import OAI.NumberTheory.Ostmann.Arithmetic.DivisorGrowth
import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationQuotient

namespace OAI

namespace Ostmann.QuadraticSieve

theorem divisorWeightedEnergy_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N d : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
      (∀ n ∈ S, 0 < n ∧ n ≤ N) →
      divisorWeightedEnergy S d a ≤ C * (N : ℝ) ^ ε *
        coefficientEnergy S (fun n => if d ∣ n then a n else 0) := by
  obtain ⟨C, hC, hdiv⟩ := Ostmann.Arithmetic.divisors_card_le_rpow ε hε
  refine ⟨C, hC, ?_⟩
  intro N d S a hS
  unfold divisorWeightedEnergy coefficientEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (hdiv n (hS n hn).1).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (hS n hn).2) hε.le) hC.le)

theorem sum_divisorWeightedEnergy_le_sq_divisors (D S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) :
    (∑ d ∈ D, divisorWeightedEnergy S d a) ≤
      ∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 * ‖a n‖ ^ 2 := by
  unfold divisorWeightedEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n hn
  have hc : (D.filter (fun d => d ∣ n)).card ≤ n.divisors.card := by
    apply Finset.card_le_card
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, (hS n hn).ne'⟩
  have he : (∑ d ∈ D, ‖if d ∣ n then a n else 0‖ ^ 2) =
      ((D.filter (fun d => d ∣ n)).card : ℝ) * ‖a n‖ ^ 2 := by
    calc
      _ = ∑ d ∈ D, if d ∣ n then ‖a n‖ ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        split <;> simp
      _ = ∑ d ∈ D.filter (fun d => d ∣ n), ‖a n‖ ^ 2 := (Finset.sum_filter _ _).symm
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, he, ← mul_assoc]
  calc
    _ ≤ (n.divisors.card : ℝ) * n.divisors.card * ‖a n‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (Nat.cast_nonneg _))
        (sq_nonneg _)
    _ = _ := by ring

theorem sum_divisorWeightedEnergy_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (D S : Finset ℕ) (a : ℕ → ℂ),
      (∀ n ∈ S, 0 < n ∧ n ≤ N) →
      (∑ d ∈ D, divisorWeightedEnergy S d a) ≤
        C * (N : ℝ) ^ ε * coefficientEnergy S a := by
  obtain ⟨C, hC, hdiv⟩ := Ostmann.Arithmetic.divisors_card_pow_le_rpow 2 ε hε
  refine ⟨C, hC, ?_⟩
  intro N D S a hS
  apply (sum_divisorWeightedEnergy_le_sq_divisors D S a (fun n hn => (hS n hn).1)).trans
  unfold coefficientEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (hdiv n (hS n hn).1).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (hS n hn).2) hε.le) hC.le)

noncomputable def coprimeDivisorJacobiRow (S T : Finset ℕ) (a b : ℕ → ℂ)
    (d₁ d₂ : ℕ) (m : ℤ) : ℂ :=
  ∑ n ∈ S, ∑ t ∈ T,
    if n.Coprime t ∧ d₁ ∣ n ∧ d₂ ∣ t then a n * b t * (jacobiSym m (n * t) : ℂ) else 0

theorem coprimeDivisorJacobiRow_eq (S T : Finset ℕ) (a b : ℕ → ℂ)
    (d₁ d₂ : ℕ) (hS : ∀ n ∈ S, 0 < n) (hT : ∀ t ∈ T, 0 < t) (m : ℤ) :
    coprimeDivisorJacobiRow S T a b d₁ d₂ m =
      ∑ n ∈ S, ∑ t ∈ T, if n.Coprime t then
        (if d₁ ∣ n then a n * (jacobiSym m n : ℂ) else 0) *
        (if d₂ ∣ t then b t * (jacobiSym m t : ℂ) else 0) else 0 := by
  unfold coprimeDivisorJacobiRow
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  rw [jacobiSym.mul_right' m (hS n hn).ne' (hT t ht).ne', Int.cast_mul]
  by_cases hnt : n.Coprime t <;> by_cases hdn : d₁ ∣ n <;> by_cases hdt : d₂ ∣ t <;>
    simp [hnt, hdn, hdt, mul_assoc, mul_left_comm, mul_comm]

theorem coprimeDivisorJacobiRow_norm_sq_le (V S T : Finset ℕ) (a b : ℕ → ℂ)
    (d₁ d₂ N : ℕ) [NeZero d₁] [NeZero d₂]
    (hV : ∀ v ∈ V, Odd v)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Odd n)
    (hT : ∀ t ∈ T, 0 < t ∧ t ≤ N ∧ Odd t) :
    (∑ v ∈ V, ‖coprimeDivisorJacobiRow S T a b d₁ d₂ (v : ℤ)‖) ^ 2 ≤
      (2 * quadraticNorm V (quotientSupport S d₁) * divisorWeightedEnergy S d₁ a) *
      (2 * quadraticNorm V (quotientSupport T d₂) * divisorWeightedEnergy T d₂ b) := by
  simp_rw [coprimeDivisorJacobiRow_eq S T a b d₁ d₂
    (fun n hn => (hS n hn).1) (fun t ht => (hT t ht).1)]
  have hcs := sum_coprime_bilinear_norm_sq_le V S T
    (fun v n => if d₁ ∣ n then a n * (jacobiSym (v : ℤ) n : ℂ) else 0)
    (fun v t => if d₂ ∣ t then b t * (jacobiSym (v : ℤ) t : ℂ) else 0)
    N (fun n hn => ⟨(hS n hn).1, (hS n hn).2.1⟩)
  apply hcs.trans
  apply mul_le_mul
  · simpa only [← ite_and, and_comm] using
      sum_divisor_jacobi_energy_le_quotient_norm V S a d₁ N hV hS
  · simpa only [← ite_and, and_comm] using
      sum_divisor_jacobi_energy_le_quotient_norm V T b d₂ N hV hT
  · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  · exact mul_nonneg (mul_nonneg (by norm_num) (quadraticNorm_nonneg _ _))
      (divisorWeightedEnergy_nonneg _ _ _)

end Ostmann.QuadraticSieve

end OAI
