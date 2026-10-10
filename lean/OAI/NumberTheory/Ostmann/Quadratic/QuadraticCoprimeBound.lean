import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimeEnergy
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorBound

namespace OAI

/-! # Bounding the coprime bilinear part by actual quadratic-sieve energy -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_coprime_pointwise (N : ℕ) (b : ℕ → ℂ) (m : ℤ) :
    ‖quadraticGcdKernelSum N 1 b m‖ ≤
      ∑ d ∈ Finset.Icc 1 N,
        ‖quadraticTransposeSum N (fun n => if d ∣ n then b n else 0) m‖ ^ 2 := by
  rw [quadratic_coprime_energy_expansion]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  have hd : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hd (sq_nonneg _)

 theorem quadratic_divisibility_total_energy (N : ℕ) (b : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 N, quadraticSieveEnergy N (fun n => if d ∣ n then b n else 0)) =
      ∑ n ∈ oddSquarefreeRange N, (n.divisors.card : ℝ) * ‖b n‖ ^ 2 := by
  unfold quadraticSieveEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hr, _, hs⟩ := Finset.mem_filter.mp hn
  have hf : (Finset.Icc 1 N).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hd⟩
      exact ⟨hd, hs.ne_zero⟩
    · rintro ⟨hd, _⟩
      have hdpos := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hd, hs.ne_zero⟩)
      exact ⟨⟨hdpos, (Nat.le_of_dvd (Finset.mem_Icc.mp hr).1 hd).trans
        (Finset.mem_Icc.mp hr).2⟩, hd⟩
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ← Finset.sum_filter]
  rw [hf]
  simp

 theorem quadratic_coprime_bilinear_bound {M N : ℕ} {K : ℝ}
    (h : QuadraticSieveBound M N K) (b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticGcdKernelSum N 1 b m‖) ≤
      2 * K * ∑ n ∈ oddSquarefreeRange N, (n.divisors.card : ℝ) * ‖b n‖ ^ 2 := by
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M, ∑ d ∈ Finset.Icc 1 N,
        ‖quadraticTransposeSum N (fun n => if d ∣ n then b n else 0) m‖ ^ 2 :=
      Finset.sum_le_sum (fun m _ => quadratic_coprime_pointwise N b m)
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N (fun n => if d ∣ n then b n else 0) m‖ ^ 2 :=
      Finset.sum_comm
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
        2 * K * quadraticSieveEnergy N (fun n => if d ∣ n then b n else 0) :=
      Finset.sum_le_sum (fun d _ => quadraticTranspose_of_bound h _)
    _ = _ := by rw [← Finset.mul_sum, quadratic_divisibility_total_energy]

 theorem quadratic_coprime_bilinear_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, ∀ K : ℝ, 0 ≤ K →
      QuadraticSieveBound M N K → ∀ b : ℕ → ℂ,
      (∑ m ∈ oddSquarefreeRange M, ‖quadraticGcdKernelSum N 1 b m‖) ≤
        C * K * (N : ℝ) ^ ε * quadraticSieveEnergy N b := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_bound ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro M N K hK h b
  have hweight : (∑ n ∈ oddSquarefreeRange N, (n.divisors.card : ℝ) * ‖b n‖ ^ 2) ≤
      C * (N : ℝ) ^ ε * quadraticSieveEnergy N b := by
    rw [quadraticSieveEnergy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hsf := (Finset.mem_filter.mp hn).2.2
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    have hd := (hc n hsf.ne_zero).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnN hε.le) hC.le)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hd (sq_nonneg ‖b n‖)
  have hh := (quadratic_coprime_bilinear_bound h b).trans
    (mul_le_mul_of_nonneg_left hweight (by positivity : 0 ≤ 2 * K))
  convert hh using 1
  ring

end Ostmann

end OAI
